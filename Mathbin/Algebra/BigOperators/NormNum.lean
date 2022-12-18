/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module algebra.big_operators.norm_num
! leanprover-community/mathlib commit c5c7e2760814660967bc27f0de95d190a22297f3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Int.Interval
import Mathbin.Tactic.NormNum

/-! ### `norm_num` plugin for big operators

This `norm_num` plugin provides support for computing sums and products of
lists, multisets and finsets.

Example goals this plugin can solve:

 * `∑ i in finset.range 10, (i^2 : ℕ) = 285`
 * `Π i in {1, 4, 9, 16}, nat.sqrt i = 24`
 * `([1, 2, 1, 3]).sum = 7`

## Implementation notes

The tactic works by first converting the expression denoting the collection
(list, multiset, finset) to a list of expressions denoting each element. For
finsets, this involves erasing duplicate elements (the tactic fails if equality
or disequality cannot be determined).

After rewriting the big operator to a product/sum of lists, we evaluate this
using `norm_num` itself to handle multiplication/addition.

Finally, we package up the result using some congruence lemmas.

-/


open Tactic

namespace Tactic.NormNum

/-- Use `norm_num` to decide equality between two expressions.

If the decision procedure succeeds, the `bool` value indicates whether the expressions are equal,
and the `expr` is a proof of (dis)equality.
This procedure is partial: it will fail in cases where `norm_num` can't reduce either side
to a rational numeral.
-/
unsafe def decide_eq (l r : expr) : tactic (Bool × expr) := do
  let (l', l'_pf) ← or_refl_conv norm_num.derive l
  let (r', r'_pf) ← or_refl_conv norm_num.derive r
  let n₁ ← l'.to_rat
  let n₂ ← r'.to_rat
  let c ← infer_type l' >>= mk_instance_cache
  if n₁ = n₂ then do
      let pf ← i_to_expr ``(Eq.trans $(l'_pf) <| Eq.symm $(r'_pf))
      pure (tt, pf)
    else do
      let (_, p) ← norm_num.prove_ne c l' r' n₁ n₂
      pure (ff, p)
#align tactic.norm_num.decide_eq tactic.norm_num.decide_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem List.not_mem_cons {α : Type _} {x y : α} {ys : List α} (h₁ : x ≠ y) (h₂ : x ∉ ys) :
    x ∉ y::ys := fun h => ((List.mem_cons_iff _ _ _).mp h).elim h₁ h₂
#align tactic.norm_num.list.not_mem_cons Tactic.NormNum.List.not_mem_cons

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Use a decision procedure for the equality of list elements to decide list membership.

If the decision procedure succeeds, the `bool` value indicates whether the expressions are equal,
and the `expr` is a proof of (dis)equality.
This procedure is partial iff its parameter `decide_eq` is partial.
-/
unsafe def list.decide_mem (decide_eq : expr → expr → tactic (Bool × expr)) :
    expr → List expr → tactic (Bool × expr)
  | x, [] => do
    let pf ← i_to_expr ``(List.not_mem_nil $(x))
    pure (ff, pf)
  | x, y::ys => do
    let (is_head, head_pf) ← decide_eq x y
    if is_head then do
        let pf ← i_to_expr ``((List.mem_cons_iff $(x) $(y) _).mpr (Or.inl $(head_pf)))
        pure (tt, pf)
      else do
        let (mem_tail, tail_pf) ← list.decide_mem x ys
        if mem_tail then do
            let pf ← i_to_expr ``((List.mem_cons_iff $(x) $(y) _).mpr (Or.inr $(tail_pf)))
            pure (tt, pf)
          else do
            let pf ← i_to_expr ``(List.not_mem_cons $(head_pf) $(tail_pf))
            pure (ff, pf)
#align tactic.norm_num.list.decide_mem tactic.norm_num.list.decide_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem List.map_cons_congr {α β : Type _} (f : α → β) {x : α} {xs : List α} {fx : β} {fxs : List β}
    (h₁ : f x = fx) (h₂ : xs.map f = fxs) : (x::xs).map f = fx::fxs := by rw [List.map_cons, h₁, h₂]
#align tactic.norm_num.list.map_cons_congr Tactic.NormNum.List.map_cons_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Apply `ef : α → β` to all elements of the list, constructing an equality proof. -/
unsafe def eval_list_map (ef : expr) : List expr → tactic (List expr × expr)
  | [] => do
    let eq ← i_to_expr ``(List.map_nil $(ef))
    pure ([], Eq)
  | x::xs => do
    let (fx, fx_eq) ← or_refl_conv norm_num.derive (expr.app ef x)
    let (fxs, fxs_eq) ← eval_list_map xs
    let eq ← i_to_expr ``(List.map_cons_congr $(ef) $(fx_eq) $(fxs_eq))
    pure (fx::fxs, Eq)
#align tactic.norm_num.eval_list_map tactic.norm_num.eval_list_map

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem List.cons_congr {α : Type _} (x : α) {xs : List α} {xs' : List α} (xs_eq : xs' = xs) :
    (x::xs') = x::xs := by rw [xs_eq]
#align tactic.norm_num.list.cons_congr Tactic.NormNum.List.cons_congr

theorem List.map_congr {α β : Type _} (f : α → β) {xs xs' : List α} {ys : List β} (xs_eq : xs = xs')
    (ys_eq : xs'.map f = ys) : xs.map f = ys := by rw [← ys_eq, xs_eq]
#align tactic.norm_num.list.map_congr Tactic.NormNum.List.map_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Convert an expression denoting a list to a list of elements. -/
unsafe def eval_list : expr → tactic (List expr × expr)
  | e@q(List.nil) => do
    let eq ← mk_eq_refl e
    pure ([], Eq)
  | e@q(List.cons $(x) $(xs)) => do
    let (xs, xs_eq) ← eval_list xs
    let eq ← i_to_expr ``(List.cons_congr $(x) $(xs_eq))
    pure (x::xs, Eq)
  | e@q(List.range $(en)) => do
    let n ← expr.to_nat en
    let eis ← (List.range n).mmap fun i => expr.of_nat q(ℕ) i
    let eq ← mk_eq_refl e
    pure (eis, Eq)
  | q(@List.map $(α) $(β) $(ef) $(exs)) => do
    let (xs, xs_eq) ← eval_list exs
    let (ys, ys_eq) ← eval_list_map ef xs
    let eq ← i_to_expr ``(List.map_congr $(ef) $(xs_eq) $(ys_eq))
    pure (ys, Eq)
  | e@q(@List.finRange $(en)) => do
    let n ← expr.to_nat en
    let eis ← (List.finRange n).mmap fun i => expr.of_nat q(Fin $(en)) i
    let eq ← mk_eq_refl e
    pure (eis, Eq)
  | e => fail (to_fmt "Unknown list expression" ++ format.line ++ to_fmt e)
#align tactic.norm_num.eval_list tactic.norm_num.eval_list

theorem Multiset.cons_congr {α : Type _} (x : α) {xs : Multiset α} {xs' : List α}
    (xs_eq : (xs' : Multiset α) = xs) : (List.cons x xs' : Multiset α) = x ::ₘ xs := by
  rw [← xs_eq] <;> rfl
#align tactic.norm_num.multiset.cons_congr Tactic.NormNum.Multiset.cons_congr

theorem Multiset.map_congr {α β : Type _} (f : α → β) {xs : Multiset α} {xs' : List α} {ys : List β}
    (xs_eq : xs = (xs' : Multiset α)) (ys_eq : xs'.map f = ys) : xs.map f = (ys : Multiset β) := by
  rw [← ys_eq, ← Multiset.coe_map, xs_eq]
#align tactic.norm_num.multiset.map_congr Tactic.NormNum.Multiset.map_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Convert an expression denoting a multiset to a list of elements.

We return a list rather than a finset, so we can more easily iterate over it
(without having to prove that our tactics are independent of the order of iteration,
which is in general not true).
-/
unsafe def eval_multiset : expr → tactic (List expr × expr)
  | e@q(@Zero.zero (Multiset _) _) => do
    let eq ← mk_eq_refl e
    pure ([], Eq)
  | e@q(EmptyCollection.emptyCollection) => do
    let eq ← mk_eq_refl e
    pure ([], Eq)
  | e@q(Singleton.singleton $(x)) => do
    let eq ← mk_eq_refl e
    pure ([x], Eq)
  | e@q(Multiset.cons $(x) $(xs)) => do
    let (xs, xs_eq) ← eval_multiset xs
    let eq ← i_to_expr ``(Multiset.cons_congr $(x) $(xs_eq))
    pure (x::xs, Eq)
  | e@q(@Insert.insert Multiset.hasInsert $(x) $(xs)) => do
    let (xs, xs_eq) ← eval_multiset xs
    let eq ← i_to_expr ``(Multiset.cons_congr $(x) $(xs_eq))
    pure (x::xs, Eq)
  | e@q(Multiset.range $(en)) => do
    let n ← expr.to_nat en
    let eis ← (List.range n).mmap fun i => expr.of_nat q(ℕ) i
    let eq ← mk_eq_refl e
    pure (eis, Eq)
  | q(@coe (@coeToLift (@coeBase Multiset.hasCoe)) $(exs)) => do
    let (xs, xs_eq) ← eval_list exs
    let eq ← i_to_expr ``(congr_arg coe $(xs_eq))
    pure (xs, Eq)
  | q(@Multiset.map $(α) $(β) $(ef) $(exs)) => do
    let (xs, xs_eq) ← eval_multiset exs
    let (ys, ys_eq) ← eval_list_map ef xs
    let eq ← i_to_expr ``(Multiset.map_congr $(ef) $(xs_eq) $(ys_eq))
    pure (ys, Eq)
  | e => fail (to_fmt "Unknown multiset expression" ++ format.line ++ to_fmt e)
#align tactic.norm_num.eval_multiset tactic.norm_num.eval_multiset

theorem Finset.mk_congr {α : Type _} {xs xs' : Multiset α} (h : xs = xs') (nd nd') :
    Finset.mk xs nd = Finset.mk xs' nd' := by congr <;> assumption
#align tactic.norm_num.finset.mk_congr Tactic.NormNum.Finset.mk_congr

theorem Finset.insert_eq_coe_list_of_mem {α : Type _} [DecidableEq α] (x : α) (xs : Finset α)
    {xs' : List α} (h : x ∈ xs') (nd_xs : xs'.Nodup)
    (hxs' : xs = Finset.mk (↑xs') (Multiset.coe_nodup.mpr nd_xs)) :
    insert x xs = Finset.mk (↑xs') (Multiset.coe_nodup.mpr nd_xs) := by
  have h : x ∈ xs := by simpa [hxs'] using h
  rw [Finset.insert_eq_of_mem h, hxs']
#align
  tactic.norm_num.finset.insert_eq_coe_list_of_mem Tactic.NormNum.Finset.insert_eq_coe_list_of_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Finset.insert_eq_coe_list_cons {α : Type _} [DecidableEq α] (x : α) (xs : Finset α)
    {xs' : List α} (h : x ∉ xs') (nd_xs : xs'.Nodup) (nd_xxs : (x::xs').Nodup)
    (hxs' : xs = Finset.mk (↑xs') (Multiset.coe_nodup.mpr nd_xs)) :
    insert x xs = Finset.mk (↑(x::xs')) (Multiset.coe_nodup.mpr nd_xxs) := by
  have h : x ∉ xs := by simpa [hxs'] using h
  rw [← Finset.val_inj, Finset.insert_val_of_not_mem h, hxs']
  simp only [Multiset.cons_coe]
#align tactic.norm_num.finset.insert_eq_coe_list_cons Tactic.NormNum.Finset.insert_eq_coe_list_cons

/-- For now this only works on types that are contiguous subsets of the integers -/
unsafe def eval_finset_interval : expr → tactic (Option (List expr × expr × expr))
  | e@q(@Finset.icc $(α) $(inst_1) $(inst_2) $(ea) $(eb)) => do
    let a ← expr.to_int ea
    let b ← expr.to_int eb
    let eis ← (Finset.icc a b).val.unquot.mmap fun i => expr.of_int α i
    let eq ← mk_eq_refl e
    let nd ← i_to_expr ``(Finset.nodup $(e))
    pure (eis, Eq, nd)
  | e@q(@Finset.ico $(α) $(inst_1) $(inst_2) $(ea) $(eb)) => do
    let a ← expr.to_int ea
    let b ← expr.to_int eb
    let eis ← (Finset.ico a b).val.unquot.mmap fun i => expr.of_int α i
    let eq ← mk_eq_refl e
    let nd ← i_to_expr ``(Finset.nodup $(e))
    pure (eis, Eq, nd)
  | e@q(@Finset.ioc $(α) $(inst_1) $(inst_2) $(ea) $(eb)) => do
    let a ← expr.to_int ea
    let b ← expr.to_int eb
    let eis ← (Finset.ioc a b).val.unquot.mmap fun i => expr.of_int α i
    let eq ← mk_eq_refl e
    let nd ← i_to_expr ``(Finset.nodup $(e))
    pure (eis, Eq, nd)
  | e@q(@Finset.ioo $(α) $(inst_1) $(inst_2) $(ea) $(eb)) => do
    let a ← expr.to_int ea
    let b ← expr.to_int eb
    let eis ← (Finset.ioo a b).val.unquot.mmap fun i => expr.of_int α i
    let eq ← mk_eq_refl e
    let nd ← i_to_expr ``(Finset.nodup $(e))
    pure (eis, Eq, nd)
  | _ => pure none
#align tactic.norm_num.eval_finset_interval tactic.norm_num.eval_finset_interval

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Convert an expression denoting a finset to a list of elements,
a proof that this list is equal to the original finset,
and a proof that the list contains no duplicates.

We return a list rather than a finset, so we can more easily iterate over it
(without having to prove that our tactics are independent of the order of iteration,
which is in general not true).

`decide_eq` is a (partial) decision procedure for determining whether two
elements of the finset are equal, for example to parse `{2, 1, 2}` into `[2, 1]`.
-/
unsafe def eval_finset (decide_eq : expr → expr → tactic (Bool × expr)) :
    expr → tactic (List expr × expr × expr)
  | e@q(Finset.mk $(val) $(nd)) => do
    let (val', Eq) ← eval_multiset val
    let eq' ← i_to_expr ``(Finset.mk_congr $(Eq) _ _)
    pure (val', eq', nd)
  | e@q(EmptyCollection.emptyCollection) => do
    let eq ← mk_eq_refl e
    let nd ← i_to_expr ``(List.nodup_nil)
    pure ([], Eq, nd)
  | e@q(Singleton.singleton $(x)) => do
    let eq ← mk_eq_refl e
    let nd ← i_to_expr ``(List.nodup_singleton $(x))
    pure ([x], Eq, nd)
  | q(@Insert.insert (@Finset.hasInsert $(dec)) $(x) $(xs)) => do
    let (exs, xs_eq, xs_nd) ← eval_finset xs
    let (is_mem, mem_pf) ← list.decide_mem decide_eq x exs
    if is_mem then do
        let pf ←
          i_to_expr ``(Finset.insert_eq_coe_list_of_mem $(x) $(xs) $(mem_pf) $(xs_nd) $(xs_eq))
        pure (exs, pf, xs_nd)
      else do
        let nd ← i_to_expr ``(List.nodup_cons.mpr ⟨$(mem_pf), $(xs_nd)⟩)
        let pf ←
          i_to_expr ``(Finset.insert_eq_coe_list_cons $(x) $(xs) $(mem_pf) $(xs_nd) $(nd) $(xs_eq))
        pure (x::exs, pf, nd)
  | q(@Finset.univ $(ft)) => do
    let-- Convert the fintype instance expression `ft` to a list of its elements.
      -- Unfold it to the `fintype.mk` constructor and a list of arguments.
      `fintype.mk
      ← get_app_fn_const_whnf ft |
      fail (to_fmt "Unknown fintype expression" ++ format.line ++ to_fmt ft)
    let [_, args, _] ← get_app_args_whnf ft |
      fail (to_fmt "Expected 3 arguments to `fintype.mk`")
    eval_finset args
  | e@q(Finset.range $(en)) => do
    let n ← expr.to_nat en
    let eis ← (List.range n).mmap fun i => expr.of_nat q(ℕ) i
    let eq ← mk_eq_refl e
    let nd ← i_to_expr ``(List.nodup_range $(en))
    pure (eis, Eq, nd)
  | e => do
    let-- try some other parsers
        some
        v
      ← eval_finset_interval e |
      fail (to_fmt "Unknown finset expression" ++ format.line ++ to_fmt e)
    pure v
#align tactic.norm_num.eval_finset tactic.norm_num.eval_finset

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem List.prod_cons_congr {α : Type _} [Monoid α] (xs : List α) (x y z : α) (his : xs.Prod = y)
    (hi : x * y = z) : (x::xs).Prod = z := by rw [List.prod_cons, his, hi]
#align tactic.norm_num.list.prod_cons_congr Tactic.NormNum.List.prod_cons_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Evaluate `list.prod %%xs`,
      producing the evaluated expression and an equality proof. -/
    unsafe
  def
    list.prove_prod
    ( α : expr ) : List expr → tactic ( expr × expr )
    |
        [ ]
        =>
        do
          let result ← expr.of_nat α 1
            let proof ← i_to_expr ` `( @ List.prod_nil $ ( α ) _ )
            pure ( result , proof )
      |
        x :: xs
        =>
        do
          let eval_xs ← list.prove_prod xs
            let xxs ← i_to_expr ` `( $ ( x ) * $ ( eval_xs . 1 ) )
            let eval_xxs ← or_refl_conv norm_num.derive xxs
            let exs ← expr.of_list α xs
            let
              proof
                ←
                i_to_expr
                  `
                    `(
                      List.prod_cons_congr
                        $ ( exs )
                          $ ( x )
                          $ ( eval_xs . 1 )
                          $ ( eval_xxs . 1 )
                          $ ( eval_xs . 2 )
                          $ ( eval_xxs . 2 )
                      )
            pure ( eval_xxs . 1 , proof )
#align tactic.norm_num.list.prove_prod tactic.norm_num.list.prove_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Evaluate `list.sum %%xs`,
      sumucing the evaluated expression and an equality proof. -/
    unsafe
  def
    list.prove_sum
    ( α : expr ) : List expr → tactic ( expr × expr )
    |
        [ ]
        =>
        do
          let result ← expr.of_nat α 0
            let proof ← i_to_expr ` `( @ List.sum_nil $ ( α ) _ )
            pure ( result , proof )
      |
        x :: xs
        =>
        do
          let eval_xs ← list.prove_sum xs
            let xxs ← i_to_expr ` `( $ ( x ) + $ ( eval_xs . 1 ) )
            let eval_xxs ← or_refl_conv norm_num.derive xxs
            let exs ← expr.of_list α xs
            let
              proof
                ←
                i_to_expr
                  `
                    `(
                      List.sum_cons_congr
                        $ ( exs )
                          $ ( x )
                          $ ( eval_xs . 1 )
                          $ ( eval_xxs . 1 )
                          $ ( eval_xs . 2 )
                          $ ( eval_xxs . 2 )
                      )
            pure ( eval_xxs . 1 , proof )
#align tactic.norm_num.list.prove_sum tactic.norm_num.list.prove_sum

@[to_additive]
theorem List.prod_congr {α : Type _} [Monoid α] {xs xs' : List α} {z : α} (h₁ : xs = xs')
    (h₂ : xs'.Prod = z) : xs.Prod = z := by cc
#align tactic.norm_num.list.prod_congr Tactic.NormNum.List.prod_congr

@[to_additive]
theorem Multiset.prod_congr {α : Type _} [CommMonoid α] {xs : Multiset α} {xs' : List α} {z : α}
    (h₁ : xs = (xs' : Multiset α)) (h₂ : xs'.Prod = z) : xs.Prod = z := by
  rw [← h₂, ← Multiset.coe_prod, h₁]
#align tactic.norm_num.multiset.prod_congr Tactic.NormNum.Multiset.prod_congr

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).prod`,
producing the evaluated expression and an equality proof. -/
unsafe def list.prove_prod_map (β ef : expr) (xs : List expr) : tactic (expr × expr) := do
  let (fxs, fxs_eq) ← eval_list_map ef xs
  let (Prod, prod_eq) ← list.prove_prod β fxs
  let eq ← i_to_expr ``(List.prod_congr $(fxs_eq) $(prod_eq))
  pure (Prod, Eq)
#align tactic.norm_num.list.prove_prod_map tactic.norm_num.list.prove_prod_map

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).sum`,
producing the evaluated expression and an equality proof. -/
unsafe def list.prove_sum_map (β ef : expr) (xs : List expr) : tactic (expr × expr) := do
  let (fxs, fxs_eq) ← eval_list_map ef xs
  let (Sum, sum_eq) ← list.prove_sum β fxs
  let eq ← i_to_expr ``(List.sum_congr $(fxs_eq) $(sum_eq))
  pure (Sum, Eq)
#align tactic.norm_num.list.prove_sum_map tactic.norm_num.list.prove_sum_map

@[to_additive]
theorem Finset.eval_prod_of_list {β α : Type _} [CommMonoid β] (s : Finset α) (f : α → β)
    {is : List α} (his : is.Nodup) (hs : Finset.mk (↑is) (Multiset.coe_nodup.mpr his) = s) {x : β}
    (hx : (is.map f).Prod = x) : s.Prod f = x := by
  rw [← hs, Finset.prod_mk, Multiset.coe_map, Multiset.coe_prod, hx]
#align tactic.norm_num.finset.eval_prod_of_list Tactic.NormNum.Finset.eval_prod_of_list

/-- `norm_num` plugin for evaluating big operators:
 * `list.prod`
 * `list.sum`
 * `multiset.prod`
 * `multiset.sum`
 * `finset.prod`
 * `finset.sum`
-/
@[norm_num]
unsafe def eval_big_operators : expr → tactic (expr × expr)
  | q(@List.prod $(α) $(inst1) $(inst2) $(exs)) =>
    (tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:") do
      let (xs, list_eq) ← eval_list exs
      let (result, sum_eq) ← list.prove_prod α xs
      let pf ← i_to_expr ``(List.prod_congr $(list_eq) $(sum_eq))
      pure (result, pf)
  | q(@List.sum $(α) $(inst1) $(inst2) $(exs)) =>
    (tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:") do
      let (xs, list_eq) ← eval_list exs
      let (result, sum_eq) ← list.prove_sum α xs
      let pf ← i_to_expr ``(List.sum_congr $(list_eq) $(sum_eq))
      pure (result, pf)
  | q(@Multiset.prod $(α) $(inst) $(exs)) =>
    (tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:") do
      let (xs, list_eq) ← eval_multiset exs
      let (result, sum_eq) ← list.prove_prod α xs
      let pf ← i_to_expr ``(Multiset.prod_congr $(list_eq) $(sum_eq))
      pure (result, pf)
  | q(@Multiset.sum $(α) $(inst) $(exs)) =>
    (tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:") do
      let (xs, list_eq) ← eval_multiset exs
      let (result, sum_eq) ← list.prove_sum α xs
      let pf ← i_to_expr ``(Multiset.sum_congr $(list_eq) $(sum_eq))
      pure (result, pf)
  | q(@Finset.prod $(β) $(α) $(inst) $(es) $(ef)) =>
    (tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:") do
      let (xs, list_eq, nodup) ← eval_finset decide_eq es
      let (result, sum_eq) ← list.prove_prod_map β ef xs
      let pf ← i_to_expr ``(Finset.eval_prod_of_list $(es) $(ef) $(nodup) $(list_eq) $(sum_eq))
      pure (result, pf)
  | q(@Finset.sum $(β) $(α) $(inst) $(es) $(ef)) =>
    (tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:") do
      let (xs, list_eq, nodup) ← eval_finset decide_eq es
      let (result, sum_eq) ← list.prove_sum_map β ef xs
      let pf ← i_to_expr ``(Finset.eval_sum_of_list $(es) $(ef) $(nodup) $(list_eq) $(sum_eq))
      pure (result, pf)
  | _ => failed
#align tactic.norm_num.eval_big_operators tactic.norm_num.eval_big_operators

end Tactic.NormNum

