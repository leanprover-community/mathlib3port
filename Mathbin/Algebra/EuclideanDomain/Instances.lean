/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro

! This file was ported from Lean 3 source module algebra.euclidean_domain.instances
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.EuclideanDomain.Defs
import Mathbin.Algebra.Field.Defs
import Mathbin.Algebra.GroupWithZero.Units.Lemmas
import Mathbin.Data.Nat.Order.Basic
import Mathbin.Data.Int.Order.Basic

/-!
# Instances for Euclidean domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `int.euclidean_domain`: shows that `ℤ` is a Euclidean domain.
* `field.to_euclidean_domain`: shows that any field is a Euclidean domain.

-/


#print Int.euclideanDomain /-
instance Int.euclideanDomain : EuclideanDomain ℤ :=
  { Int.commRing, Int.nontrivial with
    add := (· + ·)
    mul := (· * ·)
    one := 1
    zero := 0
    neg := Neg.neg
    Quotient := (· / ·)
    quotient_zero := Int.div_zero
    remainder := (· % ·)
    quotient_mul_add_remainder_eq := fun a b => Int.div_add_mod _ _
    R := fun a b => a.natAbs < b.natAbs
    r_well_founded := measure_wf fun a => Int.natAbs a
    remainder_lt := fun a b b0 =>
      Int.ofNat_lt.1 <|
        by
        rw [Int.natAbs_of_nonneg (Int.emod_nonneg _ b0), Int.coe_natAbs]
        exact Int.emod_lt _ b0
    mul_left_not_lt := fun a b b0 =>
      not_lt_of_ge <| by
        rw [← mul_one a.nat_abs, Int.natAbs_mul]
        exact mul_le_mul_of_nonneg_left (Int.natAbs_pos_of_ne_zero b0) (Nat.zero_le _) }
#align int.euclidean_domain Int.euclideanDomain
-/

#print Field.toEuclideanDomain /-
-- see Note [lower instance priority]
instance (priority := 100) Field.toEuclideanDomain {K : Type _} [Field K] : EuclideanDomain K :=
  { ‹Field K› with
    add := (· + ·)
    mul := (· * ·)
    one := 1
    zero := 0
    neg := Neg.neg
    Quotient := (· / ·)
    remainder := fun a b => a - a * b / b
    quotient_zero := div_zero
    quotient_mul_add_remainder_eq := fun a b => by
      classical by_cases b = 0 <;> simp [h, mul_div_cancel']
    R := fun a b => a = 0 ∧ b ≠ 0
    r_well_founded :=
      WellFounded.intro fun a =>
        (Acc.intro _) fun b ⟨hb, hna⟩ => (Acc.intro _) fun c ⟨hc, hnb⟩ => False.elim <| hnb hb
    remainder_lt := fun a b hnb => by simp [hnb]
    mul_left_not_lt := fun a b hnb ⟨hab, hna⟩ => Or.cases_on (mul_eq_zero.1 hab) hna hnb }
#align field.to_euclidean_domain Field.toEuclideanDomain
-/

