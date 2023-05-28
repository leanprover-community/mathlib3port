/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.two_pointing
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sum.Basic
import Mathbin.Logic.Nontrivial

/-!
# Two-pointings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `two_pointing α`, the type of two pointings of `α`. A two-pointing is the data of
two distinct terms.

This is morally a Type-valued `nontrivial`. Another type which is quite close in essence is `sym2`.
Categorically speaking, `prod` is a cospan in the category of types. This forms the category of
bipointed types. Two-pointed types form a full subcategory of those.

## References

* [nLab, *Coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/


open Function

variable {α β : Type _}

#print TwoPointing /-
/-- Two-pointing of a type. This is a Type-valued termed `nontrivial`. -/
@[ext]
structure TwoPointing (α : Type _) extends α × α where
  fst_ne_snd : fst ≠ snd
  deriving DecidableEq
#align two_pointing TwoPointing
-/

namespace TwoPointing

variable (p : TwoPointing α) (q : TwoPointing β)

#print TwoPointing.snd_ne_fst /-
theorem snd_ne_fst : p.snd ≠ p.fst :=
  p.fst_ne_snd.symm
#align two_pointing.snd_ne_fst TwoPointing.snd_ne_fst
-/

#print TwoPointing.swap /-
/-- Swaps the two pointed elements. -/
@[simps]
def swap : TwoPointing α :=
  ⟨(p.snd, p.fst), p.snd_ne_fst⟩
#align two_pointing.swap TwoPointing.swap
-/

#print TwoPointing.swap_fst /-
theorem swap_fst : p.symm.fst = p.snd :=
  rfl
#align two_pointing.swap_fst TwoPointing.swap_fst
-/

#print TwoPointing.swap_snd /-
theorem swap_snd : p.symm.snd = p.fst :=
  rfl
#align two_pointing.swap_snd TwoPointing.swap_snd
-/

#print TwoPointing.swap_swap /-
@[simp]
theorem swap_swap : p.symm.symm = p := by ext <;> rfl
#align two_pointing.swap_swap TwoPointing.swap_swap
-/

#print TwoPointing.to_nontrivial /-
-- See note [reducible non instances]
@[reducible]
theorem to_nontrivial : Nontrivial α :=
  ⟨⟨p.fst, p.snd, p.fst_ne_snd⟩⟩
#align two_pointing.to_nontrivial TwoPointing.to_nontrivial
-/

instance [Nontrivial α] : Nonempty (TwoPointing α) :=
  let ⟨a, b, h⟩ := exists_pair_ne α
  ⟨⟨(a, b), h⟩⟩

#print TwoPointing.nonempty_two_pointing_iff /-
@[simp]
theorem nonempty_two_pointing_iff : Nonempty (TwoPointing α) ↔ Nontrivial α :=
  ⟨fun ⟨p⟩ => p.to_nontrivial, @TwoPointing.nonempty _⟩
#align two_pointing.nonempty_two_pointing_iff TwoPointing.nonempty_two_pointing_iff
-/

section Pi

variable (α) [Nonempty α]

#print TwoPointing.pi /-
/-- The two-pointing of constant functions. -/
def pi : TwoPointing (α → β) where
  fst _ := q.fst
  snd _ := q.snd
  fst_ne_snd h := q.fst_ne_snd <| by convert congr_fun h (Classical.arbitrary α)
#align two_pointing.pi TwoPointing.pi
-/

@[simp]
theorem pi_fst : (q.pi α).fst = const α q.fst :=
  rfl
#align two_pointing.pi_fst TwoPointing.pi_fst

@[simp]
theorem pi_snd : (q.pi α).snd = const α q.snd :=
  rfl
#align two_pointing.pi_snd TwoPointing.pi_snd

end Pi

#print TwoPointing.prod /-
/-- The product of two two-pointings. -/
def prod : TwoPointing (α × β) where
  fst := (p.fst, q.fst)
  snd := (p.snd, q.snd)
  fst_ne_snd h := p.fst_ne_snd (congr_arg Prod.fst h)
#align two_pointing.prod TwoPointing.prod
-/

@[simp]
theorem prod_fst : (p.Prod q).fst = (p.fst, q.fst) :=
  rfl
#align two_pointing.prod_fst TwoPointing.prod_fst

@[simp]
theorem prod_snd : (p.Prod q).snd = (p.snd, q.snd) :=
  rfl
#align two_pointing.prod_snd TwoPointing.prod_snd

#print TwoPointing.sum /-
/-- The sum of two pointings. Keeps the first point from the left and the second point from the
right. -/
protected def sum : TwoPointing (Sum α β) :=
  ⟨(Sum.inl p.fst, Sum.inr q.snd), Sum.inl_ne_inr⟩
#align two_pointing.sum TwoPointing.sum
-/

@[simp]
theorem sum_fst : (p.Sum q).fst = Sum.inl p.fst :=
  rfl
#align two_pointing.sum_fst TwoPointing.sum_fst

@[simp]
theorem sum_snd : (p.Sum q).snd = Sum.inr q.snd :=
  rfl
#align two_pointing.sum_snd TwoPointing.sum_snd

#print TwoPointing.bool /-
/-- The `ff`, `tt` two-pointing of `bool`. -/
protected def bool : TwoPointing Bool :=
  ⟨(false, true), Bool.false_ne_true⟩
#align two_pointing.bool TwoPointing.bool
-/

#print TwoPointing.bool_fst /-
@[simp]
theorem bool_fst : TwoPointing.bool.fst = false :=
  rfl
#align two_pointing.bool_fst TwoPointing.bool_fst
-/

#print TwoPointing.bool_snd /-
@[simp]
theorem bool_snd : TwoPointing.bool.snd = true :=
  rfl
#align two_pointing.bool_snd TwoPointing.bool_snd
-/

instance : Inhabited (TwoPointing Bool) :=
  ⟨TwoPointing.bool⟩

#print TwoPointing.prop /-
/-- The `false`, `true` two-pointing of `Prop`. -/
protected def prop : TwoPointing Prop :=
  ⟨(False, True), false_ne_true⟩
#align two_pointing.Prop TwoPointing.prop
-/

#print TwoPointing.prop_fst /-
@[simp]
theorem prop_fst : TwoPointing.prop.fst = False :=
  rfl
#align two_pointing.Prop_fst TwoPointing.prop_fst
-/

#print TwoPointing.prop_snd /-
@[simp]
theorem prop_snd : TwoPointing.prop.snd = True :=
  rfl
#align two_pointing.Prop_snd TwoPointing.prop_snd
-/

end TwoPointing

