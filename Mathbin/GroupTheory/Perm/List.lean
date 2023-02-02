/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module group_theory.perm.list
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Rotate
import Mathbin.GroupTheory.Perm.Support

/-!
# Permutations from a list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.

When there are duplicate elements in `l`, how and in what arrangement with respect to the other
elements they appear in the list determines the formed permutation.
This is because `list.form_perm` is implemented as a product of `equiv.swap`s.
That means that presence of a sublist of two adjacent duplicates like `[..., x, x, ...]`
will produce the same permutation as if the adjacent duplicates were not present.

The `list.form_perm` definition is meant to primarily be used with `nodup l`, so that
the resulting permutation is cyclic (if `l` has at least two elements).
The presence of duplicates in a particular placement can lead `list.form_perm` to produce a
nontrivial permutation that is noncyclic.
-/


namespace List

variable {α β : Type _}

section FormPerm

variable [DecidableEq α] (l : List α)

open Equiv Equiv.Perm

#print List.formPerm /-
/-- A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.
-/
def formPerm : Equiv.Perm α :=
  (zipWith Equiv.swap l l.tail).Prod
#align list.form_perm List.formPerm
-/

/- warning: list.form_perm_nil -> List.formPerm_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.nil.{u1} α)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.nil.{u1} α)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align list.form_perm_nil List.formPerm_nilₓ'. -/
@[simp]
theorem formPerm_nil : formPerm ([] : List α) = 1 :=
  rfl
#align list.form_perm_nil List.formPerm_nil

/- warning: list.form_perm_singleton -> List.formPerm_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (x : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α x (List.nil.{u1} α))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (x : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α x (List.nil.{u1} α))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align list.form_perm_singleton List.formPerm_singletonₓ'. -/
@[simp]
theorem formPerm_singleton (x : α) : formPerm [x] = 1 :=
  rfl
#align list.form_perm_singleton List.formPerm_singleton

/- warning: list.form_perm_cons_cons -> List.formPerm_cons_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (x : α) (y : α) (l : List.{u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α x (List.cons.{u1} α y l))) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α y l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (x : α) (y : α) (l : List.{u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α x (List.cons.{u1} α y l))) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α y l)))
Case conversion may be inaccurate. Consider using '#align list.form_perm_cons_cons List.formPerm_cons_consₓ'. -/
@[simp]
theorem formPerm_cons_cons (x y : α) (l : List α) :
    formPerm (x :: y :: l) = swap x y * formPerm (y :: l) :=
  prod_cons
#align list.form_perm_cons_cons List.formPerm_cons_cons

#print List.formPerm_pair /-
theorem formPerm_pair (x y : α) : formPerm [x, y] = swap x y :=
  rfl
#align list.form_perm_pair List.formPerm_pair
-/

variable {l} {x : α}

#print List.formPerm_apply_of_not_mem /-
theorem formPerm_apply_of_not_mem (x : α) (l : List α) (h : x ∉ l) : formPerm l x = x :=
  by
  cases' l with y l
  · simp
  induction' l with z l IH generalizing x y
  · simp
  · specialize IH x z (mt (mem_cons_of_mem y) h)
    simp only [not_or, mem_cons_iff] at h
    simp [IH, swap_apply_of_ne_of_ne, h]
#align list.form_perm_apply_of_not_mem List.formPerm_apply_of_not_mem
-/

#print List.mem_of_formPerm_apply_ne /-
theorem mem_of_formPerm_apply_ne (x : α) (l : List α) : l.formPerm x ≠ x → x ∈ l :=
  not_imp_comm.2 <| List.formPerm_apply_of_not_mem _ _
#align list.mem_of_form_perm_apply_ne List.mem_of_formPerm_apply_ne
-/

#print List.formPerm_apply_mem_of_mem /-
theorem formPerm_apply_mem_of_mem (x : α) (l : List α) (h : x ∈ l) : formPerm l x ∈ l :=
  by
  cases' l with y l
  · simpa
  induction' l with z l IH generalizing x y
  · simpa using h
  · by_cases hx : x ∈ z :: l
    · rw [form_perm_cons_cons, mul_apply, swap_apply_def]
      split_ifs <;> simp [IH _ _ hx]
    · replace h : x = y := Or.resolve_right h hx
      simp [form_perm_apply_of_not_mem _ _ hx, ← h]
#align list.form_perm_apply_mem_of_mem List.formPerm_apply_mem_of_mem
-/

#print List.mem_of_formPerm_apply_mem /-
theorem mem_of_formPerm_apply_mem (x : α) (l : List α) (h : l.formPerm x ∈ l) : x ∈ l :=
  by
  cases' l with y l
  · simpa
  induction' l with z l IH generalizing x y
  · simpa using h
  · by_cases hx : (z :: l).formPerm x ∈ z :: l
    · rw [List.formPerm_cons_cons, mul_apply, swap_apply_def] at h
      split_ifs  at h <;> simp [IH _ _ hx]
    · replace hx :=
        (Function.Injective.eq_iff (Equiv.injective _)).mp (List.formPerm_apply_of_not_mem _ _ hx)
      simp only [List.formPerm_cons_cons, hx, Equiv.Perm.coe_mul, Function.comp_apply,
        List.mem_cons, swap_apply_def, ite_eq_left_iff] at h
      simp only [List.mem_cons]
      obtain h | h | h := h <;> · split_ifs  at h <;> cc
#align list.mem_of_form_perm_apply_mem List.mem_of_formPerm_apply_mem
-/

#print List.formPerm_mem_iff_mem /-
theorem formPerm_mem_iff_mem : l.formPerm x ∈ l ↔ x ∈ l :=
  ⟨l.mem_of_formPerm_apply_mem x, l.formPerm_apply_mem_of_mem x⟩
#align list.form_perm_mem_iff_mem List.formPerm_mem_iff_mem
-/

#print List.formPerm_cons_concat_apply_last /-
@[simp]
theorem formPerm_cons_concat_apply_last (x y : α) (xs : List α) :
    formPerm (x :: (xs ++ [y])) y = x :=
  by
  induction' xs with z xs IH generalizing x y
  · simp
  · simp [IH]
#align list.form_perm_cons_concat_apply_last List.formPerm_cons_concat_apply_last
-/

#print List.formPerm_apply_getLast /-
@[simp]
theorem formPerm_apply_getLast (x : α) (xs : List α) :
    formPerm (x :: xs) ((x :: xs).getLast (cons_ne_nil x xs)) = x := by
  induction' xs using List.reverseRecOn with xs y IH generalizing x <;> simp
#align list.form_perm_apply_last List.formPerm_apply_getLast
-/

#print List.formPerm_apply_nthLe_length /-
@[simp]
theorem formPerm_apply_nthLe_length (x : α) (xs : List α) :
    formPerm (x :: xs) ((x :: xs).nthLe xs.length (by simp)) = x := by
  rw [nth_le_cons_length, form_perm_apply_last] <;> rfl
#align list.form_perm_apply_nth_le_length List.formPerm_apply_nthLe_length
-/

#print List.formPerm_apply_head /-
theorem formPerm_apply_head (x y : α) (xs : List α) (h : Nodup (x :: y :: xs)) :
    formPerm (x :: y :: xs) x = y := by simp [form_perm_apply_of_not_mem _ _ h.not_mem]
#align list.form_perm_apply_head List.formPerm_apply_head
-/

#print List.formPerm_apply_nthLe_zero /-
theorem formPerm_apply_nthLe_zero (l : List α) (h : Nodup l) (hl : 1 < l.length) :
    formPerm l (l.nthLe 0 (zero_lt_one.trans hl)) = l.nthLe 1 hl :=
  by
  rcases l with (_ | ⟨x, _ | ⟨y, tl⟩⟩)
  · simp
  · simp
  · simpa using form_perm_apply_head _ _ _ h
#align list.form_perm_apply_nth_le_zero List.formPerm_apply_nthLe_zero
-/

variable (l)

#print List.formPerm_eq_head_iff_eq_getLast /-
theorem formPerm_eq_head_iff_eq_getLast (x y : α) :
    formPerm (y :: l) x = y ↔ x = getLast (y :: l) (cons_ne_nil _ _) :=
  Iff.trans (by rw [form_perm_apply_last]) (formPerm (y :: l)).Injective.eq_iff
#align list.form_perm_eq_head_iff_eq_last List.formPerm_eq_head_iff_eq_getLast
-/

#print List.zipWith_swap_prod_support' /-
theorem zipWith_swap_prod_support' (l l' : List α) :
    { x | (zipWith swap l l').Prod x ≠ x } ≤ l.toFinset ⊔ l'.toFinset :=
  by
  simp only [Set.sup_eq_union, Set.le_eq_subset]
  induction' l with y l hl generalizing l'
  · simp
  · cases' l' with z l'
    · simp
    · intro x
      simp only [Set.union_subset_iff, mem_cons_iff, zip_with_cons_cons, foldr, prod_cons,
        mul_apply]
      intro hx
      by_cases h : x ∈ { x | (zip_with swap l l').Prod x ≠ x }
      · specialize hl l' h
        refine' Set.MemUnion.elim hl (fun hm => _) fun hm => _ <;>
          · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, to_finset_cons,
              mem_to_finset] at hm⊢
            simp [hm]
      · simp only [Classical.not_not, Set.mem_setOf_eq] at h
        simp only [h, Set.mem_setOf_eq] at hx
        rw [swap_apply_ne_self_iff] at hx
        rcases hx with ⟨hyz, rfl | rfl⟩ <;> simp
#align list.zip_with_swap_prod_support' List.zipWith_swap_prod_support'
-/

/- warning: list.zip_with_swap_prod_support -> List.zipWith_swap_prod_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (l : List.{u1} α) (l' : List.{u1} α), LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (List.zipWith.{u1, u1, u1} α α (Equiv.Perm.{succ u1} α) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b)) l l'))) (HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l'))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (l : List.{u1} α) (l' : List.{u1} α), LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Equiv.Perm.Support.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (List.zipWith.{u1, u1, u1} α α (Equiv.Perm.{succ u1} α) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b)) l l'))) (HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l'))
Case conversion may be inaccurate. Consider using '#align list.zip_with_swap_prod_support List.zipWith_swap_prod_supportₓ'. -/
theorem zipWith_swap_prod_support [Fintype α] (l l' : List α) :
    (zipWith swap l l').Prod.Support ≤ l.toFinset ⊔ l'.toFinset :=
  by
  intro x hx
  have hx' : x ∈ { x | (zip_with swap l l').Prod x ≠ x } := by simpa using hx
  simpa using zip_with_swap_prod_support' _ _ hx'
#align list.zip_with_swap_prod_support List.zipWith_swap_prod_support

#print List.support_formPerm_le' /-
theorem support_formPerm_le' : { x | formPerm l x ≠ x } ≤ l.toFinset :=
  by
  refine' (zip_with_swap_prod_support' l l.tail).trans _
  simpa [Finset.subset_iff] using tail_subset l
#align list.support_form_perm_le' List.support_formPerm_le'
-/

#print List.support_formPerm_le /-
theorem support_formPerm_le [Fintype α] : Support (formPerm l) ≤ l.toFinset :=
  by
  intro x hx
  have hx' : x ∈ { x | form_perm l x ≠ x } := by simpa using hx
  simpa using support_form_perm_le' _ hx'
#align list.support_form_perm_le List.support_formPerm_le
-/

#print List.formPerm_apply_lt /-
theorem formPerm_apply_lt (xs : List α) (h : Nodup xs) (n : ℕ) (hn : n + 1 < xs.length) :
    formPerm xs (xs.nthLe n ((Nat.lt_succ_self n).trans hn)) = xs.nthLe (n + 1) hn :=
  by
  induction' n with n IH generalizing xs
  · simpa using form_perm_apply_nth_le_zero _ h _
  · rcases xs with (_ | ⟨x, _ | ⟨y, l⟩⟩)
    · simp
    · simp
    · specialize IH (y :: l) h.of_cons _
      · simpa [Nat.succ_lt_succ_iff] using hn
      simp only [swap_apply_eq_iff, coe_mul, form_perm_cons_cons, nth_le]
      generalize_proofs  at IH
      rw [IH, swap_apply_of_ne_of_ne, nth_le] <;>
        · rintro rfl
          simpa [nth_le_mem _ _ _] using h
#align list.form_perm_apply_lt List.formPerm_apply_lt
-/

#print List.formPerm_apply_nthLe /-
theorem formPerm_apply_nthLe (xs : List α) (h : Nodup xs) (n : ℕ) (hn : n < xs.length) :
    formPerm xs (xs.nthLe n hn) =
      xs.nthLe ((n + 1) % xs.length) (Nat.mod_lt _ (n.zero_le.trans_lt hn)) :=
  by
  cases' xs with x xs
  · simp
  · have : n ≤ xs.length := by
      refine' Nat.le_of_lt_succ _
      simpa using hn
    rcases this.eq_or_lt with (rfl | hn')
    · simp
    · simp [form_perm_apply_lt, h, Nat.mod_eq_of_lt, Nat.succ_lt_succ hn']
#align list.form_perm_apply_nth_le List.formPerm_apply_nthLe
-/

#print List.support_formPerm_of_nodup' /-
theorem support_formPerm_of_nodup' (l : List α) (h : Nodup l) (h' : ∀ x : α, l ≠ [x]) :
    { x | formPerm l x ≠ x } = l.toFinset :=
  by
  apply le_antisymm
  · exact support_form_perm_le' l
  · intro x hx
    simp only [Finset.mem_coe, mem_to_finset] at hx
    obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx
    rw [Set.mem_setOf_eq, form_perm_apply_nth_le _ h]
    intro H
    rw [nodup_iff_nth_le_inj] at h
    specialize h _ _ _ _ H
    cases' (Nat.succ_le_of_lt hn).eq_or_lt with hn' hn'
    · simp only [← hn', Nat.mod_self] at h
      refine' not_exists.mpr h' _
      simpa [← h, eq_comm, length_eq_one] using hn'
    · simpa [Nat.mod_eq_of_lt hn'] using h
#align list.support_form_perm_of_nodup' List.support_formPerm_of_nodup'
-/

#print List.support_formPerm_of_nodup /-
theorem support_formPerm_of_nodup [Fintype α] (l : List α) (h : Nodup l) (h' : ∀ x : α, l ≠ [x]) :
    Support (formPerm l) = l.toFinset :=
  by
  rw [← Finset.coe_inj]
  convert support_form_perm_of_nodup' _ h h'
  simp [Set.ext_iff]
#align list.support_form_perm_of_nodup List.support_formPerm_of_nodup
-/

#print List.formPerm_rotate_one /-
theorem formPerm_rotate_one (l : List α) (h : Nodup l) : formPerm (l.rotate 1) = formPerm l :=
  by
  have h' : nodup (l.rotate 1) := by simpa using h
  ext x
  by_cases hx : x ∈ l.rotate 1
  · obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx
    rw [form_perm_apply_nth_le _ h', nth_le_rotate l, nth_le_rotate l, form_perm_apply_nth_le _ h]
    simp
  · rw [form_perm_apply_of_not_mem _ _ hx, form_perm_apply_of_not_mem]
    simpa using hx
#align list.form_perm_rotate_one List.formPerm_rotate_one
-/

#print List.formPerm_rotate /-
theorem formPerm_rotate (l : List α) (h : Nodup l) (n : ℕ) : formPerm (l.rotate n) = formPerm l :=
  by
  induction' n with n hn
  · simp
  · rw [Nat.succ_eq_add_one, ← rotate_rotate, form_perm_rotate_one, hn]
    rwa [is_rotated.nodup_iff]
    exact is_rotated.forall l n
#align list.form_perm_rotate List.formPerm_rotate
-/

#print List.formPerm_eq_of_isRotated /-
theorem formPerm_eq_of_isRotated {l l' : List α} (hd : Nodup l) (h : l ~r l') :
    formPerm l = formPerm l' := by
  obtain ⟨n, rfl⟩ := h
  exact (form_perm_rotate l hd n).symm
#align list.form_perm_eq_of_is_rotated List.formPerm_eq_of_isRotated
-/

/- warning: list.form_perm_reverse -> List.formPerm_reverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α), (List.Nodup.{u1} α l) -> (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.reverse.{u1} α l)) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α), (List.Nodup.{u1} α l) -> (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.reverse.{u1} α l)) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l)))
Case conversion may be inaccurate. Consider using '#align list.form_perm_reverse List.formPerm_reverseₓ'. -/
theorem formPerm_reverse (l : List α) (h : Nodup l) : formPerm l.reverse = (formPerm l)⁻¹ :=
  by
  -- Let's show `form_perm l` is an inverse to `form_perm l.reverse`.
  rw [eq_comm, inv_eq_iff_mul_eq_one]
  ext x
  -- We only have to check for `x ∈ l` that `form_perm l (form_perm l.reverse x)`
  rw [mul_apply, one_apply]
  by_cases hx : x ∈ l
  swap
  · rw [form_perm_apply_of_not_mem x l.reverse, form_perm_apply_of_not_mem _ _ hx]
    simpa using hx
  · obtain ⟨k, hk, rfl⟩ := nth_le_of_mem (mem_reverse.mpr hx)
    rw [form_perm_apply_nth_le l.reverse (nodup_reverse.mpr h), nth_le_reverse',
      form_perm_apply_nth_le _ h, nth_le_reverse']
    · congr
      rw [length_reverse, ← Nat.succ_le_iff, Nat.succ_eq_add_one] at hk
      cases' hk.eq_or_lt with hk' hk'
      · simp [← hk']
      · rw [length_reverse, Nat.mod_eq_of_lt hk', tsub_add_eq_add_tsub (Nat.le_pred_of_lt hk'),
          Nat.mod_eq_of_lt]
        · simp
        · rw [tsub_add_cancel_of_le]
          refine' tsub_lt_self _ (Nat.zero_lt_succ _)
          all_goals simpa using (Nat.zero_le _).trans_lt hk'
    all_goals
      rw [← tsub_add_eq_tsub_tsub, ← length_reverse]
      refine' tsub_lt_self _ (zero_lt_one.trans_le (le_add_right le_rfl))
      exact k.zero_le.trans_lt hk
#align list.form_perm_reverse List.formPerm_reverse

#print List.formPerm_pow_apply_nthLe /-
theorem formPerm_pow_apply_nthLe (l : List α) (h : Nodup l) (n k : ℕ) (hk : k < l.length) :
    (formPerm l ^ n) (l.nthLe k hk) =
      l.nthLe ((k + n) % l.length) (Nat.mod_lt _ (k.zero_le.trans_lt hk)) :=
  by
  induction' n with n hn
  · simp [Nat.mod_eq_of_lt hk]
  · simp [pow_succ, mul_apply, hn, form_perm_apply_nth_le _ h, Nat.succ_eq_add_one, ← Nat.add_assoc]
#align list.form_perm_pow_apply_nth_le List.formPerm_pow_apply_nthLe
-/

#print List.formPerm_pow_apply_head /-
theorem formPerm_pow_apply_head (x : α) (l : List α) (h : Nodup (x :: l)) (n : ℕ) :
    (formPerm (x :: l) ^ n) x =
      (x :: l).nthLe (n % (x :: l).length) (Nat.mod_lt _ (Nat.zero_lt_succ _)) :=
  by convert form_perm_pow_apply_nth_le _ h n 0 _ <;> simp
#align list.form_perm_pow_apply_head List.formPerm_pow_apply_head
-/

#print List.formPerm_ext_iff /-
theorem formPerm_ext_iff {x y x' y' : α} {l l' : List α} (hd : Nodup (x :: y :: l))
    (hd' : Nodup (x' :: y' :: l')) :
    formPerm (x :: y :: l) = formPerm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') :=
  by
  refine' ⟨fun h => _, fun hr => form_perm_eq_of_is_rotated hd hr⟩
  rw [Equiv.Perm.ext_iff] at h
  have hx : x' ∈ x :: y :: l :=
    by
    have : x' ∈ { z | form_perm (x :: y :: l) z ≠ z } :=
      by
      rw [Set.mem_setOf_eq, h x', form_perm_apply_head _ _ _ hd']
      simp only [mem_cons_iff, nodup_cons] at hd'
      push_neg  at hd'
      exact hd'.left.left.symm
    simpa using support_form_perm_le' _ this
  obtain ⟨n, hn, hx'⟩ := nth_le_of_mem hx
  have hl : (x :: y :: l).length = (x' :: y' :: l').length :=
    by
    rw [← dedup_eq_self.mpr hd, ← dedup_eq_self.mpr hd', ← card_to_finset, ← card_to_finset]
    refine' congr_arg Finset.card _
    rw [← Finset.coe_inj, ← support_form_perm_of_nodup' _ hd (by simp), ←
      support_form_perm_of_nodup' _ hd' (by simp)]
    simp only [h]
  use n
  apply List.ext_nthLe
  · rw [length_rotate, hl]
  · intro k hk hk'
    rw [nth_le_rotate]
    induction' k with k IH
    · simp_rw [Nat.zero_add, Nat.mod_eq_of_lt hn]
      simpa
    · have : k.succ = (k + 1) % (x' :: y' :: l').length := by
        rw [← Nat.succ_eq_add_one, Nat.mod_eq_of_lt hk']
      simp_rw [this]
      rw [← form_perm_apply_nth_le _ hd' k (k.lt_succ_self.trans hk'), ←
        IH (k.lt_succ_self.trans hk), ← h, form_perm_apply_nth_le _ hd]
      congr 1
      have h1 : 1 = 1 % (x' :: y' :: l').length := by simp
      rw [hl, Nat.mod_eq_of_lt hk', h1, ← Nat.add_mod, Nat.succ_add]
#align list.form_perm_ext_iff List.formPerm_ext_iff
-/

#print List.formPerm_apply_mem_eq_self_iff /-
theorem formPerm_apply_mem_eq_self_iff (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = x ↔ length l ≤ 1 :=
  by
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx
  rw [form_perm_apply_nth_le _ hl, hl.nth_le_inj_iff]
  cases hn : l.length
  · exact absurd k.zero_le (hk.trans_le hn.le).not_le
  · rw [hn] at hk
    cases' (Nat.le_of_lt_succ hk).eq_or_lt with hk' hk'
    · simp [← hk', Nat.succ_le_succ_iff, eq_comm]
    ·
      simpa [Nat.mod_eq_of_lt (Nat.succ_lt_succ hk'), Nat.succ_lt_succ_iff] using
        k.zero_le.trans_lt hk'
#align list.form_perm_apply_mem_eq_self_iff List.formPerm_apply_mem_eq_self_iff
-/

#print List.formPerm_apply_mem_ne_self_iff /-
theorem formPerm_apply_mem_ne_self_iff (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x ≠ x ↔ 2 ≤ l.length :=
  by
  rw [Ne.def, form_perm_apply_mem_eq_self_iff _ hl x hx, not_le]
  exact ⟨Nat.succ_le_of_lt, Nat.lt_of_succ_le⟩
#align list.form_perm_apply_mem_ne_self_iff List.formPerm_apply_mem_ne_self_iff
-/

#print List.mem_of_formPerm_ne_self /-
theorem mem_of_formPerm_ne_self (l : List α) (x : α) (h : formPerm l x ≠ x) : x ∈ l :=
  by
  suffices x ∈ { y | form_perm l y ≠ y }
    by
    rw [← mem_to_finset]
    exact support_form_perm_le' _ this
  simpa using h
#align list.mem_of_form_perm_ne_self List.mem_of_formPerm_ne_self
-/

#print List.formPerm_eq_self_of_not_mem /-
theorem formPerm_eq_self_of_not_mem (l : List α) (x : α) (h : x ∉ l) : formPerm l x = x :=
  by_contra fun H => h <| mem_of_formPerm_ne_self _ _ H
#align list.form_perm_eq_self_of_not_mem List.formPerm_eq_self_of_not_mem
-/

/- warning: list.form_perm_eq_one_iff -> List.formPerm_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α), (List.Nodup.{u1} α l) -> (Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) (LE.le.{0} Nat Nat.hasLe (List.length.{u1} α l) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α), (List.Nodup.{u1} α l) -> (Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (LE.le.{0} Nat instLENat (List.length.{u1} α l) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align list.form_perm_eq_one_iff List.formPerm_eq_one_iffₓ'. -/
theorem formPerm_eq_one_iff (hl : Nodup l) : formPerm l = 1 ↔ l.length ≤ 1 :=
  by
  cases' l with hd tl
  · simp
  · rw [← form_perm_apply_mem_eq_self_iff _ hl hd (mem_cons_self _ _)]
    constructor
    · simp (config := { contextual := true })
    · intro h
      simp only [(hd :: tl).formPerm_apply_mem_eq_self_iff hl hd (mem_cons_self hd tl),
        add_le_iff_nonpos_left, length, nonpos_iff_eq_zero, length_eq_zero] at h
      simp [h]
#align list.form_perm_eq_one_iff List.formPerm_eq_one_iff

#print List.formPerm_eq_formPerm_iff /-
theorem formPerm_eq_formPerm_iff {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) :
    l.formPerm = l'.formPerm ↔ l ~r l' ∨ l.length ≤ 1 ∧ l'.length ≤ 1 :=
  by
  rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩)
  · suffices l'.length ≤ 1 ↔ l' = nil ∨ l'.length ≤ 1 by
      simpa [eq_comm, form_perm_eq_one_iff, hl, hl', length_eq_zero]
    refine' ⟨fun h => Or.inr h, _⟩
    rintro (rfl | h)
    · simp
    · exact h
  · suffices l'.length ≤ 1 ↔ [x] ~r l' ∨ l'.length ≤ 1 by
      simpa [eq_comm, form_perm_eq_one_iff, hl, hl', length_eq_zero, le_rfl]
    refine' ⟨fun h => Or.inr h, _⟩
    rintro (h | h)
    · simp [← h.perm.length_eq]
    · exact h
  · rcases l' with (_ | ⟨x', _ | ⟨y', l'⟩⟩)
    · simp [form_perm_eq_one_iff, hl, -form_perm_cons_cons]
    · suffices ¬(x :: y :: l) ~r [x'] by simp [form_perm_eq_one_iff, hl, -form_perm_cons_cons]
      intro h
      simpa using h.perm.length_eq
    · simp [-form_perm_cons_cons, form_perm_ext_iff hl hl']
#align list.form_perm_eq_form_perm_iff List.formPerm_eq_formPerm_iff
-/

#print List.form_perm_zpow_apply_mem_imp_mem /-
theorem form_perm_zpow_apply_mem_imp_mem (l : List α) (x : α) (hx : x ∈ l) (n : ℤ) :
    (formPerm l ^ n) x ∈ l := by
  by_cases h : (l.form_perm ^ n) x = x
  · simpa [h] using hx
  · have : x ∈ { x | (l.form_perm ^ n) x ≠ x } := h
    rw [← set_support_apply_mem] at this
    replace this := set_support_zpow_subset _ _ this
    simpa using support_form_perm_le' _ this
#align list.form_perm_zpow_apply_mem_imp_mem List.form_perm_zpow_apply_mem_imp_mem
-/

/- warning: list.form_perm_pow_length_eq_one_of_nodup -> List.formPerm_pow_length_eq_one_of_nodup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α), (List.Nodup.{u1} α l) -> (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HPow.hPow.{u1, 0, u1} (Equiv.Perm.{succ u1} α) Nat (Equiv.Perm.{succ u1} α) (instHPow.{u1, 0} (Equiv.Perm.{succ u1} α) Nat (Monoid.Pow.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) (List.length.{u1} α l)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α), (List.Nodup.{u1} α l) -> (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HPow.hPow.{u1, 0, u1} (Equiv.Perm.{succ u1} α) Nat (Equiv.Perm.{succ u1} α) (instHPow.{u1, 0} (Equiv.Perm.{succ u1} α) Nat (Monoid.Pow.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (List.formPerm.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) (List.length.{u1} α l)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
Case conversion may be inaccurate. Consider using '#align list.form_perm_pow_length_eq_one_of_nodup List.formPerm_pow_length_eq_one_of_nodupₓ'. -/
theorem formPerm_pow_length_eq_one_of_nodup (hl : Nodup l) : formPerm l ^ length l = 1 :=
  by
  ext x
  by_cases hx : x ∈ l
  · obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx
    simp [form_perm_pow_apply_nth_le _ hl, Nat.mod_eq_of_lt hk]
  · have : x ∉ { x | (l.form_perm ^ l.length) x ≠ x } :=
      by
      intro H
      refine' hx _
      replace H := set_support_zpow_subset l.form_perm l.length H
      simpa using support_form_perm_le' _ H
    simpa
#align list.form_perm_pow_length_eq_one_of_nodup List.formPerm_pow_length_eq_one_of_nodup

end FormPerm

end List

