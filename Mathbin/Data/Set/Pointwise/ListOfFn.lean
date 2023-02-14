/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.set.pointwise.list_of_fn
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Data.List.OfFn

/-!
# Pointwise operations with lists of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some lemmas about pointwise algebraic operations with lists of sets.
-/


namespace Set

variable {F α β γ : Type _}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

open Pointwise

/- warning: set.mem_prod_list_of_fn -> Set.mem_prod_list_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} {a : α} {s : (Fin n) -> (Set.{u1} α)}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (List.ofFn.{u1} (Set.{u1} α) n s))) (Exists.{succ u1} (forall (i : Fin n), coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (s i)) (fun (f : forall (i : Fin n), coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (s i)) => Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (List.ofFn.{u1} α n (fun (i : Fin n) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (s i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (s i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (s i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (s i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)))))) (f i)))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} {a : α} {s : (Fin n) -> (Set.{u1} α)}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Set.one.{u1} α (Monoid.toOne.{u1} α _inst_1)) (List.ofFn.{u1} (Set.{u1} α) n s))) (Exists.{succ u1} (forall (i : Fin n), Set.Elem.{u1} α (s i)) (fun (f : forall (i : Fin n), Set.Elem.{u1} α (s i)) => Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (List.ofFn.{u1} α n (fun (i : Fin n) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (s i)) (f i)))) a))
Case conversion may be inaccurate. Consider using '#align set.mem_prod_list_of_fn Set.mem_prod_list_ofFnₓ'. -/
@[to_additive]
theorem mem_prod_list_ofFn {a : α} {s : Fin n → Set α} :
    a ∈ (List.ofFn s).Prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).Prod = a :=
  by
  induction' n with n ih generalizing a
  · simp_rw [List.ofFn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
  ·
    simp_rw [List.ofFn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ,
      mem_mul, @ih, exists_and_left, exists_exists_eq_and, SetCoe.exists, Subtype.coe_mk,
      exists_prop]
#align set.mem_prod_list_of_fn Set.mem_prod_list_ofFn
#align set.mem_sum_list_of_fn Set.mem_sum_list_ofFn

/- warning: set.mem_list_prod -> Set.mem_list_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {l : List.{u1} (Set.{u1} α)} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) l)) (Exists.{succ u1} (List.{u1} (Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s))) (fun (l' : List.{u1} (Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s))) => And (Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (List.map.{u1, u1} (Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) α (fun (x : Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Sigma.fst.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) x)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Sigma.fst.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) x)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Sigma.fst.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) x)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Sigma.fst.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) x)) α (coeSubtype.{succ u1} α (fun (x_1 : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x_1 (Sigma.fst.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) x)))))) (Sigma.snd.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) x)) l')) a) (Eq.{succ u1} (List.{u1} (Set.{u1} α)) (List.map.{u1, u1} (Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.{u1} α) (Sigma.fst.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) l') l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {l : List.{u1} (Set.{u1} α)} {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Set.one.{u1} α (Monoid.toOne.{u1} α _inst_1)) l)) (Exists.{succ u1} (List.{u1} (Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Set.Elem.{u1} α s))) (fun (l' : List.{u1} (Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Set.Elem.{u1} α s))) => And (Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (List.map.{u1, u1} (Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Set.Elem.{u1} α s)) α (fun (x : Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Set.Elem.{u1} α s)) => Subtype.val.{succ u1} α (fun (x_1 : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x_1 (Sigma.fst.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Set.Elem.{u1} α s) x)) (Sigma.snd.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Set.Elem.{u1} α s) x)) l')) a) (Eq.{succ u1} (List.{u1} (Set.{u1} α)) (List.map.{u1, u1} (Sigma.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Set.Elem.{u1} α s)) (Set.{u1} α) (Sigma.fst.{u1, u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Set.Elem.{u1} α s)) l') l)))
Case conversion may be inaccurate. Consider using '#align set.mem_list_prod Set.mem_list_prodₓ'. -/
@[to_additive]
theorem mem_list_prod {l : List (Set α)} {a : α} :
    a ∈ l.Prod ↔
      ∃ l' : List (Σs : Set α, ↥s),
        List.prod (l'.map fun x => (Sigma.snd x : α)) = a ∧ l'.map Sigma.fst = l :=
  by
  induction' l using List.ofFnRec with n f
  simp_rw [List.exists_iff_exists_tuple, List.map_ofFn, List.ofFn_inj', and_left_comm,
    exists_and_left, exists_eq_left, heq_iff_eq, Function.comp, mem_prod_list_of_fn]
  constructor
  · rintro ⟨fi, rfl⟩
    exact ⟨fun i => ⟨_, fi i⟩, rfl, rfl⟩
  · rintro ⟨fi, rfl, rfl⟩
    exact ⟨fun i => _, rfl⟩
#align set.mem_list_prod Set.mem_list_prod
#align set.mem_list_sum Set.mem_list_sum

/- warning: set.mem_pow -> Set.mem_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α} {a : α} {n : Nat}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s n)) (Exists.{succ u1} ((Fin n) -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (fun (f : (Fin n) -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) => Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (List.ofFn.{u1} α n (fun (i : Fin n) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) (f i)))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α} {a : α} {n : Nat}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s n)) (Exists.{succ u1} ((Fin n) -> (Set.Elem.{u1} α s)) (fun (f : (Fin n) -> (Set.Elem.{u1} α s)) => Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (List.ofFn.{u1} α n (fun (i : Fin n) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (f i)))) a))
Case conversion may be inaccurate. Consider using '#align set.mem_pow Set.mem_powₓ'. -/
@[to_additive]
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i => (f i : α)).Prod = a := by
  rw [← mem_prod_list_of_fn, List.ofFn_const, List.prod_replicate]
#align set.mem_pow Set.mem_pow
#align set.mem_nsmul Set.mem_nsmul

end Set

