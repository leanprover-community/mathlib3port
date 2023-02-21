/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module data.finsupp.antidiagonal
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Multiset
import Mathbin.Data.Multiset.Antidiagonal

/-!
# The `finsupp` counterpart of `multiset.antidiagonal`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The antidiagonal of `s : α →₀ ℕ` consists of
all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
-/


noncomputable section

open Classical BigOperators

namespace Finsupp

open Finset

variable {α : Type _}

#print Finsupp.antidiagonal' /-
/-- The `finsupp` counterpart of `multiset.antidiagonal`: the antidiagonal of
`s : α →₀ ℕ` consists of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
The finitely supported function `antidiagonal s` is equal to the multiplicities of these pairs. -/
def antidiagonal' (f : α →₀ ℕ) : (α →₀ ℕ) × (α →₀ ℕ) →₀ ℕ :=
  (f.toMultiset.antidiagonal.map (Prod.map Multiset.toFinsupp Multiset.toFinsupp)).toFinsupp
#align finsupp.antidiagonal' Finsupp.antidiagonal'
-/

#print Finsupp.antidiagonal /-
/-- The antidiagonal of `s : α →₀ ℕ` is the finset of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)`
such that `t₁ + t₂ = s`. -/
def antidiagonal (f : α →₀ ℕ) : Finset ((α →₀ ℕ) × (α →₀ ℕ)) :=
  f.antidiagonal'.support
#align finsupp.antidiagonal Finsupp.antidiagonal
-/

/- warning: finsupp.mem_antidiagonal -> Finsupp.mem_antidiagonal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Finsupp.{u1, 0} α Nat Nat.hasZero} {p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)}, Iff (Membership.Mem.{u1, u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Finset.hasMem.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) p (Finsupp.antidiagonal.{u1} α f)) (Eq.{succ u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (HAdd.hAdd.{u1, u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) (instHAdd.{u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.hasAdd.{u1, 0} α Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid))) (Prod.fst.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p) (Prod.snd.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p)) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)} {p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))}, Iff (Membership.mem.{u1, u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Finset.instMembershipFinset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) p (Finsupp.antidiagonal.{u1} α f)) (Eq.{succ u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (HAdd.hAdd.{u1, u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (instHAdd.{u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.add.{u1, 0} α Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid))) (Prod.fst.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p) (Prod.snd.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p)) f)
Case conversion may be inaccurate. Consider using '#align finsupp.mem_antidiagonal Finsupp.mem_antidiagonalₓ'. -/
@[simp]
theorem mem_antidiagonal {f : α →₀ ℕ} {p : (α →₀ ℕ) × (α →₀ ℕ)} :
    p ∈ antidiagonal f ↔ p.1 + p.2 = f :=
  by
  rcases p with ⟨p₁, p₂⟩
  simp [antidiagonal, antidiagonal', ← and_assoc, ← finsupp.to_multiset.apply_eq_iff_eq]
#align finsupp.mem_antidiagonal Finsupp.mem_antidiagonal

#print Finsupp.swap_mem_antidiagonal /-
theorem swap_mem_antidiagonal {n : α →₀ ℕ} {f : (α →₀ ℕ) × (α →₀ ℕ)} :
    f.symm ∈ antidiagonal n ↔ f ∈ antidiagonal n := by
  simp only [mem_antidiagonal, add_comm, Prod.swap]
#align finsupp.swap_mem_antidiagonal Finsupp.swap_mem_antidiagonal
-/

/- warning: finsupp.antidiagonal_filter_fst_eq -> Finsupp.antidiagonal_filter_fst_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Finsupp.{u1, 0} α Nat Nat.hasZero) (g : Finsupp.{u1, 0} α Nat Nat.hasZero) [D : forall (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)), Decidable (Eq.{succ u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Prod.fst.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p) g)], Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Finset.filter.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) (fun (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) => Eq.{succ u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Prod.fst.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p) g) (fun (a : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) => D a) (Finsupp.antidiagonal.{u1} α f)) (ite.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (LE.le.{u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.hasLe.{u1, 0} α Nat Nat.hasZero Nat.hasLe) g f) (Finsupp.decidableLe.{u1, 0} α Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring) (fun (a : Nat) (b : Nat) => Nat.decidableLe a b) g f) (Singleton.singleton.{u1, u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Finset.hasSingleton.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Prod.mk.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) g (HSub.hSub.{u1, u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) (instHSub.{u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.tsub.{u1, 0} α Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring) Nat.hasSub Nat.hasOrderedSub)) f g))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Finset.hasEmptyc.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} (f : Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (g : Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) [D : forall (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))), Decidable (Eq.{succ u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Prod.fst.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p) g)], Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Finset.filter.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (fun (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) => Eq.{succ u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Prod.fst.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p) g) (fun (a : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) => D a) (Finsupp.antidiagonal.{u1} α f)) (ite.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (LE.le.{u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.instLEFinsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) instLENat) g f) (Finsupp.decidableLe.{u1, 0} α Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring) (fun (a : Nat) (b : Nat) => Nat.decLe a b) g f) (Singleton.singleton.{u1, u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Finset.instSingletonFinset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Prod.mk.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) g (HSub.hSub.{u1, u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (instHSub.{u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.tsub.{u1, 0} α Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring) instSubNat Nat.instOrderedSubNatInstLENatInstAddNatInstSubNat)) f g))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Finset.instEmptyCollectionFinset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))))))
Case conversion may be inaccurate. Consider using '#align finsupp.antidiagonal_filter_fst_eq Finsupp.antidiagonal_filter_fst_eqₓ'. -/
theorem antidiagonal_filter_fst_eq (f g : α →₀ ℕ)
    [D : ∀ p : (α →₀ ℕ) × (α →₀ ℕ), Decidable (p.1 = g)] :
    ((antidiagonal f).filterₓ fun p => p.1 = g) = if g ≤ f then {(g, f - g)} else ∅ :=
  by
  ext ⟨a, b⟩
  suffices a = g → (a + b = f ↔ g ≤ f ∧ b = f - g) by
    simpa [apply_ite ((· ∈ ·) (a, b)), ← and_assoc, @and_right_comm _ (a = _), and_congr_left_iff]
  rintro rfl
  constructor
  · rintro rfl
    exact ⟨le_add_right le_rfl, (add_tsub_cancel_left _ _).symm⟩
  · rintro ⟨h, rfl⟩
    exact add_tsub_cancel_of_le h
#align finsupp.antidiagonal_filter_fst_eq Finsupp.antidiagonal_filter_fst_eq

/- warning: finsupp.antidiagonal_filter_snd_eq -> Finsupp.antidiagonal_filter_snd_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Finsupp.{u1, 0} α Nat Nat.hasZero) (g : Finsupp.{u1, 0} α Nat Nat.hasZero) [D : forall (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)), Decidable (Eq.{succ u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Prod.snd.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p) g)], Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Finset.filter.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) (fun (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) => Eq.{succ u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Prod.snd.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p) g) (fun (a : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) => D a) (Finsupp.antidiagonal.{u1} α f)) (ite.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (LE.le.{u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.hasLe.{u1, 0} α Nat Nat.hasZero Nat.hasLe) g f) (Finsupp.decidableLe.{u1, 0} α Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring) (fun (a : Nat) (b : Nat) => Nat.decidableLe a b) g f) (Singleton.singleton.{u1, u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Finset.hasSingleton.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Prod.mk.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) (HSub.hSub.{u1, u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) (instHSub.{u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.tsub.{u1, 0} α Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring) Nat.hasSub Nat.hasOrderedSub)) f g) g)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero))) (Finset.hasEmptyc.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} (f : Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (g : Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) [D : forall (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))), Decidable (Eq.{succ u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Prod.snd.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p) g)], Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Finset.filter.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (fun (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) => Eq.{succ u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Prod.snd.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p) g) (fun (a : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) => D a) (Finsupp.antidiagonal.{u1} α f)) (ite.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (LE.le.{u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.instLEFinsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) instLENat) g f) (Finsupp.decidableLe.{u1, 0} α Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring) (fun (a : Nat) (b : Nat) => Nat.decLe a b) g f) (Singleton.singleton.{u1, u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Finset.instSingletonFinset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Prod.mk.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (HSub.hSub.{u1, u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (instHSub.{u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.tsub.{u1, 0} α Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring) instSubNat Nat.instOrderedSubNatInstLENatInstAddNatInstSubNat)) f g) g)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Finset.instEmptyCollectionFinset.{u1} (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))))))
Case conversion may be inaccurate. Consider using '#align finsupp.antidiagonal_filter_snd_eq Finsupp.antidiagonal_filter_snd_eqₓ'. -/
theorem antidiagonal_filter_snd_eq (f g : α →₀ ℕ)
    [D : ∀ p : (α →₀ ℕ) × (α →₀ ℕ), Decidable (p.2 = g)] :
    ((antidiagonal f).filterₓ fun p => p.2 = g) = if g ≤ f then {(f - g, g)} else ∅ :=
  by
  ext ⟨a, b⟩
  suffices b = g → (a + b = f ↔ g ≤ f ∧ a = f - g) by
    simpa [apply_ite ((· ∈ ·) (a, b)), ← and_assoc, and_congr_left_iff]
  rintro rfl
  constructor
  · rintro rfl
    exact ⟨le_add_left le_rfl, (add_tsub_cancel_right _ _).symm⟩
  · rintro ⟨h, rfl⟩
    exact tsub_add_cancel_of_le h
#align finsupp.antidiagonal_filter_snd_eq Finsupp.antidiagonal_filter_snd_eq

#print Finsupp.antidiagonal_zero /-
@[simp]
theorem antidiagonal_zero : antidiagonal (0 : α →₀ ℕ) = singleton (0, 0) := by
  rw [antidiagonal, antidiagonal', Multiset.toFinsupp_support] <;> rfl
#align finsupp.antidiagonal_zero Finsupp.antidiagonal_zero
-/

/- warning: finsupp.prod_antidiagonal_swap -> Finsupp.prod_antidiagonal_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (n : Finsupp.{u1, 0} α Nat Nat.hasZero) (f : (Finsupp.{u1, 0} α Nat Nat.hasZero) -> (Finsupp.{u1, 0} α Nat Nat.hasZero) -> M), Eq.{succ u2} M (Finset.prod.{u2, u1} M (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) _inst_1 (Finsupp.antidiagonal.{u1} α n) (fun (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) => f (Prod.fst.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p) (Prod.snd.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p))) (Finset.prod.{u2, u1} M (Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) _inst_1 (Finsupp.antidiagonal.{u1} α n) (fun (p : Prod.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero)) => f (Prod.snd.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p) (Prod.fst.{u1, u1} (Finsupp.{u1, 0} α Nat Nat.hasZero) (Finsupp.{u1, 0} α Nat Nat.hasZero) p)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (n : Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (f : (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) -> (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) -> M), Eq.{succ u1} M (Finset.prod.{u1, u2} M (Prod.{u2, u2} (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) _inst_1 (Finsupp.antidiagonal.{u2} α n) (fun (p : Prod.{u2, u2} (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) => f (Prod.fst.{u2, u2} (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p) (Prod.snd.{u2, u2} (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p))) (Finset.prod.{u1, u2} M (Prod.{u2, u2} (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) _inst_1 (Finsupp.antidiagonal.{u2} α n) (fun (p : Prod.{u2, u2} (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) => f (Prod.snd.{u2, u2} (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p) (Prod.fst.{u2, u2} (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finsupp.{u2, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) p)))
Case conversion may be inaccurate. Consider using '#align finsupp.prod_antidiagonal_swap Finsupp.prod_antidiagonal_swapₓ'. -/
@[to_additive]
theorem prod_antidiagonal_swap {M : Type _} [CommMonoid M] (n : α →₀ ℕ)
    (f : (α →₀ ℕ) → (α →₀ ℕ) → M) :
    (∏ p in antidiagonal n, f p.1 p.2) = ∏ p in antidiagonal n, f p.2 p.1 :=
  Finset.prod_bij (fun p hp => p.symm) (fun p => swap_mem_antidiagonal.2) (fun p hp => rfl)
    (fun p₁ p₂ _ _ h => Prod.swap_injective h) fun p hp =>
    ⟨p.symm, swap_mem_antidiagonal.2 hp, p.swap_swap.symm⟩
#align finsupp.prod_antidiagonal_swap Finsupp.prod_antidiagonal_swap
#align finsupp.sum_antidiagonal_swap Finsupp.sum_antidiagonal_swap

end Finsupp

