/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module logic.function.iterate
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Function.Conjugate

/-!
# Iterations of a function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/585
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove simple properties of `nat.iterate f n` a.k.a. `f^[n]`:

* `iterate_zero`, `iterate_succ`, `iterate_succ'`, `iterate_add`, `iterate_mul`:
  formulas for `f^[0]`, `f^[n+1]` (two versions), `f^[n+m]`, and `f^[n*m]`;

* `iterate_id` : `id^[n]=id`;

* `injective.iterate`, `surjective.iterate`, `bijective.iterate` :
  iterates of an injective/surjective/bijective function belong to the same class;

* `left_inverse.iterate`, `right_inverse.iterate`, `commute.iterate_left`, `commute.iterate_right`,
  `commute.iterate_iterate`:
  some properties of pairs of functions survive under iterations

* `iterate_fixed`, `semiconj.iterate_*`, `semiconj₂.iterate`:
  if `f` fixes a point (resp., semiconjugates unary/binary operarations), then so does `f^[n]`.

-/


universe u v

variable {α : Type u} {β : Type v}

namespace Function

variable (f : α → α)

#print Function.iterate_zero /-
@[simp]
theorem iterate_zero : f^[0] = id :=
  rfl
#align function.iterate_zero Function.iterate_zero
-/

#print Function.iterate_zero_apply /-
theorem iterate_zero_apply (x : α) : (f^[0]) x = x :=
  rfl
#align function.iterate_zero_apply Function.iterate_zero_apply
-/

#print Function.iterate_succ /-
@[simp]
theorem iterate_succ (n : ℕ) : f^[n.succ] = f^[n] ∘ f :=
  rfl
#align function.iterate_succ Function.iterate_succ
-/

#print Function.iterate_succ_apply /-
theorem iterate_succ_apply (n : ℕ) (x : α) : (f^[n.succ]) x = (f^[n]) (f x) :=
  rfl
#align function.iterate_succ_apply Function.iterate_succ_apply
-/

#print Function.iterate_id /-
@[simp]
theorem iterate_id (n : ℕ) : (id : α → α)^[n] = id :=
  (Nat.recOn n rfl) fun n ihn => by rw [iterate_succ, ihn, comp.left_id]
#align function.iterate_id Function.iterate_id
-/

#print Function.iterate_add /-
theorem iterate_add : ∀ m n : ℕ, f^[m + n] = f^[m] ∘ f^[n]
  | m, 0 => rfl
  | m, Nat.succ n => by rw [Nat.add_succ, iterate_succ, iterate_succ, iterate_add]
#align function.iterate_add Function.iterate_add
-/

#print Function.iterate_add_apply /-
theorem iterate_add_apply (m n : ℕ) (x : α) : (f^[m + n]) x = (f^[m]) ((f^[n]) x) := by
  rw [iterate_add]
#align function.iterate_add_apply Function.iterate_add_apply
-/

#print Function.iterate_one /-
@[simp]
theorem iterate_one : f^[1] = f :=
  funext fun a => rfl
#align function.iterate_one Function.iterate_one
-/

#print Function.iterate_mul /-
theorem iterate_mul (m : ℕ) : ∀ n, f^[m * n] = f^[m]^[n]
  | 0 => by simp only [Nat.mul_zero, iterate_zero]
  | n + 1 => by simp only [Nat.mul_succ, Nat.mul_one, iterate_one, iterate_add, iterate_mul n]
#align function.iterate_mul Function.iterate_mul
-/

variable {f}

#print Function.iterate_fixed /-
theorem iterate_fixed {x} (h : f x = x) (n : ℕ) : (f^[n]) x = x :=
  (Nat.recOn n rfl) fun n ihn => by rw [iterate_succ_apply, h, ihn]
#align function.iterate_fixed Function.iterate_fixed
-/

#print Function.Injective.iterate /-
theorem Injective.iterate (Hinj : Injective f) (n : ℕ) : Injective (f^[n]) :=
  (Nat.recOn n injective_id) fun n ihn => ihn.comp Hinj
#align function.injective.iterate Function.Injective.iterate
-/

#print Function.Surjective.iterate /-
theorem Surjective.iterate (Hsurj : Surjective f) (n : ℕ) : Surjective (f^[n]) :=
  (Nat.recOn n surjective_id) fun n ihn => ihn.comp Hsurj
#align function.surjective.iterate Function.Surjective.iterate
-/

#print Function.Bijective.iterate /-
theorem Bijective.iterate (Hbij : Bijective f) (n : ℕ) : Bijective (f^[n]) :=
  ⟨Hbij.1.iterate n, Hbij.2.iterate n⟩
#align function.bijective.iterate Function.Bijective.iterate
-/

namespace Semiconj

#print Function.Semiconj.iterate_right /-
theorem iterate_right {f : α → β} {ga : α → α} {gb : β → β} (h : Semiconj f ga gb) (n : ℕ) :
    Semiconj f (ga^[n]) (gb^[n]) :=
  (Nat.recOn n id_right) fun n ihn => ihn.compRight h
#align function.semiconj.iterate_right Function.Semiconj.iterate_right
-/

#print Function.Semiconj.iterate_left /-
theorem iterate_left {g : ℕ → α → α} (H : ∀ n, Semiconj f (g n) (g <| n + 1)) (n k : ℕ) :
    Semiconj (f^[n]) (g k) (g <| n + k) :=
  by
  induction' n with n ihn generalizing k
  · rw [Nat.zero_add]
    exact id_left
  · rw [Nat.succ_eq_add_one, Nat.add_right_comm, Nat.add_assoc]
    exact (H k).compLeft (ihn (k + 1))
#align function.semiconj.iterate_left Function.Semiconj.iterate_left
-/

end Semiconj

namespace Commute

variable {g : α → α}

#print Function.Commute.iterate_right /-
theorem iterate_right (h : Commute f g) (n : ℕ) : Commute f (g^[n]) :=
  h.iterate_right n
#align function.commute.iterate_right Function.Commute.iterate_right
-/

#print Function.Commute.iterate_left /-
theorem iterate_left (h : Commute f g) (n : ℕ) : Commute (f^[n]) g :=
  (h.symm.iterate_right n).symm
#align function.commute.iterate_left Function.Commute.iterate_left
-/

#print Function.Commute.iterate_iterate /-
theorem iterate_iterate (h : Commute f g) (m n : ℕ) : Commute (f^[m]) (g^[n]) :=
  (h.iterate_left m).iterate_right n
#align function.commute.iterate_iterate Function.Commute.iterate_iterate
-/

#print Function.Commute.iterate_eq_of_map_eq /-
theorem iterate_eq_of_map_eq (h : Commute f g) (n : ℕ) {x} (hx : f x = g x) :
    (f^[n]) x = (g^[n]) x :=
  (Nat.recOn n rfl) fun n ihn => by
    simp only [iterate_succ_apply, hx, (h.iterate_left n).Eq, ihn, ((refl g).iterate_right n).Eq]
#align function.commute.iterate_eq_of_map_eq Function.Commute.iterate_eq_of_map_eq
-/

#print Function.Commute.comp_iterate /-
theorem comp_iterate (h : Commute f g) (n : ℕ) : (f ∘ g)^[n] = f^[n] ∘ g^[n] :=
  by
  induction' n with n ihn; · rfl
  funext x
  simp only [ihn, (h.iterate_right n).Eq, iterate_succ, comp_app]
#align function.commute.comp_iterate Function.Commute.comp_iterate
-/

variable (f)

#print Function.Commute.iterate_self /-
theorem iterate_self (n : ℕ) : Commute (f^[n]) f :=
  (refl f).iterate_left n
#align function.commute.iterate_self Function.Commute.iterate_self
-/

#print Function.Commute.self_iterate /-
theorem self_iterate (n : ℕ) : Commute f (f^[n]) :=
  (refl f).iterate_right n
#align function.commute.self_iterate Function.Commute.self_iterate
-/

#print Function.Commute.iterate_iterate_self /-
theorem iterate_iterate_self (m n : ℕ) : Commute (f^[m]) (f^[n]) :=
  (refl f).iterate_iterate m n
#align function.commute.iterate_iterate_self Function.Commute.iterate_iterate_self
-/

end Commute

#print Function.Semiconj₂.iterate /-
theorem Semiconj₂.iterate {f : α → α} {op : α → α → α} (hf : Semiconj₂ f op op) (n : ℕ) :
    Semiconj₂ (f^[n]) op op :=
  Nat.recOn n (Semiconj₂.id_left op) fun n ihn => ihn.comp hf
#align function.semiconj₂.iterate Function.Semiconj₂.iterate
-/

variable (f)

#print Function.iterate_succ' /-
theorem iterate_succ' (n : ℕ) : f^[n.succ] = f ∘ f^[n] := by
  rw [iterate_succ, (commute.self_iterate f n).comp_eq]
#align function.iterate_succ' Function.iterate_succ'
-/

#print Function.iterate_succ_apply' /-
theorem iterate_succ_apply' (n : ℕ) (x : α) : (f^[n.succ]) x = f ((f^[n]) x) := by
  rw [iterate_succ']
#align function.iterate_succ_apply' Function.iterate_succ_apply'
-/

#print Function.iterate_pred_comp_of_pos /-
theorem iterate_pred_comp_of_pos {n : ℕ} (hn : 0 < n) : f^[n.pred] ∘ f = f^[n] := by
  rw [← iterate_succ, Nat.succ_pred_eq_of_pos hn]
#align function.iterate_pred_comp_of_pos Function.iterate_pred_comp_of_pos
-/

#print Function.comp_iterate_pred_of_pos /-
theorem comp_iterate_pred_of_pos {n : ℕ} (hn : 0 < n) : f ∘ f^[n.pred] = f^[n] := by
  rw [← iterate_succ', Nat.succ_pred_eq_of_pos hn]
#align function.comp_iterate_pred_of_pos Function.comp_iterate_pred_of_pos
-/

#print Function.Iterate.rec /-
/-- A recursor for the iterate of a function. -/
def Iterate.rec (p : α → Sort _) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) (n : ℕ) :
    p ((f^[n]) a) :=
  Nat.rec ha
    (fun m => by
      rw [iterate_succ']
      exact h _)
    n
#align function.iterate.rec Function.Iterate.rec
-/

/- warning: function.iterate.rec_zero -> Function.Iterate.rec_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Sort.{u2}) {f : α -> α} (h : forall (a : α), (p a) -> (p (f a))) {a : α} (ha : p a), Eq.{u2} (p (Nat.iterate.{succ u1} α (fun (a : α) => f a) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a)) (Function.Iterate.rec.{u1, u2} α p (fun (a : α) => f a) h a ha (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) ha
but is expected to have type
  forall {α : Type.{u2}} (p : α -> Sort.{u1}) {f : α -> α} (h : forall (a : α), (p a) -> (p (f a))) {a : α} (ha : p a), Eq.{u1} (p (Nat.iterate.{succ u2} α (fun (a : α) => f a) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a)) (Function.Iterate.rec.{u2, u1} α p (fun (a : α) => f a) h a ha (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) ha
Case conversion may be inaccurate. Consider using '#align function.iterate.rec_zero Function.Iterate.rec_zeroₓ'. -/
theorem Iterate.rec_zero (p : α → Sort _) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) :
    Iterate.rec p h ha 0 = ha :=
  rfl
#align function.iterate.rec_zero Function.Iterate.rec_zero

variable {f}

#print Function.LeftInverse.iterate /-
theorem LeftInverse.iterate {g : α → α} (hg : LeftInverse g f) (n : ℕ) :
    LeftInverse (g^[n]) (f^[n]) :=
  (Nat.recOn n fun _ => rfl) fun n ihn =>
    by
    rw [iterate_succ', iterate_succ]
    exact ihn.comp hg
#align function.left_inverse.iterate Function.LeftInverse.iterate
-/

#print Function.RightInverse.iterate /-
theorem RightInverse.iterate {g : α → α} (hg : RightInverse g f) (n : ℕ) :
    RightInverse (g^[n]) (f^[n]) :=
  hg.iterate n
#align function.right_inverse.iterate Function.RightInverse.iterate
-/

#print Function.iterate_comm /-
theorem iterate_comm (f : α → α) (m n : ℕ) : f^[n]^[m] = f^[m]^[n] :=
  (iterate_mul _ _ _).symm.trans (Eq.trans (by rw [Nat.mul_comm]) (iterate_mul _ _ _))
#align function.iterate_comm Function.iterate_comm
-/

#print Function.iterate_commute /-
theorem iterate_commute (m n : ℕ) : Commute (fun f : α → α => f^[m]) fun f => f^[n] := fun f =>
  iterate_comm f m n
#align function.iterate_commute Function.iterate_commute
-/

end Function

namespace List

open Function

#print List.foldl_const /-
theorem foldl_const (f : α → α) (a : α) (l : List β) :
    l.foldl (fun b _ => f b) a = (f^[l.length]) a :=
  by
  induction' l with b l H generalizing a
  · rfl
  · rw [length_cons, foldl, iterate_succ_apply, H]
#align list.foldl_const List.foldl_const
-/

#print List.foldr_const /-
theorem foldr_const (f : β → β) (b : β) : ∀ l : List α, l.foldr (fun _ => f) b = (f^[l.length]) b
  | [] => rfl
  | a :: l => by rw [length_cons, foldr, foldr_const l, iterate_succ_apply']
#align list.foldr_const List.foldr_const
-/

end List

