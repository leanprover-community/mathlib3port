/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.quotient
! leanprover-community/mathlib commit a87d22575d946e1e156fc1edd1e1269600a8a282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic

/-!
# Quotients of families indexed by a finite type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides `quotient.fin_choice`, a mechanism to go from a finite family of quotients
to a quotient of finite families.

## Main definitions

* `quotient.fin_choice`

-/


#print Quotient.finChoiceAux /-
/-- An auxiliary function for `quotient.fin_choice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def Quotient.finChoiceAux {ι : Type _} [DecidableEq ι] {α : ι → Type _} [S : ∀ i, Setoid (α i)] :
    ∀ l : List ι, (∀ i ∈ l, Quotient (S i)) → @Quotient (∀ i ∈ l, α i) (by infer_instance)
  | [], f => ⟦fun i => False.elim⟧
  | i :: l, f =>
    by
    refine'
      Quotient.liftOn₂ (f i (List.mem_cons_self _ _))
        (Quotient.finChoiceAux l fun j h => f j (List.mem_cons_of_mem _ h)) _ _
    exact fun a l =>
      ⟦fun j h => if e : j = i then by rw [e] <;> exact a else l _ (h.resolve_left e)⟧
    refine' fun a₁ l₁ a₂ l₂ h₁ h₂ => Quotient.sound fun j h => _
    by_cases e : j = i <;> simp [e]
    · subst j
      exact h₁
    · exact h₂ _ _
#align quotient.fin_choice_aux Quotient.finChoiceAux
-/

/- warning: quotient.fin_choice_aux_eq -> Quotient.finChoiceAux_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} ι] {α : ι -> Type.{u2}} [S : forall (i : ι), Setoid.{succ u2} (α i)] (l : List.{u1} ι) (f : forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)), Eq.{max (succ u1) (succ u2)} (Quotient.{max (succ u1) (succ u2)} (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)) (fun (i : ι) => piSetoid.{0, succ u2} (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) (fun (H : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => α i) (fun (i_1 : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => S i)))) (Quotient.finChoiceAux.{u1, u2} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => α i) (fun (i : ι) => S i) l (fun (i : ι) (h : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => Quotient.mk'.{succ u2} (α i) (S i) (f i h))) (Quotient.mk'.{max (succ u1) (succ u2)} (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)) (fun (i : ι) => piSetoid.{0, succ u2} (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) (fun (H : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => α i) (fun (i_1 : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => S i))) f)
but is expected to have type
  forall {ι : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} ι] {α : ι -> Type.{u1}} [S : forall (i : ι), Setoid.{succ u1} (α i)] (l : List.{u2} ι) (f : forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)), Eq.{max (succ u2) (succ u1)} (Quotient.{max (succ u2) (succ u1)} (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i))) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)) (fun (i : ι) => piSetoid.{0, succ u1} (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) (fun (a._@.Mathlib.Data.Fintype.Quotient._hyg.57 : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => α i) (fun (i_1 : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => (fun (i : ι) => S i) i))))) (Quotient.finChoiceAux.{u2, u1} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => α i) (fun (i : ι) => S i) l (fun (i : ι) (h : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => Quotient.mk.{succ u1} (α i) (S i) (f i h))) (Quotient.mk.{max (succ u2) (succ u1)} (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i))) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)) (fun (i : ι) => piSetoid.{0, succ u1} (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) (fun (a._@.Mathlib.Data.Fintype.Quotient._hyg.57 : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => α i) (fun (i_1 : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => (fun (i : ι) => S i) i)))) f)
Case conversion may be inaccurate. Consider using '#align quotient.fin_choice_aux_eq Quotient.finChoiceAux_eqₓ'. -/
theorem Quotient.finChoiceAux_eq {ι : Type _} [DecidableEq ι] {α : ι → Type _}
    [S : ∀ i, Setoid (α i)] :
    ∀ (l : List ι) (f : ∀ i ∈ l, α i), (Quotient.finChoiceAux l fun i h => ⟦f i h⟧) = ⟦f⟧
  | [], f => Quotient.sound fun i h => h.elim
  | i :: l, f => by
    simp [Quotient.finChoiceAux, Quotient.finChoiceAux_eq l]
    refine' Quotient.sound fun j h => _
    by_cases e : j = i <;> simp [e]
    subst j; rfl
#align quotient.fin_choice_aux_eq Quotient.finChoiceAux_eq

#print Quotient.finChoice /-
/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def Quotient.finChoice {ι : Type _} [DecidableEq ι] [Fintype ι] {α : ι → Type _}
    [S : ∀ i, Setoid (α i)] (f : ∀ i, Quotient (S i)) : @Quotient (∀ i, α i) (by infer_instance) :=
  Quotient.liftOn
    (@Quotient.recOn _ _ (fun l : Multiset ι => @Quotient (∀ i ∈ l, α i) (by infer_instance))
      Finset.univ.1 (fun l => Quotient.finChoiceAux l fun i _ => f i) fun a b h =>
      by
      have := fun a => Quotient.finChoiceAux_eq a fun i h => Quotient.out (f i)
      simp [Quotient.out_eq] at this
      simp [this]
      let g := fun a : Multiset ι => ⟦fun (i : ι) (h : i ∈ a) => Quotient.out (f i)⟧
      refine' eq_of_hEq ((eq_rec_hEq _ _).trans (_ : HEq (g a) (g b)))
      congr 1; exact Quotient.sound h)
    (fun f => ⟦fun i => f i (Finset.mem_univ _)⟧) fun a b h => Quotient.sound fun i => h _ _
#align quotient.fin_choice Quotient.finChoice
-/

/- warning: quotient.fin_choice_eq -> Quotient.finChoice_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] {α : ι -> Type.{u2}} [_inst_3 : forall (i : ι), Setoid.{succ u2} (α i)] (f : forall (i : ι), α i), Eq.{max (succ u1) (succ u2)} (Quotient.{max (succ u1) (succ u2)} (forall (i : ι), α i) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i))) (Quotient.finChoice.{u1, u2} ι (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => Quotient.mk'.{succ u2} (α i) (_inst_3 i) (f i))) (Quotient.mk'.{max (succ u1) (succ u2)} (forall (i : ι), α i) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i)) f)
but is expected to have type
  forall {ι : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] {α : ι -> Type.{u1}} [_inst_3 : forall (i : ι), Setoid.{succ u1} (α i)] (f : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Quotient.{max (succ u2) (succ u1)} (forall (i : ι), α i) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), α i)) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i)))) (Quotient.finChoice.{u2, u1} ι (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => Quotient.mk.{succ u1} (α i) (_inst_3 i) (f i))) (Quotient.mk.{max (succ u2) (succ u1)} (forall (i : ι), α i) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), α i)) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i))) f)
Case conversion may be inaccurate. Consider using '#align quotient.fin_choice_eq Quotient.finChoice_eqₓ'. -/
theorem Quotient.finChoice_eq {ι : Type _} [DecidableEq ι] [Fintype ι] {α : ι → Type _}
    [∀ i, Setoid (α i)] (f : ∀ i, α i) : (Quotient.finChoice fun i => ⟦f i⟧) = ⟦f⟧ :=
  by
  let q
  swap
  change Quotient.liftOn q _ _ = _
  have : q = ⟦fun i h => f i⟧ := by
    dsimp only [q]
    exact Quotient.inductionOn (@Finset.univ ι _).1 fun l => Quotient.finChoiceAux_eq _ _
  simp [this]
  exact Setoid.refl _
#align quotient.fin_choice_eq Quotient.finChoice_eq

