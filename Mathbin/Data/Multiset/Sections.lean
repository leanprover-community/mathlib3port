/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.multiset.sections
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Bind

/-!
# Sections of a multiset

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Multiset

variable {α : Type _}

section Sections

#print Multiset.Sections /-
/-- The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is an member of the corresponding multiset.
-/
def Sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ s pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]
#align multiset.sections Multiset.Sections
-/

#print Multiset.sections_zero /-
@[simp]
theorem sections_zero : Sections (0 : Multiset (Multiset α)) = {0} :=
  rfl
#align multiset.sections_zero Multiset.sections_zero
-/

#print Multiset.sections_cons /-
@[simp]
theorem sections_cons (s : Multiset (Multiset α)) (m : Multiset α) :
    Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.cons a) :=
  recOn_cons m s
#align multiset.sections_cons Multiset.sections_cons
-/

#print Multiset.coe_sections /-
theorem coe_sections :
    ∀ l : List (List α),
      Sections (l.map fun l : List α => (l : Multiset α) : Multiset (Multiset α)) =
        (l.sections.map fun l : List α => (l : Multiset α) : Multiset (Multiset α))
  | [] => rfl
  | a :: l => by
    simp
    rw [← cons_coe, sections_cons, bind_map_comm, coe_sections l]
    simp [List.sections, (· ∘ ·), List.bind]
#align multiset.coe_sections Multiset.coe_sections
-/

#print Multiset.sections_add /-
@[simp]
theorem sections_add (s t : Multiset (Multiset α)) :
    Sections (s + t) = (Sections s).bind fun m => (Sections t).map ((· + ·) m) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, bind_assoc, map_bind, bind_map, -add_comm]
#align multiset.sections_add Multiset.sections_add
-/

#print Multiset.mem_sections /-
theorem mem_sections {s : Multiset (Multiset α)} :
    ∀ {a}, a ∈ Sections s ↔ s.Rel (fun s a => a ∈ s) a :=
  Multiset.induction_on s (by simp) fun a s ih a' => by
    simp [ih, rel_cons_left, -exists_and_left, exists_and_distrib_left.symm, eq_comm]
#align multiset.mem_sections Multiset.mem_sections
-/

/- warning: multiset.card_sections -> Multiset.card_sections is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} (Multiset.{u1} α)}, Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.orderedCancelAddCommMonoid.{u1} (Multiset.{u1} α))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.orderedCancelAddCommMonoid.{u1} (Multiset.{u1} α))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} (Multiset.{u1} α)) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.orderedCancelAddCommMonoid.{u1} (Multiset.{u1} α))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} (Multiset.{u1} α)) (Multiset.Sections.{u1} α s)) (Multiset.prod.{0} Nat Nat.commMonoid (Multiset.map.{u1, 0} (Multiset.{u1} α) Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} (Multiset.{u1} α)}, Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Multiset.{u1} α)) => Nat) (Multiset.Sections.{u1} α s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Multiset.{u1} α))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Multiset.{u1} α)) (fun (_x : Multiset.{u1} (Multiset.{u1} α)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (Multiset.{u1} α)) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Multiset.{u1} α))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Multiset.{u1} α)) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Multiset.{u1} α)))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Multiset.{u1} α))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (Multiset.{u1} α)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Multiset.{u1} α))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (Multiset.{u1} α))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} (Multiset.{u1} α)) (Multiset.Sections.{u1} α s)) (Multiset.prod.{0} Nat Nat.commMonoid (Multiset.map.{u1, 0} (Multiset.{u1} α) Nat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_sections Multiset.card_sectionsₓ'. -/
theorem card_sections {s : Multiset (Multiset α)} : card (Sections s) = prod (s.map card) :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }))
#align multiset.card_sections Multiset.card_sections

#print Multiset.prod_map_sum /-
theorem prod_map_sum [CommSemiring α] {s : Multiset (Multiset α)} :
    prod (s.map sum) = sum ((Sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]
#align multiset.prod_map_sum Multiset.prod_map_sum
-/

end Sections

end Multiset

