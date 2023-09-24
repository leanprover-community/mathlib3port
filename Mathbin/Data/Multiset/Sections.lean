/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Data.Multiset.Bind

#align_import data.multiset.sections from "leanprover-community/mathlib"@"f2f413b9d4be3a02840d0663dace76e8fe3da053"

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

#print Multiset.card_sections /-
theorem card_sections {s : Multiset (Multiset α)} : card (Sections s) = prod (s.map card) :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }))
#align multiset.card_sections Multiset.card_sections
-/

#print Multiset.prod_map_sum /-
theorem prod_map_sum [CommSemiring α] {s : Multiset (Multiset α)} :
    prod (s.map sum) = sum ((Sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]
#align multiset.prod_map_sum Multiset.prod_map_sum
-/

end Sections

end Multiset

