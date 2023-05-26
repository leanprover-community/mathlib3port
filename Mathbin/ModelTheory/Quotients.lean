/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.quotients
! leanprover-community/mathlib commit a87d22575d946e1e156fc1edd1e1269600a8a282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Quotient
import Mathbin.ModelTheory.Semantics

/-!
# Quotients of First-Order Structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines prestructures and quotients of first-order structures.

## Main Definitions
* If `s` is a setoid (equivalence relation) on `M`, a `first_order.language.prestructure s` is the
data for a first-order structure on `M` that will still be a structure when modded out by `s`.
* The structure `first_order.language.quotient_structure s` is the resulting structure on
`quotient s`.

-/


namespace FirstOrder

namespace Language

variable (L : Language) {M : Type _}

open FirstOrder

open Structure

#print FirstOrder.Language.Prestructure /-
/-- A prestructure is a first-order structure with a `setoid` equivalence relation on it,
  such that quotienting by that equivalence relation is still a structure. -/
class Prestructure (s : Setoid M) where
  toStructure : L.Structure M
  fun_equiv : ∀ {n} {f : L.Functions n} (x y : Fin n → M), x ≈ y → funMap f x ≈ funMap f y
  rel_equiv : ∀ {n} {r : L.Relations n} (x y : Fin n → M) (h : x ≈ y), RelMap r x = RelMap r y
#align first_order.language.prestructure FirstOrder.Language.Prestructure
-/

variable {L} {s : Setoid M} [ps : L.Prestructure s]

#print FirstOrder.Language.quotientStructure /-
instance quotientStructure : L.Structure (Quotient s)
    where
  funMap n f x :=
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice x)
  rel_map n r x :=
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice x)
#align first_order.language.quotient_structure FirstOrder.Language.quotientStructure
-/

variable (s)

include s

/- warning: first_order.language.fun_map_quotient_mk -> FirstOrder.Language.funMap_quotient_mk' is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [s : Setoid.{succ u3} M] [ps : FirstOrder.Language.Prestructure.{u1, u2, u3} L M s] {n : Nat} (f : FirstOrder.Language.Functions.{u1, u2} L n) (x : (Fin n) -> M), Eq.{succ u3} (Quotient.{succ u3} M s) (FirstOrder.Language.Structure.funMap.{u1, u2, u3} L (Quotient.{succ u3} M s) (FirstOrder.Language.quotientStructure.{u1, u2, u3} L M s ps) n f (fun (i : Fin n) => Quotient.mk'.{succ u3} M s (x i))) (Quotient.mk'.{succ u3} M s (FirstOrder.Language.Structure.funMap.{u1, u2, u3} L M (FirstOrder.Language.Prestructure.toStructure.{u1, u2, u3} L M s ps) n f x))
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u2}} {M : Type.{u1}} (s : Setoid.{succ u1} M) [ps : FirstOrder.Language.Prestructure.{u3, u2, u1} L M s] {n : Nat} (f : FirstOrder.Language.Functions.{u3, u2} L n) (x : (Fin n) -> M), Eq.{succ u1} (Quotient.{succ u1} M s) (FirstOrder.Language.Structure.funMap.{u3, u2, u1} L (Quotient.{succ u1} M s) (FirstOrder.Language.quotientStructure.{u3, u2, u1} L M s ps) n f (fun (i : Fin n) => Quotient.mk.{succ u1} M s (x i))) (Quotient.mk.{succ u1} M s (FirstOrder.Language.Structure.funMap.{u3, u2, u1} L M (FirstOrder.Language.Prestructure.toStructure.{u3, u2, u1} L M s ps) n f x))
Case conversion may be inaccurate. Consider using '#align first_order.language.fun_map_quotient_mk FirstOrder.Language.funMap_quotient_mk'ₓ'. -/
theorem funMap_quotient_mk' {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    (funMap f fun i => ⟦x i⟧) = ⟦@funMap _ _ ps.toStructure _ f x⟧ :=
  by
  change
    Quotient.map (@fun_map L M ps.to_structure n f) prestructure.fun_equiv (Quotient.finChoice _) =
      _
  rw [Quotient.finChoice_eq, Quotient.map_mk]
#align first_order.language.fun_map_quotient_mk FirstOrder.Language.funMap_quotient_mk'

/- warning: first_order.language.rel_map_quotient_mk -> FirstOrder.Language.relMap_quotient_mk' is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [s : Setoid.{succ u3} M] [ps : FirstOrder.Language.Prestructure.{u1, u2, u3} L M s] {n : Nat} (r : FirstOrder.Language.Relations.{u1, u2} L n) (x : (Fin n) -> M), Iff (FirstOrder.Language.Structure.RelMap.{u1, u2, u3} L (Quotient.{succ u3} M s) (FirstOrder.Language.quotientStructure.{u1, u2, u3} L M s ps) n r (fun (i : Fin n) => Quotient.mk'.{succ u3} M s (x i))) (FirstOrder.Language.Structure.RelMap.{u1, u2, u3} L M (FirstOrder.Language.Prestructure.toStructure.{u1, u2, u3} L M s ps) n r x)
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u2}} {M : Type.{u1}} (s : Setoid.{succ u1} M) [ps : FirstOrder.Language.Prestructure.{u3, u2, u1} L M s] {n : Nat} (r : FirstOrder.Language.Relations.{u3, u2} L n) (x : (Fin n) -> M), Iff (FirstOrder.Language.Structure.RelMap.{u3, u2, u1} L (Quotient.{succ u1} M s) (FirstOrder.Language.quotientStructure.{u3, u2, u1} L M s ps) n r (fun (i : Fin n) => Quotient.mk.{succ u1} M s (x i))) (FirstOrder.Language.Structure.RelMap.{u3, u2, u1} L M (FirstOrder.Language.Prestructure.toStructure.{u3, u2, u1} L M s ps) n r x)
Case conversion may be inaccurate. Consider using '#align first_order.language.rel_map_quotient_mk FirstOrder.Language.relMap_quotient_mk'ₓ'. -/
theorem relMap_quotient_mk' {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    (RelMap r fun i => ⟦x i⟧) ↔ @RelMap _ _ ps.toStructure _ r x :=
  by
  change
    Quotient.lift (@rel_map L M ps.to_structure n r) prestructure.rel_equiv (Quotient.finChoice _) ↔
      _
  rw [Quotient.finChoice_eq, Quotient.lift_mk]
#align first_order.language.rel_map_quotient_mk FirstOrder.Language.relMap_quotient_mk'

/- warning: first_order.language.term.realize_quotient_mk -> FirstOrder.Language.Term.realize_quotient_mk' is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [s : Setoid.{succ u3} M] [ps : FirstOrder.Language.Prestructure.{u1, u2, u3} L M s] {β : Type.{u4}} (t : FirstOrder.Language.Term.{u1, u2, u4} L β) (x : β -> M), Eq.{succ u3} (Quotient.{succ u3} M s) (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L (Quotient.{succ u3} M s) (FirstOrder.Language.quotientStructure.{u1, u2, u3} L M s ps) β (fun (i : β) => Quotient.mk'.{succ u3} M s (x i)) t) (Quotient.mk'.{succ u3} M s (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M (FirstOrder.Language.Prestructure.toStructure.{u1, u2, u3} L M s ps) β x t))
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u2}} {M : Type.{u1}} (s : Setoid.{succ u1} M) [ps : FirstOrder.Language.Prestructure.{u3, u2, u1} L M s] {β : Type.{u4}} (t : FirstOrder.Language.Term.{u3, u2, u4} L β) (x : β -> M), Eq.{succ u1} (Quotient.{succ u1} M s) (FirstOrder.Language.Term.realize.{u3, u2, u1, u4} L (Quotient.{succ u1} M s) (FirstOrder.Language.quotientStructure.{u3, u2, u1} L M s ps) β (fun (i : β) => Quotient.mk.{succ u1} M s (x i)) t) (Quotient.mk.{succ u1} M s (FirstOrder.Language.Term.realize.{u3, u2, u1, u4} L M (FirstOrder.Language.Prestructure.toStructure.{u3, u2, u1} L M s ps) β x t))
Case conversion may be inaccurate. Consider using '#align first_order.language.term.realize_quotient_mk FirstOrder.Language.Term.realize_quotient_mk'ₓ'. -/
theorem Term.realize_quotient_mk' {β : Type _} (t : L.term β) (x : β → M) :
    (t.realize fun i => ⟦x i⟧) = ⟦@Term.realize _ _ ps.toStructure _ x t⟧ :=
  by
  induction' t with _ _ _ _ ih
  · rfl
  · simp only [ih, fun_map_quotient_mk, term.realize]
#align first_order.language.term.realize_quotient_mk FirstOrder.Language.Term.realize_quotient_mk'

end Language

end FirstOrder

