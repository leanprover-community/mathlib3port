/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Simon Hudon, Kenny Lau

! This file was ported from Lean 3 source module data.opposite
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Defs

/-!
# Opposites

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a type synonym `opposite α := α`, denoted by `αᵒᵖ` and two synonyms for the
identity map, `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`. If `α` is a category, then `αᵒᵖ` is the opposite
category, with all arrows reversed.
-/


universe v u

-- morphism levels before object levels. See note [category_theory universes].
variable (α : Sort u)

/- warning: opposite -> Opposite is a dubious translation:
lean 3 declaration is
  Sort.{u1} -> Sort.{u1}
but is expected to have type
  Sort.{u1} -> Sort.{max 1 u1}
Case conversion may be inaccurate. Consider using '#align opposite Oppositeₓ'. -/
/-- The type of objects of the opposite of `α`; used to define the opposite category.

  In order to avoid confusion between `α` and its opposite type, we
  set up the type of objects `opposite α` using the following pattern,
  which will be repeated later for the morphisms.

  1. Define `opposite α := α`.
  2. Define the isomorphisms `op : α → opposite α`, `unop : opposite α → α`.
  3. Make the definition `opposite` irreducible.

  This has the following consequences.

  * `opposite α` and `α` are distinct types in the elaborator, so you
    must use `op` and `unop` explicitly to convert between them.
  * Both `unop (op X) = X` and `op (unop X) = X` are definitional
    equalities. Notably, every object of the opposite category is
    definitionally of the form `op X`, which greatly simplifies the
    definition of the structure of the opposite category, for example.

  (If Lean supported definitional eta equality for records, we could
  achieve the same goals using a structure with one field.)
-/
def Opposite : Sort u :=
  α
#align opposite Opposite

-- mathport name: «expr ᵒᵖ»
notation:max -- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `presheaf Cᵒᵖ` parses as `presheaf (Cᵒᵖ)` and not `(presheaf C)ᵒᵖ`.
α "ᵒᵖ" => Opposite α

namespace Opposite

variable {α}

#print Opposite.op /-
/-- The canonical map `α → αᵒᵖ`. -/
@[pp_nodot]
def op : α → αᵒᵖ :=
  id
#align opposite.op Opposite.op
-/

#print Opposite.unop /-
/-- The canonical map `αᵒᵖ → α`. -/
@[pp_nodot]
def unop : αᵒᵖ → α :=
  id
#align opposite.unop Opposite.unop
-/

/- warning: opposite.op_injective -> Opposite.op_injective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Function.Injective.{u1, u1} α (Opposite.{u1} α) (Opposite.op.{u1} α)
but is expected to have type
  forall {α : Sort.{u1}}, Function.Injective.{u1, max 1 u1} α (Opposite.{u1} α) (Opposite.op.{u1} α)
Case conversion may be inaccurate. Consider using '#align opposite.op_injective Opposite.op_injectiveₓ'. -/
theorem op_injective : Function.Injective (op : α → αᵒᵖ) := fun _ _ => id
#align opposite.op_injective Opposite.op_injective

/- warning: opposite.unop_injective -> Opposite.unop_injective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Function.Injective.{u1, u1} (Opposite.{u1} α) α (Opposite.unop.{u1} α)
but is expected to have type
  forall {α : Sort.{u1}}, Function.Injective.{max 1 u1, u1} (Opposite.{u1} α) α (Opposite.unop.{u1} α)
Case conversion may be inaccurate. Consider using '#align opposite.unop_injective Opposite.unop_injectiveₓ'. -/
theorem unop_injective : Function.Injective (unop : αᵒᵖ → α) := fun _ _ => id
#align opposite.unop_injective Opposite.unop_injective

/- warning: opposite.op_unop -> Opposite.op_unop is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} (x : Opposite.{u1} α), Eq.{u1} (Opposite.{u1} α) (Opposite.op.{u1} α (Opposite.unop.{u1} α x)) x
but is expected to have type
  forall {α : Sort.{u1}} (x : Opposite.{u1} α), Eq.{max 1 u1} (Opposite.{u1} α) (Opposite.op.{u1} α (Opposite.unop.{u1} α x)) x
Case conversion may be inaccurate. Consider using '#align opposite.op_unop Opposite.op_unopₓ'. -/
@[simp]
theorem op_unop (x : αᵒᵖ) : op (unop x) = x :=
  rfl
#align opposite.op_unop Opposite.op_unop

#print Opposite.unop_op /-
@[simp]
theorem unop_op (x : α) : unop (op x) = x :=
  rfl
#align opposite.unop_op Opposite.unop_op
-/

/- warning: opposite.op_inj_iff -> Opposite.op_inj_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} (x : α) (y : α), Iff (Eq.{u1} (Opposite.{u1} α) (Opposite.op.{u1} α x) (Opposite.op.{u1} α y)) (Eq.{u1} α x y)
but is expected to have type
  forall {α : Sort.{u1}} (x : α) (y : α), Iff (Eq.{max 1 u1} (Opposite.{u1} α) (Opposite.op.{u1} α x) (Opposite.op.{u1} α y)) (Eq.{u1} α x y)
Case conversion may be inaccurate. Consider using '#align opposite.op_inj_iff Opposite.op_inj_iffₓ'. -/
-- We could prove these by `iff.rfl`, but that would make these eligible for `dsimp`. That would be
-- a bad idea because `opposite` is irreducible.
@[simp]
theorem op_inj_iff (x y : α) : op x = op y ↔ x = y :=
  op_injective.eq_iff
#align opposite.op_inj_iff Opposite.op_inj_iff

/- warning: opposite.unop_inj_iff -> Opposite.unop_inj_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} (x : Opposite.{u1} α) (y : Opposite.{u1} α), Iff (Eq.{u1} α (Opposite.unop.{u1} α x) (Opposite.unop.{u1} α y)) (Eq.{u1} (Opposite.{u1} α) x y)
but is expected to have type
  forall {α : Sort.{u1}} (x : Opposite.{u1} α) (y : Opposite.{u1} α), Iff (Eq.{u1} α (Opposite.unop.{u1} α x) (Opposite.unop.{u1} α y)) (Eq.{max 1 u1} (Opposite.{u1} α) x y)
Case conversion may be inaccurate. Consider using '#align opposite.unop_inj_iff Opposite.unop_inj_iffₓ'. -/
@[simp]
theorem unop_inj_iff (x y : αᵒᵖ) : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff
#align opposite.unop_inj_iff Opposite.unop_inj_iff

/- warning: opposite.equiv_to_opposite -> Opposite.equivToOpposite is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Equiv.{u1, u1} α (Opposite.{u1} α)
but is expected to have type
  forall {α : Sort.{u1}}, Equiv.{u1, max 1 u1} α (Opposite.{u1} α)
Case conversion may be inaccurate. Consider using '#align opposite.equiv_to_opposite Opposite.equivToOppositeₓ'. -/
/-- The type-level equivalence between a type and its opposite. -/
def equivToOpposite : α ≃ αᵒᵖ where
  toFun := op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop
#align opposite.equiv_to_opposite Opposite.equivToOpposite

/- warning: opposite.equiv_to_opposite_coe -> Opposite.equivToOpposite_coe is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Eq.{u1} ((fun (_x : Equiv.{u1, u1} α (Opposite.{u1} α)) => α -> (Opposite.{u1} α)) (Opposite.equivToOpposite.{u1} α)) (coeFn.{max 1 u1, u1} (Equiv.{u1, u1} α (Opposite.{u1} α)) (fun (_x : Equiv.{u1, u1} α (Opposite.{u1} α)) => α -> (Opposite.{u1} α)) (Equiv.hasCoeToFun.{u1, u1} α (Opposite.{u1} α)) (Opposite.equivToOpposite.{u1} α)) (Opposite.op.{u1} α)
but is expected to have type
  forall {α : Sort.{u1}}, Eq.{max 1 u1} (forall (a : α), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Opposite.{u1} α) a) (FunLike.coe.{max 1 u1, u1, max 1 u1} (Equiv.{u1, max 1 u1} α (Opposite.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Opposite.{u1} α) _x) (Equiv.instFunLikeEquiv.{u1, max 1 u1} α (Opposite.{u1} α)) (Opposite.equivToOpposite.{u1} α)) (Opposite.op.{u1} α)
Case conversion may be inaccurate. Consider using '#align opposite.equiv_to_opposite_coe Opposite.equivToOpposite_coeₓ'. -/
@[simp]
theorem equivToOpposite_coe : (equivToOpposite : α → αᵒᵖ) = op :=
  rfl
#align opposite.equiv_to_opposite_coe Opposite.equivToOpposite_coe

/- warning: opposite.equiv_to_opposite_symm_coe -> Opposite.equivToOpposite_symm_coe is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Eq.{u1} ((fun (_x : Equiv.{u1, u1} (Opposite.{u1} α) α) => (Opposite.{u1} α) -> α) (Equiv.symm.{u1, u1} α (Opposite.{u1} α) (Opposite.equivToOpposite.{u1} α))) (coeFn.{max 1 u1, u1} (Equiv.{u1, u1} (Opposite.{u1} α) α) (fun (_x : Equiv.{u1, u1} (Opposite.{u1} α) α) => (Opposite.{u1} α) -> α) (Equiv.hasCoeToFun.{u1, u1} (Opposite.{u1} α) α) (Equiv.symm.{u1, u1} α (Opposite.{u1} α) (Opposite.equivToOpposite.{u1} α))) (Opposite.unop.{u1} α)
but is expected to have type
  forall {α : Sort.{u1}}, Eq.{imax (max 1 u1) u1} (forall (a : Opposite.{u1} α), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Opposite.{u1} α) => α) a) (FunLike.coe.{max 1 u1, max 1 u1, u1} (Equiv.{max 1 u1, u1} (Opposite.{u1} α) α) (Opposite.{u1} α) (fun (_x : Opposite.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Opposite.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{max 1 u1, u1} (Opposite.{u1} α) α) (Equiv.symm.{u1, max 1 u1} α (Opposite.{u1} α) (Opposite.equivToOpposite.{u1} α))) (Opposite.unop.{u1} α)
Case conversion may be inaccurate. Consider using '#align opposite.equiv_to_opposite_symm_coe Opposite.equivToOpposite_symm_coeₓ'. -/
@[simp]
theorem equivToOpposite_symm_coe : (equivToOpposite.symm : αᵒᵖ → α) = unop :=
  rfl
#align opposite.equiv_to_opposite_symm_coe Opposite.equivToOpposite_symm_coe

/- warning: opposite.op_eq_iff_eq_unop -> Opposite.op_eq_iff_eq_unop is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {x : α} {y : Opposite.{u1} α}, Iff (Eq.{u1} (Opposite.{u1} α) (Opposite.op.{u1} α x) y) (Eq.{u1} α x (Opposite.unop.{u1} α y))
but is expected to have type
  forall {α : Sort.{u1}} {x : α} {y : Opposite.{u1} α}, Iff (Eq.{max 1 u1} (Opposite.{u1} α) (Opposite.op.{u1} α x) y) (Eq.{u1} α x (Opposite.unop.{u1} α y))
Case conversion may be inaccurate. Consider using '#align opposite.op_eq_iff_eq_unop Opposite.op_eq_iff_eq_unopₓ'. -/
theorem op_eq_iff_eq_unop {x : α} {y} : op x = y ↔ x = unop y :=
  equivToOpposite.apply_eq_iff_eq_symm_apply
#align opposite.op_eq_iff_eq_unop Opposite.op_eq_iff_eq_unop

/- warning: opposite.unop_eq_iff_eq_op -> Opposite.unop_eq_iff_eq_op is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {x : Opposite.{u1} α} {y : α}, Iff (Eq.{u1} α (Opposite.unop.{u1} α x) y) (Eq.{u1} (Opposite.{u1} α) x (Opposite.op.{u1} α y))
but is expected to have type
  forall {α : Sort.{u1}} {x : Opposite.{u1} α} {y : α}, Iff (Eq.{u1} α (Opposite.unop.{u1} α x) y) (Eq.{max 1 u1} (Opposite.{u1} α) x (Opposite.op.{u1} α y))
Case conversion may be inaccurate. Consider using '#align opposite.unop_eq_iff_eq_op Opposite.unop_eq_iff_eq_opₓ'. -/
theorem unop_eq_iff_eq_op {x} {y : α} : unop x = y ↔ x = op y :=
  equivToOpposite.symm.apply_eq_iff_eq_symm_apply
#align opposite.unop_eq_iff_eq_op Opposite.unop_eq_iff_eq_op

instance [Inhabited α] : Inhabited αᵒᵖ :=
  ⟨op default⟩

#print Opposite.rec' /-
/-- A recursor for `opposite`. Use as `induction x using opposite.rec`. -/
@[simp]
protected def rec' {F : ∀ X : αᵒᵖ, Sort v} (h : ∀ X, F (op X)) : ∀ X, F X := fun X => h (unop X)
#align opposite.rec Opposite.rec'
-/

end Opposite

namespace Tactic

open Opposite

namespace OpInduction

/-- Test if `e : expr` is of type `opposite α` for some `α`. -/
unsafe def is_opposite (e : expr) : tactic Bool := do
  let t ← infer_type e
  let q(Opposite _) ← whnf t |
    return false
  return tt
#align tactic.op_induction.is_opposite tactic.op_induction.is_opposite

/-- Find the first hypothesis of type `opposite _`. Fail if no such hypothesis exist in the local
context. -/
unsafe def find_opposite_hyp : tactic Name := do
  let lc ← local_context
  let h :: _ ← lc.filterM <| is_opposite |
    fail "No hypotheses of the form Xᵒᵖ"
  return h
#align tactic.op_induction.find_opposite_hyp tactic.op_induction.find_opposite_hyp

end OpInduction

open OpInduction

/-- A version of `induction x using opposite.rec` which finds the appropriate hypothesis
automatically, for use with `local attribute [tidy] op_induction'`. This is necessary because
`induction x` is not able to deduce that `opposite.rec` should be used. -/
unsafe def op_induction' : tactic Unit := do
  let h ← find_opposite_hyp
  let h' ← tactic.get_local h
  tactic.induction' h' [] `opposite.rec
#align tactic.op_induction' tactic.op_induction'

end Tactic

