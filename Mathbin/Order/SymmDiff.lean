/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen, Yaël Dillies

! This file was ported from Lean 3 source module order.symm_diff
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.BooleanAlgebra
import Mathbin.Logic.Equiv.Basic

/-!
# Symmetric difference and bi-implication

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the symmetric difference and bi-implication operators in (co-)Heyting algebras.

## Examples

Some examples are
* The symmetric difference of two sets is the set of elements that are in either but not both.
* The symmetric difference on propositions is `xor`.
* The symmetric difference on `bool` is `bxor`.
* The equivalence of propositions. Two propositions are equivalent if they imply each other.
* The symmetric difference translates to addition when considering a Boolean algebra as a Boolean
  ring.

## Main declarations

* `symm_diff`: The symmetric difference operator, defined as `(a \ b) ⊔ (b \ a)`
* `bihimp`: The bi-implication operator, defined as `(b ⇨ a) ⊓ (a ⇨ b)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symm_diff_comm`: commutative, and
* `symm_diff_assoc`: associative.

## Notations

* `a ∆ b`: `symm_diff a b`
* `a ⇔ b`: `bihimp a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags

boolean ring, generalized boolean algebra, boolean algebra, symmetric difference, bi-implication,
Heyting
-/


open Function OrderDual

variable {ι α β : Type _} {π : ι → Type _}

#print symmDiff /-
/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symmDiff [HasSup α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a
#align symm_diff symmDiff
-/

#print bihimp /-
/-- The Heyting bi-implication is `(b ⇨ a) ⊓ (a ⇨ b)`. This generalizes equivalence of
propositions. -/
def bihimp [HasInf α] [HImp α] (a b : α) : α :=
  (b ⇨ a) ⊓ (a ⇨ b)
#align bihimp bihimp
-/

-- mathport name: «expr ∆ »
infixl:100
  " ∆ " =>/- This notation might conflict with the Laplacian once we have it. Feel free to put it in locale
  `order` or `symm_diff` if that happens. -/
  symmDiff

-- mathport name: «expr ⇔ »
infixl:100 " ⇔ " => bihimp

#print symmDiff_def /-
theorem symmDiff_def [HasSup α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔ b \ a :=
  rfl
#align symm_diff_def symmDiff_def
-/

#print bihimp_def /-
theorem bihimp_def [HasInf α] [HImp α] (a b : α) : a ⇔ b = (b ⇨ a) ⊓ (a ⇨ b) :=
  rfl
#align bihimp_def bihimp_def
-/

/- warning: symm_diff_eq_xor -> symmDiff_eq_Xor' is a dubious translation:
lean 3 declaration is
  forall (p : Prop) (q : Prop), Eq.{1} Prop (symmDiff.{0} Prop (SemilatticeSup.toHasSup.{0} Prop (Lattice.toSemilatticeSup.{0} Prop (GeneralizedCoheytingAlgebra.toLattice.{0} Prop (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{0} Prop (BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} Prop Prop.booleanAlgebra))))) (BooleanAlgebra.toHasSdiff.{0} Prop Prop.booleanAlgebra) p q) (Xor' p q)
but is expected to have type
  forall (p : Prop) (q : Prop), Eq.{1} Prop (symmDiff.{0} Prop (SemilatticeSup.toHasSup.{0} Prop (Lattice.toSemilatticeSup.{0} Prop (GeneralizedCoheytingAlgebra.toLattice.{0} Prop (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} Prop (BiheytingAlgebra.toCoheytingAlgebra.{0} Prop (BooleanAlgebra.toBiheytingAlgebra.{0} Prop Prop.booleanAlgebra)))))) (BooleanAlgebra.toSDiff.{0} Prop Prop.booleanAlgebra) p q) (Xor' p q)
Case conversion may be inaccurate. Consider using '#align symm_diff_eq_xor symmDiff_eq_Xor'ₓ'. -/
theorem symmDiff_eq_Xor' (p q : Prop) : p ∆ q = Xor' p q :=
  rfl
#align symm_diff_eq_xor symmDiff_eq_Xor'

/- warning: bihimp_iff_iff -> bihimp_iff_iff is a dubious translation:
lean 3 declaration is
  forall {p : Prop} {q : Prop}, Iff (bihimp.{0} Prop (SemilatticeInf.toHasInf.{0} Prop (Lattice.toSemilatticeInf.{0} Prop (GeneralizedCoheytingAlgebra.toLattice.{0} Prop (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{0} Prop (BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} Prop Prop.booleanAlgebra))))) (BooleanAlgebra.toHasHimp.{0} Prop Prop.booleanAlgebra) p q) (Iff p q)
but is expected to have type
  forall {p : Prop} {q : Prop}, Iff (bihimp.{0} Prop (Lattice.toHasInf.{0} Prop (GeneralizedCoheytingAlgebra.toLattice.{0} Prop (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} Prop (BiheytingAlgebra.toCoheytingAlgebra.{0} Prop (BooleanAlgebra.toBiheytingAlgebra.{0} Prop Prop.booleanAlgebra))))) (BooleanAlgebra.toHImp.{0} Prop Prop.booleanAlgebra) p q) (Iff p q)
Case conversion may be inaccurate. Consider using '#align bihimp_iff_iff bihimp_iff_iffₓ'. -/
@[simp]
theorem bihimp_iff_iff {p q : Prop} : p ⇔ q ↔ (p ↔ q) :=
  (iff_iff_implies_and_implies _ _).symm.trans Iff.comm
#align bihimp_iff_iff bihimp_iff_iff

/- warning: bool.symm_diff_eq_bxor -> Bool.symmDiff_eq_xor is a dubious translation:
lean 3 declaration is
  forall (p : Bool) (q : Bool), Eq.{1} Bool (symmDiff.{0} Bool (SemilatticeSup.toHasSup.{0} Bool (Lattice.toSemilatticeSup.{0} Bool (GeneralizedCoheytingAlgebra.toLattice.{0} Bool (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{0} Bool (BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} Bool Bool.booleanAlgebra))))) (BooleanAlgebra.toHasSdiff.{0} Bool Bool.booleanAlgebra) p q) (xor p q)
but is expected to have type
  forall (p : Bool) (q : Bool), Eq.{1} Bool (symmDiff.{0} Bool (SemilatticeSup.toHasSup.{0} Bool (Lattice.toSemilatticeSup.{0} Bool (GeneralizedCoheytingAlgebra.toLattice.{0} Bool (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} Bool (BiheytingAlgebra.toCoheytingAlgebra.{0} Bool (BooleanAlgebra.toBiheytingAlgebra.{0} Bool instBooleanAlgebraBool)))))) (BooleanAlgebra.toSDiff.{0} Bool instBooleanAlgebraBool) p q) (xor p q)
Case conversion may be inaccurate. Consider using '#align bool.symm_diff_eq_bxor Bool.symmDiff_eq_xorₓ'. -/
@[simp]
theorem Bool.symmDiff_eq_xor : ∀ p q : Bool, p ∆ q = xor p q := by decide
#align bool.symm_diff_eq_bxor Bool.symmDiff_eq_xor

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] (a b c d : α)

#print toDual_symmDiff /-
@[simp]
theorem toDual_symmDiff : toDual (a ∆ b) = toDual a ⇔ toDual b :=
  rfl
#align to_dual_symm_diff toDual_symmDiff
-/

#print ofDual_bihimp /-
@[simp]
theorem ofDual_bihimp (a b : αᵒᵈ) : ofDual (a ⇔ b) = ofDual a ∆ ofDual b :=
  rfl
#align of_dual_bihimp ofDual_bihimp
-/

/- warning: symm_diff_comm -> symmDiff_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align symm_diff_comm symmDiff_commₓ'. -/
theorem symmDiff_comm : a ∆ b = b ∆ a := by simp only [(· ∆ ·), sup_comm]
#align symm_diff_comm symmDiff_comm

/- warning: symm_diff_is_comm -> symmDiff_isCommutative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α], IsCommutative.{u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α], IsCommutative.{u1} α (fun (x._@.Mathlib.Order.SymmDiff._hyg.1539 : α) (x._@.Mathlib.Order.SymmDiff._hyg.1541 : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.1539 x._@.Mathlib.Order.SymmDiff._hyg.1541)
Case conversion may be inaccurate. Consider using '#align symm_diff_is_comm symmDiff_isCommutativeₓ'. -/
instance symmDiff_isCommutative : IsCommutative α (· ∆ ·) :=
  ⟨symmDiff_comm⟩
#align symm_diff_is_comm symmDiff_isCommutative

/- warning: symm_diff_self -> symmDiff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a a) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a a) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align symm_diff_self symmDiff_selfₓ'. -/
@[simp]
theorem symmDiff_self : a ∆ a = ⊥ := by rw [(· ∆ ·), sup_idem, sdiff_self]
#align symm_diff_self symmDiff_self

/- warning: symm_diff_bot -> symmDiff_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1))) a
Case conversion may be inaccurate. Consider using '#align symm_diff_bot symmDiff_botₓ'. -/
@[simp]
theorem symmDiff_bot : a ∆ ⊥ = a := by rw [(· ∆ ·), sdiff_bot, bot_sdiff, sup_bot_eq]
#align symm_diff_bot symmDiff_bot

/- warning: bot_symm_diff -> bot_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1)) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1)) a) a
Case conversion may be inaccurate. Consider using '#align bot_symm_diff bot_symmDiffₓ'. -/
@[simp]
theorem bot_symmDiff : ⊥ ∆ a = a := by rw [symmDiff_comm, symmDiff_bot]
#align bot_symm_diff bot_symmDiff

/- warning: symm_diff_eq_bot -> symmDiff_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1))) (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1))) (Eq.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_eq_bot symmDiff_eq_botₓ'. -/
@[simp]
theorem symmDiff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b := by
  simp_rw [symmDiff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]
#align symm_diff_eq_bot symmDiff_eq_bot

/- warning: symm_diff_of_le -> symmDiff_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a))
Case conversion may be inaccurate. Consider using '#align symm_diff_of_le symmDiff_of_leₓ'. -/
theorem symmDiff_of_le {a b : α} (h : a ≤ b) : a ∆ b = b \ a := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, bot_sup_eq]
#align symm_diff_of_le symmDiff_of_le

/- warning: symm_diff_of_ge -> symmDiff_of_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align symm_diff_of_ge symmDiff_of_geₓ'. -/
theorem symmDiff_of_ge {a b : α} (h : b ≤ a) : a ∆ b = a \ b := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, sup_bot_eq]
#align symm_diff_of_ge symmDiff_of_ge

/- warning: symm_diff_le -> symmDiff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c)
Case conversion may be inaccurate. Consider using '#align symm_diff_le symmDiff_leₓ'. -/
theorem symmDiff_le {a b c : α} (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ∆ b ≤ c :=
  sup_le (sdiff_le_iff.2 ha) <| sdiff_le_iff.2 hb
#align symm_diff_le symmDiff_le

/- warning: symm_diff_le_iff -> symmDiff_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a c)))
Case conversion may be inaccurate. Consider using '#align symm_diff_le_iff symmDiff_le_iffₓ'. -/
theorem symmDiff_le_iff {a b c : α} : a ∆ b ≤ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c := by
  simp_rw [symmDiff, sup_le_iff, sdiff_le_iff]
#align symm_diff_le_iff symmDiff_le_iff

/- warning: symm_diff_le_sup -> symmDiff_le_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_le_sup symmDiff_le_supₓ'. -/
@[simp]
theorem symmDiff_le_sup {a b : α} : a ∆ b ≤ a ⊔ b :=
  sup_le_sup sdiff_le sdiff_le
#align symm_diff_le_sup symmDiff_le_sup

/- warning: symm_diff_eq_sup_sdiff_inf -> symmDiff_eq_sup_sdiff_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align symm_diff_eq_sup_sdiff_inf symmDiff_eq_sup_sdiff_infₓ'. -/
theorem symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) := by simp [sup_sdiff, symmDiff]
#align symm_diff_eq_sup_sdiff_inf symmDiff_eq_sup_sdiff_inf

/- warning: disjoint.symm_diff_eq_sup -> Disjoint.symmDiff_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align disjoint.symm_diff_eq_sup Disjoint.symmDiff_eq_supₓ'. -/
theorem Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoint a b) : a ∆ b = a ⊔ b := by
  rw [(· ∆ ·), h.sdiff_eq_left, h.sdiff_eq_right]
#align disjoint.symm_diff_eq_sup Disjoint.symmDiff_eq_sup

/- warning: symm_diff_sdiff -> symmDiff_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a c)))
Case conversion may be inaccurate. Consider using '#align symm_diff_sdiff symmDiff_sdiffₓ'. -/
theorem symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) := by
  rw [symmDiff, sup_sdiff_distrib, sdiff_sdiff_left, sdiff_sdiff_left]
#align symm_diff_sdiff symmDiff_sdiff

/- warning: symm_diff_sdiff_inf -> symmDiff_sdiff_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a b)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_sdiff_inf symmDiff_sdiff_infₓ'. -/
@[simp]
theorem symmDiff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b :=
  by
  rw [symmDiff_sdiff]
  simp [symmDiff]
#align symm_diff_sdiff_inf symmDiff_sdiff_inf

/- warning: symm_diff_sdiff_eq_sup -> symmDiff_sdiff_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_sdiff_eq_sup symmDiff_sdiff_eq_supₓ'. -/
@[simp]
theorem symmDiff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b :=
  by
  rw [symmDiff, sdiff_idem]
  exact
    le_antisymm (sup_le_sup sdiff_le sdiff_le)
      (sup_le le_sdiff_sup <| le_sdiff_sup.trans <| sup_le le_sup_right le_sdiff_sup)
#align symm_diff_sdiff_eq_sup symmDiff_sdiff_eq_sup

/- warning: sdiff_symm_diff_eq_sup -> sdiff_symmDiff_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align sdiff_symm_diff_eq_sup sdiff_symmDiff_eq_supₓ'. -/
@[simp]
theorem sdiff_symmDiff_eq_sup : (a \ b) ∆ b = a ⊔ b := by
  rw [symmDiff_comm, symmDiff_sdiff_eq_sup, sup_comm]
#align sdiff_symm_diff_eq_sup sdiff_symmDiff_eq_sup

/- warning: symm_diff_sup_inf -> symmDiff_sup_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_sup_inf symmDiff_sup_infₓ'. -/
@[simp]
theorem symmDiff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b :=
  by
  refine' le_antisymm (sup_le symmDiff_le_sup inf_le_sup) _
  rw [sup_inf_left, symmDiff]
  refine' sup_le (le_inf le_sup_right _) (le_inf _ le_sup_right)
  · rw [sup_right_comm]
    exact le_sup_of_le_left le_sdiff_sup
  · rw [sup_assoc]
    exact le_sup_of_le_right le_sdiff_sup
#align symm_diff_sup_inf symmDiff_sup_inf

/- warning: inf_sup_symm_diff -> inf_sup_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align inf_sup_symm_diff inf_sup_symmDiffₓ'. -/
@[simp]
theorem inf_sup_symmDiff : a ⊓ b ⊔ a ∆ b = a ⊔ b := by rw [sup_comm, symmDiff_sup_inf]
#align inf_sup_symm_diff inf_sup_symmDiff

/- warning: symm_diff_symm_diff_inf -> symmDiff_symmDiff_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_symm_diff_inf symmDiff_symmDiff_infₓ'. -/
@[simp]
theorem symmDiff_symmDiff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b := by
  rw [← symmDiff_sdiff_inf a, sdiff_symmDiff_eq_sup, symmDiff_sup_inf]
#align symm_diff_symm_diff_inf symmDiff_symmDiff_inf

/- warning: inf_symm_diff_symm_diff -> inf_symmDiff_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align inf_symm_diff_symm_diff inf_symmDiff_symmDiffₓ'. -/
@[simp]
theorem inf_symmDiff_symmDiff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b := by
  rw [symmDiff_comm, symmDiff_symmDiff_inf]
#align inf_symm_diff_symm_diff inf_symmDiff_symmDiff

/- warning: symm_diff_triangle -> symmDiff_triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align symm_diff_triangle symmDiff_triangleₓ'. -/
theorem symmDiff_triangle : a ∆ c ≤ a ∆ b ⊔ b ∆ c :=
  by
  refine' (sup_le_sup (sdiff_triangle a b c) <| sdiff_triangle _ b _).trans_eq _
  rw [@sup_comm _ _ (c \ b), sup_sup_sup_comm, symmDiff, symmDiff]
#align symm_diff_triangle symmDiff_triangle

end GeneralizedCoheytingAlgebra

section GeneralizedHeytingAlgebra

variable [GeneralizedHeytingAlgebra α] (a b c d : α)

#print toDual_bihimp /-
@[simp]
theorem toDual_bihimp : toDual (a ⇔ b) = toDual a ∆ toDual b :=
  rfl
#align to_dual_bihimp toDual_bihimp
-/

#print ofDual_symmDiff /-
@[simp]
theorem ofDual_symmDiff (a b : αᵒᵈ) : ofDual (a ∆ b) = ofDual a ⇔ ofDual b :=
  rfl
#align of_dual_symm_diff ofDual_symmDiff
-/

/- warning: bihimp_comm -> bihimp_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align bihimp_comm bihimp_commₓ'. -/
theorem bihimp_comm : a ⇔ b = b ⇔ a := by simp only [(· ⇔ ·), inf_comm]
#align bihimp_comm bihimp_comm

/- warning: bihimp_is_comm -> bihimp_isCommutative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α], IsCommutative.{u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α], IsCommutative.{u1} α (fun (x._@.Mathlib.Order.SymmDiff._hyg.3040 : α) (x._@.Mathlib.Order.SymmDiff._hyg.3042 : α) => bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.3040 x._@.Mathlib.Order.SymmDiff._hyg.3042)
Case conversion may be inaccurate. Consider using '#align bihimp_is_comm bihimp_isCommutativeₓ'. -/
instance bihimp_isCommutative : IsCommutative α (· ⇔ ·) :=
  ⟨bihimp_comm⟩
#align bihimp_is_comm bihimp_isCommutative

/- warning: bihimp_self -> bihimp_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a a) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a a) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align bihimp_self bihimp_selfₓ'. -/
@[simp]
theorem bihimp_self : a ⇔ a = ⊤ := by rw [(· ⇔ ·), inf_idem, himp_self]
#align bihimp_self bihimp_self

/- warning: bihimp_top -> bihimp_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1))) a
Case conversion may be inaccurate. Consider using '#align bihimp_top bihimp_topₓ'. -/
@[simp]
theorem bihimp_top : a ⇔ ⊤ = a := by rw [(· ⇔ ·), himp_top, top_himp, inf_top_eq]
#align bihimp_top bihimp_top

/- warning: top_bihimp -> top_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1)) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1)) a) a
Case conversion may be inaccurate. Consider using '#align top_bihimp top_bihimpₓ'. -/
@[simp]
theorem top_bihimp : ⊤ ⇔ a = a := by rw [bihimp_comm, bihimp_top]
#align top_bihimp top_bihimp

/- warning: bihimp_eq_top -> bihimp_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1))) (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1))) (Eq.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align bihimp_eq_top bihimp_eq_topₓ'. -/
@[simp]
theorem bihimp_eq_top {a b : α} : a ⇔ b = ⊤ ↔ a = b :=
  @symmDiff_eq_bot αᵒᵈ _ _ _
#align bihimp_eq_top bihimp_eq_top

/- warning: bihimp_of_le -> bihimp_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b a))
Case conversion may be inaccurate. Consider using '#align bihimp_of_le bihimp_of_leₓ'. -/
theorem bihimp_of_le {a b : α} (h : a ≤ b) : a ⇔ b = b ⇨ a := by
  rw [bihimp, himp_eq_top_iff.2 h, inf_top_eq]
#align bihimp_of_le bihimp_of_le

/- warning: bihimp_of_ge -> bihimp_of_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align bihimp_of_ge bihimp_of_geₓ'. -/
theorem bihimp_of_ge {a b : α} (h : b ≤ a) : a ⇔ b = a ⇨ b := by
  rw [bihimp, himp_eq_top_iff.2 h, top_inf_eq]
#align bihimp_of_ge bihimp_of_ge

/- warning: le_bihimp -> le_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a c) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a c) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align le_bihimp le_bihimpₓ'. -/
theorem le_bihimp {a b c : α} (hb : a ⊓ b ≤ c) (hc : a ⊓ c ≤ b) : a ≤ b ⇔ c :=
  le_inf (le_himp_iff.2 hc) <| le_himp_iff.2 hb
#align le_bihimp le_bihimp

/- warning: le_bihimp_iff -> le_bihimp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a c) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a c) b))
Case conversion may be inaccurate. Consider using '#align le_bihimp_iff le_bihimp_iffₓ'. -/
theorem le_bihimp_iff {a b c : α} : a ≤ b ⇔ c ↔ a ⊓ b ≤ c ∧ a ⊓ c ≤ b := by
  simp_rw [bihimp, le_inf_iff, le_himp_iff, and_comm]
#align le_bihimp_iff le_bihimp_iff

/- warning: inf_le_bihimp -> inf_le_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align inf_le_bihimp inf_le_bihimpₓ'. -/
@[simp]
theorem inf_le_bihimp {a b : α} : a ⊓ b ≤ a ⇔ b :=
  inf_le_inf le_himp le_himp
#align inf_le_bihimp inf_le_bihimp

/- warning: bihimp_eq_inf_himp_inf -> bihimp_eq_inf_himp_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align bihimp_eq_inf_himp_inf bihimp_eq_inf_himp_infₓ'. -/
theorem bihimp_eq_inf_himp_inf : a ⇔ b = a ⊔ b ⇨ a ⊓ b := by simp [himp_inf_distrib, bihimp]
#align bihimp_eq_inf_himp_inf bihimp_eq_inf_himp_inf

/- warning: codisjoint.bihimp_eq_inf -> Codisjoint.bihimp_eq_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align codisjoint.bihimp_eq_inf Codisjoint.bihimp_eq_infₓ'. -/
theorem Codisjoint.bihimp_eq_inf {a b : α} (h : Codisjoint a b) : a ⇔ b = a ⊓ b := by
  rw [(· ⇔ ·), h.himp_eq_left, h.himp_eq_right]
#align codisjoint.bihimp_eq_inf Codisjoint.bihimp_eq_inf

/- warning: himp_bihimp -> himp_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a c) b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a c) b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b) c))
Case conversion may be inaccurate. Consider using '#align himp_bihimp himp_bihimpₓ'. -/
theorem himp_bihimp : a ⇨ b ⇔ c = (a ⊓ c ⇨ b) ⊓ (a ⊓ b ⇨ c) := by
  rw [bihimp, himp_inf_distrib, himp_himp, himp_himp]
#align himp_bihimp himp_bihimp

/- warning: sup_himp_bihimp -> sup_himp_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align sup_himp_bihimp sup_himp_bihimpₓ'. -/
@[simp]
theorem sup_himp_bihimp : a ⊔ b ⇨ a ⇔ b = a ⇔ b :=
  by
  rw [himp_bihimp]
  simp [bihimp]
#align sup_himp_bihimp sup_himp_bihimp

/- warning: bihimp_himp_eq_inf -> bihimp_himp_eq_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_himp_eq_inf bihimp_himp_eq_infₓ'. -/
@[simp]
theorem bihimp_himp_eq_inf : a ⇔ (a ⇨ b) = a ⊓ b :=
  @symmDiff_sdiff_eq_sup αᵒᵈ _ _ _
#align bihimp_himp_eq_inf bihimp_himp_eq_inf

/- warning: himp_bihimp_eq_inf -> himp_bihimp_eq_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b a) b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b a) b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align himp_bihimp_eq_inf himp_bihimp_eq_infₓ'. -/
@[simp]
theorem himp_bihimp_eq_inf : (b ⇨ a) ⇔ b = a ⊓ b :=
  @sdiff_symmDiff_eq_sup αᵒᵈ _ _ _
#align himp_bihimp_eq_inf himp_bihimp_eq_inf

/- warning: bihimp_inf_sup -> bihimp_inf_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_inf_sup bihimp_inf_supₓ'. -/
@[simp]
theorem bihimp_inf_sup : a ⇔ b ⊓ (a ⊔ b) = a ⊓ b :=
  @symmDiff_sup_inf αᵒᵈ _ _ _
#align bihimp_inf_sup bihimp_inf_sup

/- warning: sup_inf_bihimp -> sup_inf_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align sup_inf_bihimp sup_inf_bihimpₓ'. -/
@[simp]
theorem sup_inf_bihimp : (a ⊔ b) ⊓ a ⇔ b = a ⊓ b :=
  @inf_sup_symmDiff αᵒᵈ _ _ _
#align sup_inf_bihimp sup_inf_bihimp

/- warning: bihimp_bihimp_sup -> bihimp_bihimp_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_bihimp_sup bihimp_bihimp_supₓ'. -/
@[simp]
theorem bihimp_bihimp_sup : a ⇔ b ⇔ (a ⊔ b) = a ⊓ b :=
  @symmDiff_symmDiff_inf αᵒᵈ _ _ _
#align bihimp_bihimp_sup bihimp_bihimp_sup

/- warning: sup_bihimp_bihimp -> sup_bihimp_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align sup_bihimp_bihimp sup_bihimp_bihimpₓ'. -/
@[simp]
theorem sup_bihimp_bihimp : (a ⊔ b) ⇔ (a ⇔ b) = a ⊓ b :=
  @inf_symmDiff_symmDiff αᵒᵈ _ _ _
#align sup_bihimp_bihimp sup_bihimp_bihimp

/- warning: bihimp_triangle -> bihimp_triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align bihimp_triangle bihimp_triangleₓ'. -/
theorem bihimp_triangle : a ⇔ b ⊓ b ⇔ c ≤ a ⇔ c :=
  @symmDiff_triangle αᵒᵈ _ _ _ _
#align bihimp_triangle bihimp_triangle

end GeneralizedHeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] (a : α)

/- warning: symm_diff_top' -> symmDiff_top' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align symm_diff_top' symmDiff_top'ₓ'. -/
@[simp]
theorem symmDiff_top' : a ∆ ⊤ = ￢a := by simp [symmDiff]
#align symm_diff_top' symmDiff_top'

/- warning: top_symm_diff' -> top_symmDiff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1)) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1)) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align top_symm_diff' top_symmDiff'ₓ'. -/
@[simp]
theorem top_symmDiff' : ⊤ ∆ a = ￢a := by simp [symmDiff]
#align top_symm_diff' top_symmDiff'

/- warning: hnot_symm_diff_self -> hnot_symmDiff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) a) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) a) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align hnot_symm_diff_self hnot_symmDiff_selfₓ'. -/
@[simp]
theorem hnot_symmDiff_self : (￢a) ∆ a = ⊤ :=
  by
  rw [eq_top_iff, symmDiff, hnot_sdiff, sup_sdiff_self]
  exact Codisjoint.top_le codisjoint_hnot_left
#align hnot_symm_diff_self hnot_symmDiff_self

/- warning: symm_diff_hnot_self -> symmDiff_hnot_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align symm_diff_hnot_self symmDiff_hnot_selfₓ'. -/
@[simp]
theorem symmDiff_hnot_self : a ∆ (￢a) = ⊤ := by rw [symmDiff_comm, hnot_symmDiff_self]
#align symm_diff_hnot_self symmDiff_hnot_self

/- warning: is_compl.symm_diff_eq_top -> IsCompl.symmDiff_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a b) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a b) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_compl.symm_diff_eq_top IsCompl.symmDiff_eq_topₓ'. -/
theorem IsCompl.symmDiff_eq_top {a b : α} (h : IsCompl a b) : a ∆ b = ⊤ := by
  rw [h.eq_hnot, hnot_symmDiff_self]
#align is_compl.symm_diff_eq_top IsCompl.symmDiff_eq_top

end CoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] (a : α)

/- warning: bihimp_bot -> bihimp_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align bihimp_bot bihimp_botₓ'. -/
@[simp]
theorem bihimp_bot : a ⇔ ⊥ = aᶜ := by simp [bihimp]
#align bihimp_bot bihimp_bot

/- warning: bot_bihimp -> bot_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1)) a) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1)) a) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align bot_bihimp bot_bihimpₓ'. -/
@[simp]
theorem bot_bihimp : ⊥ ⇔ a = aᶜ := by simp [bihimp]
#align bot_bihimp bot_bihimp

/- warning: compl_bihimp_self -> compl_bihimp_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) a) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) a) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align compl_bihimp_self compl_bihimp_selfₓ'. -/
@[simp]
theorem compl_bihimp_self : aᶜ ⇔ a = ⊥ :=
  @hnot_symmDiff_self αᵒᵈ _ _
#align compl_bihimp_self compl_bihimp_self

/- warning: bihimp_hnot_self -> bihimp_hnot_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align bihimp_hnot_self bihimp_hnot_selfₓ'. -/
@[simp]
theorem bihimp_hnot_self : a ⇔ aᶜ = ⊥ :=
  @symmDiff_hnot_self αᵒᵈ _ _
#align bihimp_hnot_self bihimp_hnot_self

/- warning: is_compl.bihimp_eq_bot -> IsCompl.bihimp_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (HeytingAlgebra.toBoundedOrder.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (HeytingAlgebra.toBoundedOrder.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_compl.bihimp_eq_bot IsCompl.bihimp_eq_botₓ'. -/
theorem IsCompl.bihimp_eq_bot {a b : α} (h : IsCompl a b) : a ⇔ b = ⊥ := by
  rw [h.eq_compl, compl_bihimp_self]
#align is_compl.bihimp_eq_bot IsCompl.bihimp_eq_bot

end HeytingAlgebra

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] (a b c d : α)

/- warning: sup_sdiff_symm_diff -> sup_sdiff_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align sup_sdiff_symm_diff sup_sdiff_symmDiffₓ'. -/
@[simp]
theorem sup_sdiff_symmDiff : (a ⊔ b) \ a ∆ b = a ⊓ b :=
  sdiff_eq_symm inf_le_sup (by rw [symmDiff_eq_sup_sdiff_inf])
#align sup_sdiff_symm_diff sup_sdiff_symmDiff

/- warning: disjoint_symm_diff_inf -> disjoint_symmDiff_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align disjoint_symm_diff_inf disjoint_symmDiff_infₓ'. -/
theorem disjoint_symmDiff_inf : Disjoint (a ∆ b) (a ⊓ b) :=
  by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact disjoint_sdiff_self_left
#align disjoint_symm_diff_inf disjoint_symmDiff_inf

/- warning: inf_symm_diff_distrib_left -> inf_symmDiff_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b c)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b c)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a c))
Case conversion may be inaccurate. Consider using '#align inf_symm_diff_distrib_left inf_symmDiff_distrib_leftₓ'. -/
theorem inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c) := by
  rw [symmDiff_eq_sup_sdiff_inf, inf_sdiff_distrib_left, inf_sup_left, inf_inf_distrib_left,
    symmDiff_eq_sup_sdiff_inf]
#align inf_symm_diff_distrib_left inf_symmDiff_distrib_left

/- warning: inf_symm_diff_distrib_right -> inf_symmDiff_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a c) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a c) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align inf_symm_diff_distrib_right inf_symmDiff_distrib_rightₓ'. -/
theorem inf_symmDiff_distrib_right : a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c) := by
  simp_rw [@inf_comm _ _ _ c, inf_symmDiff_distrib_left]
#align inf_symm_diff_distrib_right inf_symmDiff_distrib_right

/- warning: sdiff_symm_diff -> sdiff_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) c a) b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c a) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) c a) b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c a) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c b)))
Case conversion may be inaccurate. Consider using '#align sdiff_symm_diff sdiff_symmDiffₓ'. -/
theorem sdiff_symmDiff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b := by
  simp only [(· ∆ ·), sdiff_sdiff_sup_sdiff']
#align sdiff_symm_diff sdiff_symmDiff

/- warning: sdiff_symm_diff' -> sdiff_symmDiff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) c a) b) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) c a) b) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)))
Case conversion may be inaccurate. Consider using '#align sdiff_symm_diff' sdiff_symmDiff'ₓ'. -/
theorem sdiff_symmDiff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b) := by
  rw [sdiff_symmDiff, sdiff_sup, sup_comm]
#align sdiff_symm_diff' sdiff_symmDiff'

/- warning: symm_diff_sdiff_left -> symmDiff_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) a) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) a) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align symm_diff_sdiff_left symmDiff_sdiff_leftₓ'. -/
@[simp]
theorem symmDiff_sdiff_left : a ∆ b \ a = b \ a := by
  rw [symmDiff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]
#align symm_diff_sdiff_left symmDiff_sdiff_left

/- warning: symm_diff_sdiff_right -> symmDiff_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) b) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) b) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_sdiff_right symmDiff_sdiff_rightₓ'. -/
@[simp]
theorem symmDiff_sdiff_right : a ∆ b \ b = a \ b := by rw [symmDiff_comm, symmDiff_sdiff_left]
#align symm_diff_sdiff_right symmDiff_sdiff_right

/- warning: sdiff_symm_diff_left -> sdiff_symmDiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align sdiff_symm_diff_left sdiff_symmDiff_leftₓ'. -/
@[simp]
theorem sdiff_symmDiff_left : a \ a ∆ b = a ⊓ b := by simp [sdiff_symmDiff]
#align sdiff_symm_diff_left sdiff_symmDiff_left

/- warning: sdiff_symm_diff_right -> sdiff_symmDiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align sdiff_symm_diff_right sdiff_symmDiff_rightₓ'. -/
@[simp]
theorem sdiff_symmDiff_right : b \ a ∆ b = a ⊓ b := by
  rw [symmDiff_comm, inf_comm, sdiff_symmDiff_left]
#align sdiff_symm_diff_right sdiff_symmDiff_right

/- warning: symm_diff_eq_sup -> symmDiff_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)) (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)) (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_eq_sup symmDiff_eq_supₓ'. -/
theorem symmDiff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b :=
  by
  refine' ⟨fun h => _, Disjoint.symmDiff_eq_sup⟩
  rw [symmDiff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h
  exact h.of_disjoint_inf_of_le le_sup_left
#align symm_diff_eq_sup symmDiff_eq_sup

/- warning: le_symm_diff_iff_left -> le_symmDiff_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align le_symm_diff_iff_left le_symmDiff_iff_leftₓ'. -/
@[simp]
theorem le_symmDiff_iff_left : a ≤ a ∆ b ↔ Disjoint a b :=
  by
  refine' ⟨fun h => _, fun h => h.symm_diff_eq_sup.symm ▸ le_sup_left⟩
  rw [symmDiff_eq_sup_sdiff_inf] at h
  exact disjoint_iff_inf_le.mpr (le_sdiff_iff.1 <| inf_le_of_left_le h).le
#align le_symm_diff_iff_left le_symmDiff_iff_left

/- warning: le_symm_diff_iff_right -> le_symmDiff_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) b (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) b (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align le_symm_diff_iff_right le_symmDiff_iff_rightₓ'. -/
@[simp]
theorem le_symmDiff_iff_right : b ≤ a ∆ b ↔ Disjoint a b := by
  rw [symmDiff_comm, le_symmDiff_iff_left, disjoint_comm]
#align le_symm_diff_iff_right le_symmDiff_iff_right

/- warning: symm_diff_symm_diff_left -> symmDiff_symmDiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) b c)) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a c))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) b c)) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a c))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a b) c))
Case conversion may be inaccurate. Consider using '#align symm_diff_symm_diff_left symmDiff_symmDiff_leftₓ'. -/
theorem symmDiff_symmDiff_left : a ∆ b ∆ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ b ∆ c = a ∆ b \ c ⊔ c \ a ∆ b := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ (c \ (a ⊔ b) ⊔ c ⊓ a ⊓ b) := by
      rw [sdiff_symmDiff', @sup_comm _ _ (c ⊓ a ⊓ b), symmDiff_sdiff]
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl
    
#align symm_diff_symm_diff_left symmDiff_symmDiff_left

/- warning: symm_diff_symm_diff_right -> symmDiff_symmDiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) b c)) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a c))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) b c)) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a c))) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a b) c))
Case conversion may be inaccurate. Consider using '#align symm_diff_symm_diff_right symmDiff_symmDiff_rightₓ'. -/
theorem symmDiff_symmDiff_right :
    a ∆ (b ∆ c) = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ (b ∆ c) = a \ b ∆ c ⊔ b ∆ c \ a := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ a ⊓ b ⊓ c ⊔ (b \ (c ⊔ a) ⊔ c \ (b ⊔ a)) := by
      rw [sdiff_symmDiff', @sup_comm _ _ (a ⊓ b ⊓ c), symmDiff_sdiff]
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl
    
#align symm_diff_symm_diff_right symmDiff_symmDiff_right

/- warning: symm_diff_assoc -> symmDiff_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align symm_diff_assoc symmDiff_assocₓ'. -/
theorem symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c) := by
  rw [symmDiff_symmDiff_left, symmDiff_symmDiff_right]
#align symm_diff_assoc symmDiff_assoc

/- warning: symm_diff_is_assoc -> symmDiff_isAssociative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α], IsAssociative.{u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α], IsAssociative.{u1} α (fun (x._@.Mathlib.Order.SymmDiff._hyg.6043 : α) (x._@.Mathlib.Order.SymmDiff._hyg.6045 : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.6043 x._@.Mathlib.Order.SymmDiff._hyg.6045)
Case conversion may be inaccurate. Consider using '#align symm_diff_is_assoc symmDiff_isAssociativeₓ'. -/
instance symmDiff_isAssociative : IsAssociative α (· ∆ ·) :=
  ⟨symmDiff_assoc⟩
#align symm_diff_is_assoc symmDiff_isAssociative

/- warning: symm_diff_left_comm -> symmDiff_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b c)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b c)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align symm_diff_left_comm symmDiff_left_commₓ'. -/
theorem symmDiff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c) := by
  simp_rw [← symmDiff_assoc, symmDiff_comm]
#align symm_diff_left_comm symmDiff_left_comm

/- warning: symm_diff_right_comm -> symmDiff_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a c) b)
Case conversion may be inaccurate. Consider using '#align symm_diff_right_comm symmDiff_right_commₓ'. -/
theorem symmDiff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b := by simp_rw [symmDiff_assoc, symmDiff_comm]
#align symm_diff_right_comm symmDiff_right_comm

/- warning: symm_diff_symm_diff_symm_diff_comm -> symmDiff_symmDiff_symmDiff_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c d)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c d)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align symm_diff_symm_diff_symm_diff_comm symmDiff_symmDiff_symmDiff_commₓ'. -/
theorem symmDiff_symmDiff_symmDiff_comm : a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d) := by
  simp_rw [symmDiff_assoc, symmDiff_left_comm]
#align symm_diff_symm_diff_symm_diff_comm symmDiff_symmDiff_symmDiff_comm

/- warning: symm_diff_symm_diff_cancel_left -> symmDiff_symmDiff_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) b
Case conversion may be inaccurate. Consider using '#align symm_diff_symm_diff_cancel_left symmDiff_symmDiff_cancel_leftₓ'. -/
@[simp]
theorem symmDiff_symmDiff_cancel_left : a ∆ (a ∆ b) = b := by simp [← symmDiff_assoc]
#align symm_diff_symm_diff_cancel_left symmDiff_symmDiff_cancel_left

/- warning: symm_diff_symm_diff_cancel_right -> symmDiff_symmDiff_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b a) a) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b a) a) b
Case conversion may be inaccurate. Consider using '#align symm_diff_symm_diff_cancel_right symmDiff_symmDiff_cancel_rightₓ'. -/
@[simp]
theorem symmDiff_symmDiff_cancel_right : b ∆ a ∆ a = b := by simp [symmDiff_assoc]
#align symm_diff_symm_diff_cancel_right symmDiff_symmDiff_cancel_right

/- warning: symm_diff_symm_diff_self' -> symmDiff_symmDiff_self' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) a) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) a) b
Case conversion may be inaccurate. Consider using '#align symm_diff_symm_diff_self' symmDiff_symmDiff_self'ₓ'. -/
@[simp]
theorem symmDiff_symmDiff_self' : a ∆ b ∆ a = b := by
  rw [symmDiff_comm, symmDiff_symmDiff_cancel_left]
#align symm_diff_symm_diff_self' symmDiff_symmDiff_self'

/- warning: symm_diff_left_involutive -> symmDiff_left_involutive is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Involutive.{succ u1} α (fun (_x : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) _x a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Involutive.{succ u1} α (fun (_x : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) _x a)
Case conversion may be inaccurate. Consider using '#align symm_diff_left_involutive symmDiff_left_involutiveₓ'. -/
theorem symmDiff_left_involutive (a : α) : Involutive (· ∆ a) :=
  symmDiff_symmDiff_cancel_right _
#align symm_diff_left_involutive symmDiff_left_involutive

/- warning: symm_diff_right_involutive -> symmDiff_right_involutive is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Involutive.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Involutive.{succ u1} α ((fun (x._@.Mathlib.Order.SymmDiff._hyg.6378 : α) (x._@.Mathlib.Order.SymmDiff._hyg.6380 : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.6378 x._@.Mathlib.Order.SymmDiff._hyg.6380) a)
Case conversion may be inaccurate. Consider using '#align symm_diff_right_involutive symmDiff_right_involutiveₓ'. -/
theorem symmDiff_right_involutive (a : α) : Involutive ((· ∆ ·) a) :=
  symmDiff_symmDiff_cancel_left _
#align symm_diff_right_involutive symmDiff_right_involutive

/- warning: symm_diff_left_injective -> symmDiff_left_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Injective.{succ u1, succ u1} α α (fun (_x : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) _x a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Injective.{succ u1, succ u1} α α (fun (_x : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) _x a)
Case conversion may be inaccurate. Consider using '#align symm_diff_left_injective symmDiff_left_injectiveₓ'. -/
theorem symmDiff_left_injective (a : α) : Injective (· ∆ a) :=
  (symmDiff_left_involutive _).Injective
#align symm_diff_left_injective symmDiff_left_injective

/- warning: symm_diff_right_injective -> symmDiff_right_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Injective.{succ u1, succ u1} α α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Injective.{succ u1, succ u1} α α ((fun (x._@.Mathlib.Order.SymmDiff._hyg.6450 : α) (x._@.Mathlib.Order.SymmDiff._hyg.6452 : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.6450 x._@.Mathlib.Order.SymmDiff._hyg.6452) a)
Case conversion may be inaccurate. Consider using '#align symm_diff_right_injective symmDiff_right_injectiveₓ'. -/
theorem symmDiff_right_injective (a : α) : Injective ((· ∆ ·) a) :=
  (symmDiff_right_involutive _).Injective
#align symm_diff_right_injective symmDiff_right_injective

/- warning: symm_diff_left_surjective -> symmDiff_left_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Surjective.{succ u1, succ u1} α α (fun (_x : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) _x a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Surjective.{succ u1, succ u1} α α (fun (_x : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) _x a)
Case conversion may be inaccurate. Consider using '#align symm_diff_left_surjective symmDiff_left_surjectiveₓ'. -/
theorem symmDiff_left_surjective (a : α) : Surjective (· ∆ a) :=
  (symmDiff_left_involutive _).Surjective
#align symm_diff_left_surjective symmDiff_left_surjective

/- warning: symm_diff_right_surjective -> symmDiff_right_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Surjective.{succ u1, succ u1} α α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (a : α), Function.Surjective.{succ u1, succ u1} α α ((fun (x._@.Mathlib.Order.SymmDiff._hyg.6525 : α) (x._@.Mathlib.Order.SymmDiff._hyg.6527 : α) => symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.6525 x._@.Mathlib.Order.SymmDiff._hyg.6527) a)
Case conversion may be inaccurate. Consider using '#align symm_diff_right_surjective symmDiff_right_surjectiveₓ'. -/
theorem symmDiff_right_surjective (a : α) : Surjective ((· ∆ ·) a) :=
  (symmDiff_right_involutive _).Surjective
#align symm_diff_right_surjective symmDiff_right_surjective

variable {a b c}

/- warning: symm_diff_left_inj -> symmDiff_left_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c b)) (Eq.{succ u1} α a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c b)) (Eq.{succ u1} α a c)
Case conversion may be inaccurate. Consider using '#align symm_diff_left_inj symmDiff_left_injₓ'. -/
@[simp]
theorem symmDiff_left_inj : a ∆ b = c ∆ b ↔ a = c :=
  (symmDiff_left_injective _).eq_iff
#align symm_diff_left_inj symmDiff_left_inj

/- warning: symm_diff_right_inj -> symmDiff_right_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a c)) (Eq.{succ u1} α b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a c)) (Eq.{succ u1} α b c)
Case conversion may be inaccurate. Consider using '#align symm_diff_right_inj symmDiff_right_injₓ'. -/
@[simp]
theorem symmDiff_right_inj : a ∆ b = a ∆ c ↔ b = c :=
  (symmDiff_right_injective _).eq_iff
#align symm_diff_right_inj symmDiff_right_inj

/- warning: symm_diff_eq_left -> symmDiff_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) a) (Eq.{succ u1} α b (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) a) (Eq.{succ u1} α b (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align symm_diff_eq_left symmDiff_eq_leftₓ'. -/
@[simp]
theorem symmDiff_eq_left : a ∆ b = a ↔ b = ⊥ :=
  calc
    a ∆ b = a ↔ a ∆ b = a ∆ ⊥ := by rw [symmDiff_bot]
    _ ↔ b = ⊥ := by rw [symmDiff_right_inj]
    
#align symm_diff_eq_left symmDiff_eq_left

/- warning: symm_diff_eq_right -> symmDiff_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) b) (Eq.{succ u1} α a (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) b) (Eq.{succ u1} α a (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align symm_diff_eq_right symmDiff_eq_rightₓ'. -/
@[simp]
theorem symmDiff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symmDiff_comm, symmDiff_eq_left]
#align symm_diff_eq_right symmDiff_eq_right

/- warning: disjoint.symm_diff_left -> Disjoint.symmDiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a c) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) b c) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a c) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) b c) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) c)
Case conversion may be inaccurate. Consider using '#align disjoint.symm_diff_left Disjoint.symmDiff_leftₓ'. -/
protected theorem Disjoint.symmDiff_left (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (a ∆ b) c := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact (ha.sup_left hb).disjoint_sdiff_left
#align disjoint.symm_diff_left Disjoint.symmDiff_left

/- warning: disjoint.symm_diff_right -> Disjoint.symmDiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a c) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a c) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align disjoint.symm_diff_right Disjoint.symmDiff_rightₓ'. -/
protected theorem Disjoint.symmDiff_right (ha : Disjoint a b) (hb : Disjoint a c) :
    Disjoint a (b ∆ c) :=
  (ha.symm.symmDiff_left hb.symm).symm
#align disjoint.symm_diff_right Disjoint.symmDiff_right

/- warning: symm_diff_eq_iff_sdiff_eq -> symmDiff_eq_iff_sdiff_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) a c) -> (Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) c a) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) a c) -> (Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) a b) c) (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) c a) b))
Case conversion may be inaccurate. Consider using '#align symm_diff_eq_iff_sdiff_eq symmDiff_eq_iff_sdiff_eqₓ'. -/
theorem symmDiff_eq_iff_sdiff_eq (ha : a ≤ c) : a ∆ b = c ↔ c \ a = b :=
  by
  rw [← symmDiff_of_le ha]
  exact ((symmDiff_right_involutive a).toPerm _).apply_eq_iff_eq_symm_apply.trans eq_comm
#align symm_diff_eq_iff_sdiff_eq symmDiff_eq_iff_sdiff_eq

end GeneralizedBooleanAlgebra

section BooleanAlgebra

variable [BooleanAlgebra α] (a b c d : α)

/- `cogeneralized_boolean_algebra` isn't actually a typeclass, but the lemmas in here are dual to
the `generalized_boolean_algebra` ones -/
section CogeneralizedBooleanAlgebra

/- warning: inf_himp_bihimp -> inf_himp_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align inf_himp_bihimp inf_himp_bihimpₓ'. -/
@[simp]
theorem inf_himp_bihimp : a ⇔ b ⇨ a ⊓ b = a ⊔ b :=
  @sup_sdiff_symmDiff αᵒᵈ _ _ _
#align inf_himp_bihimp inf_himp_bihimp

/- warning: codisjoint_bihimp_sup -> codisjoint_bihimp_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align codisjoint_bihimp_sup codisjoint_bihimp_supₓ'. -/
theorem codisjoint_bihimp_sup : Codisjoint (a ⇔ b) (a ⊔ b) :=
  @disjoint_symmDiff_inf αᵒᵈ _ _ _
#align codisjoint_bihimp_sup codisjoint_bihimp_sup

/- warning: himp_bihimp_left -> himp_bihimp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b)) (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) a (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b)) (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align himp_bihimp_left himp_bihimp_leftₓ'. -/
@[simp]
theorem himp_bihimp_left : a ⇨ a ⇔ b = a ⇨ b :=
  @symmDiff_sdiff_left αᵒᵈ _ _ _
#align himp_bihimp_left himp_bihimp_left

/- warning: himp_bihimp_right -> himp_bihimp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b)) (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) b (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b)) (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align himp_bihimp_right himp_bihimp_rightₓ'. -/
@[simp]
theorem himp_bihimp_right : b ⇨ a ⇔ b = b ⇨ a :=
  @symmDiff_sdiff_right αᵒᵈ _ _ _
#align himp_bihimp_right himp_bihimp_right

/- warning: bihimp_himp_left -> bihimp_himp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_himp_left bihimp_himp_leftₓ'. -/
@[simp]
theorem bihimp_himp_left : a ⇔ b ⇨ a = a ⊔ b :=
  @sdiff_symmDiff_left αᵒᵈ _ _ _
#align bihimp_himp_left bihimp_himp_left

/- warning: bihimp_himp_right -> bihimp_himp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_himp_right bihimp_himp_rightₓ'. -/
@[simp]
theorem bihimp_himp_right : a ⇔ b ⇨ b = a ⊔ b :=
  @sdiff_symmDiff_right αᵒᵈ _ _ _
#align bihimp_himp_right bihimp_himp_right

/- warning: bihimp_eq_inf -> bihimp_eq_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b)) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) a b)) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_eq_inf bihimp_eq_infₓ'. -/
@[simp]
theorem bihimp_eq_inf : a ⇔ b = a ⊓ b ↔ Codisjoint a b :=
  @symmDiff_eq_sup αᵒᵈ _ _ _
#align bihimp_eq_inf bihimp_eq_inf

/- warning: bihimp_le_iff_left -> bihimp_le_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))))) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) a) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) a) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_le_iff_left bihimp_le_iff_leftₓ'. -/
@[simp]
theorem bihimp_le_iff_left : a ⇔ b ≤ a ↔ Codisjoint a b :=
  @le_symmDiff_iff_left αᵒᵈ _ _ _
#align bihimp_le_iff_left bihimp_le_iff_left

/- warning: bihimp_le_iff_right -> bihimp_le_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))))) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) b) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) b) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_le_iff_right bihimp_le_iff_rightₓ'. -/
@[simp]
theorem bihimp_le_iff_right : a ⇔ b ≤ b ↔ Codisjoint a b :=
  @le_symmDiff_iff_right αᵒᵈ _ _ _
#align bihimp_le_iff_right bihimp_le_iff_right

/- warning: bihimp_assoc -> bihimp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) c) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) c) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align bihimp_assoc bihimp_assocₓ'. -/
theorem bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c) :=
  @symmDiff_assoc αᵒᵈ _ _ _ _
#align bihimp_assoc bihimp_assoc

/- warning: bihimp_is_assoc -> bihimp_isAssociative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α], IsAssociative.{u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α], IsAssociative.{u1} α (fun (x._@.Mathlib.Order.SymmDiff._hyg.7446 : α) (x._@.Mathlib.Order.SymmDiff._hyg.7448 : α) => bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.7446 x._@.Mathlib.Order.SymmDiff._hyg.7448)
Case conversion may be inaccurate. Consider using '#align bihimp_is_assoc bihimp_isAssociativeₓ'. -/
instance bihimp_isAssociative : IsAssociative α (· ⇔ ·) :=
  ⟨bihimp_assoc⟩
#align bihimp_is_assoc bihimp_isAssociative

/- warning: bihimp_left_comm -> bihimp_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b c)) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) b c)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) b (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align bihimp_left_comm bihimp_left_commₓ'. -/
theorem bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c) := by simp_rw [← bihimp_assoc, bihimp_comm]
#align bihimp_left_comm bihimp_left_comm

/- warning: bihimp_right_comm -> bihimp_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) c) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) c) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a c) b)
Case conversion may be inaccurate. Consider using '#align bihimp_right_comm bihimp_right_commₓ'. -/
theorem bihimp_right_comm : a ⇔ b ⇔ c = a ⇔ c ⇔ b := by simp_rw [bihimp_assoc, bihimp_comm]
#align bihimp_right_comm bihimp_right_comm

/- warning: bihimp_bihimp_bihimp_comm -> bihimp_bihimp_bihimp_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) c d)) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a c) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) c d)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a c) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align bihimp_bihimp_bihimp_comm bihimp_bihimp_bihimp_commₓ'. -/
theorem bihimp_bihimp_bihimp_comm : a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d) := by
  simp_rw [bihimp_assoc, bihimp_left_comm]
#align bihimp_bihimp_bihimp_comm bihimp_bihimp_bihimp_comm

/- warning: bihimp_bihimp_cancel_left -> bihimp_bihimp_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b)) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b)) b
Case conversion may be inaccurate. Consider using '#align bihimp_bihimp_cancel_left bihimp_bihimp_cancel_leftₓ'. -/
@[simp]
theorem bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b := by simp [← bihimp_assoc]
#align bihimp_bihimp_cancel_left bihimp_bihimp_cancel_left

/- warning: bihimp_bihimp_cancel_right -> bihimp_bihimp_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b a) a) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) b a) a) b
Case conversion may be inaccurate. Consider using '#align bihimp_bihimp_cancel_right bihimp_bihimp_cancel_rightₓ'. -/
@[simp]
theorem bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b := by simp [bihimp_assoc]
#align bihimp_bihimp_cancel_right bihimp_bihimp_cancel_right

/- warning: bihimp_bihimp_self -> bihimp_bihimp_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) a) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) a) b
Case conversion may be inaccurate. Consider using '#align bihimp_bihimp_self bihimp_bihimp_selfₓ'. -/
@[simp]
theorem bihimp_bihimp_self : a ⇔ b ⇔ a = b := by rw [bihimp_comm, bihimp_bihimp_cancel_left]
#align bihimp_bihimp_self bihimp_bihimp_self

/- warning: bihimp_left_involutive -> bihimp_left_involutive is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Involutive.{succ u1} α (fun (_x : α) => bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) _x a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Involutive.{succ u1} α (fun (_x : α) => bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) _x a)
Case conversion may be inaccurate. Consider using '#align bihimp_left_involutive bihimp_left_involutiveₓ'. -/
theorem bihimp_left_involutive (a : α) : Involutive (· ⇔ a) :=
  bihimp_bihimp_cancel_right _
#align bihimp_left_involutive bihimp_left_involutive

/- warning: bihimp_right_involutive -> bihimp_right_involutive is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Involutive.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Involutive.{succ u1} α ((fun (x._@.Mathlib.Order.SymmDiff._hyg.7781 : α) (x._@.Mathlib.Order.SymmDiff._hyg.7783 : α) => bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.7781 x._@.Mathlib.Order.SymmDiff._hyg.7783) a)
Case conversion may be inaccurate. Consider using '#align bihimp_right_involutive bihimp_right_involutiveₓ'. -/
theorem bihimp_right_involutive (a : α) : Involutive ((· ⇔ ·) a) :=
  bihimp_bihimp_cancel_left _
#align bihimp_right_involutive bihimp_right_involutive

/- warning: bihimp_left_injective -> bihimp_left_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Injective.{succ u1, succ u1} α α (fun (_x : α) => bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) _x a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Injective.{succ u1, succ u1} α α (fun (_x : α) => bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) _x a)
Case conversion may be inaccurate. Consider using '#align bihimp_left_injective bihimp_left_injectiveₓ'. -/
theorem bihimp_left_injective (a : α) : Injective (· ⇔ a) :=
  @symmDiff_left_injective αᵒᵈ _ _
#align bihimp_left_injective bihimp_left_injective

/- warning: bihimp_right_injective -> bihimp_right_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Injective.{succ u1, succ u1} α α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Injective.{succ u1, succ u1} α α ((fun (x._@.Mathlib.Order.SymmDiff._hyg.7854 : α) (x._@.Mathlib.Order.SymmDiff._hyg.7856 : α) => bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.7854 x._@.Mathlib.Order.SymmDiff._hyg.7856) a)
Case conversion may be inaccurate. Consider using '#align bihimp_right_injective bihimp_right_injectiveₓ'. -/
theorem bihimp_right_injective (a : α) : Injective ((· ⇔ ·) a) :=
  @symmDiff_right_injective αᵒᵈ _ _
#align bihimp_right_injective bihimp_right_injective

/- warning: bihimp_left_surjective -> bihimp_left_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Surjective.{succ u1, succ u1} α α (fun (_x : α) => bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) _x a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Surjective.{succ u1, succ u1} α α (fun (_x : α) => bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) _x a)
Case conversion may be inaccurate. Consider using '#align bihimp_left_surjective bihimp_left_surjectiveₓ'. -/
theorem bihimp_left_surjective (a : α) : Surjective (· ⇔ a) :=
  @symmDiff_left_surjective αᵒᵈ _ _
#align bihimp_left_surjective bihimp_left_surjective

/- warning: bihimp_right_surjective -> bihimp_right_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Surjective.{succ u1, succ u1} α α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Function.Surjective.{succ u1, succ u1} α α ((fun (x._@.Mathlib.Order.SymmDiff._hyg.7931 : α) (x._@.Mathlib.Order.SymmDiff._hyg.7933 : α) => bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) x._@.Mathlib.Order.SymmDiff._hyg.7931 x._@.Mathlib.Order.SymmDiff._hyg.7933) a)
Case conversion may be inaccurate. Consider using '#align bihimp_right_surjective bihimp_right_surjectiveₓ'. -/
theorem bihimp_right_surjective (a : α) : Surjective ((· ⇔ ·) a) :=
  @symmDiff_right_surjective αᵒᵈ _ _
#align bihimp_right_surjective bihimp_right_surjective

variable {a b c}

/- warning: bihimp_left_inj -> bihimp_left_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) c b)) (Eq.{succ u1} α a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) c b)) (Eq.{succ u1} α a c)
Case conversion may be inaccurate. Consider using '#align bihimp_left_inj bihimp_left_injₓ'. -/
@[simp]
theorem bihimp_left_inj : a ⇔ b = c ⇔ b ↔ a = c :=
  (bihimp_left_injective _).eq_iff
#align bihimp_left_inj bihimp_left_inj

/- warning: bihimp_right_inj -> bihimp_right_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a c)) (Eq.{succ u1} α b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a c)) (Eq.{succ u1} α b c)
Case conversion may be inaccurate. Consider using '#align bihimp_right_inj bihimp_right_injₓ'. -/
@[simp]
theorem bihimp_right_inj : a ⇔ b = a ⇔ c ↔ b = c :=
  (bihimp_right_injective _).eq_iff
#align bihimp_right_inj bihimp_right_inj

/- warning: bihimp_eq_left -> bihimp_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) a) (Eq.{succ u1} α b (Top.top.{u1} α (BooleanAlgebra.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) a) (Eq.{succ u1} α b (Top.top.{u1} α (BooleanAlgebra.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align bihimp_eq_left bihimp_eq_leftₓ'. -/
@[simp]
theorem bihimp_eq_left : a ⇔ b = a ↔ b = ⊤ :=
  @symmDiff_eq_left αᵒᵈ _ _ _
#align bihimp_eq_left bihimp_eq_left

/- warning: bihimp_eq_right -> bihimp_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) b) (Eq.{succ u1} α a (Top.top.{u1} α (BooleanAlgebra.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) b) (Eq.{succ u1} α a (Top.top.{u1} α (BooleanAlgebra.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align bihimp_eq_right bihimp_eq_rightₓ'. -/
@[simp]
theorem bihimp_eq_right : a ⇔ b = b ↔ a = ⊤ :=
  @symmDiff_eq_right αᵒᵈ _ _ _
#align bihimp_eq_right bihimp_eq_right

/- warning: codisjoint.bihimp_left -> Codisjoint.bihimp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) a c) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) b c) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a c) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) b c) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) c)
Case conversion may be inaccurate. Consider using '#align codisjoint.bihimp_left Codisjoint.bihimp_leftₓ'. -/
protected theorem Codisjoint.bihimp_left (ha : Codisjoint a c) (hb : Codisjoint b c) :
    Codisjoint (a ⇔ b) c :=
  (ha.inf_left hb).mono_left inf_le_bihimp
#align codisjoint.bihimp_left Codisjoint.bihimp_left

/- warning: codisjoint.bihimp_right -> Codisjoint.bihimp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) a b) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) a c) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) a (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a b) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a c) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align codisjoint.bihimp_right Codisjoint.bihimp_rightₓ'. -/
protected theorem Codisjoint.bihimp_right (ha : Codisjoint a b) (hb : Codisjoint a c) :
    Codisjoint a (b ⇔ c) :=
  (ha.inf_right hb).mono_right inf_le_bihimp
#align codisjoint.bihimp_right Codisjoint.bihimp_right

end CogeneralizedBooleanAlgebra

/- warning: symm_diff_eq -> symmDiff_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) b (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) a (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) b (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)))
Case conversion may be inaccurate. Consider using '#align symm_diff_eq symmDiff_eqₓ'. -/
theorem symmDiff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ := by simp only [(· ∆ ·), sdiff_eq]
#align symm_diff_eq symmDiff_eq

/- warning: bihimp_eq -> bihimp_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) b (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) a (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) b (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)))
Case conversion may be inaccurate. Consider using '#align bihimp_eq bihimp_eqₓ'. -/
theorem bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ) := by simp only [(· ⇔ ·), himp_eq]
#align bihimp_eq bihimp_eq

/- warning: symm_diff_eq' -> symmDiff_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)))
Case conversion may be inaccurate. Consider using '#align symm_diff_eq' symmDiff_eq'ₓ'. -/
theorem symmDiff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ) := by
  rw [symmDiff_eq_sup_sdiff_inf, sdiff_eq, compl_inf]
#align symm_diff_eq' symmDiff_eq'

/- warning: bihimp_eq' -> bihimp_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)))
Case conversion may be inaccurate. Consider using '#align bihimp_eq' bihimp_eq'ₓ'. -/
theorem bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ :=
  @symmDiff_eq' αᵒᵈ _ _ _
#align bihimp_eq' bihimp_eq'

/- warning: symm_diff_top -> symmDiff_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (Top.top.{u1} α (BooleanAlgebra.toHasTop.{u1} α _inst_1))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a (Top.top.{u1} α (BooleanAlgebra.toTop.{u1} α _inst_1))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align symm_diff_top symmDiff_topₓ'. -/
theorem symmDiff_top : a ∆ ⊤ = aᶜ :=
  symmDiff_top' _
#align symm_diff_top symmDiff_top

/- warning: top_symm_diff -> top_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) (Top.top.{u1} α (BooleanAlgebra.toHasTop.{u1} α _inst_1)) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) (Top.top.{u1} α (BooleanAlgebra.toTop.{u1} α _inst_1)) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align top_symm_diff top_symmDiffₓ'. -/
theorem top_symmDiff : ⊤ ∆ a = aᶜ :=
  top_symmDiff' _
#align top_symm_diff top_symmDiff

/- warning: compl_symm_diff -> compl_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a b)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align compl_symm_diff compl_symmDiffₓ'. -/
@[simp]
theorem compl_symmDiff : (a ∆ b)ᶜ = a ⇔ b := by
  simp_rw [symmDiff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]
#align compl_symm_diff compl_symmDiff

/- warning: compl_bihimp -> compl_bihimp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align compl_bihimp compl_bihimpₓ'. -/
@[simp]
theorem compl_bihimp : (a ⇔ b)ᶜ = a ∆ b :=
  @compl_symmDiff αᵒᵈ _ _ _
#align compl_bihimp compl_bihimp

/- warning: compl_symm_diff_compl -> compl_symmDiff_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align compl_symm_diff_compl compl_symmDiff_complₓ'. -/
@[simp]
theorem compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b :=
  sup_comm.trans <| by simp_rw [compl_sdiff_compl, sdiff_eq, symmDiff_eq]
#align compl_symm_diff_compl compl_symmDiff_compl

/- warning: compl_bihimp_compl -> compl_bihimp_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align compl_bihimp_compl compl_bihimp_complₓ'. -/
@[simp]
theorem compl_bihimp_compl : aᶜ ⇔ bᶜ = a ⇔ b :=
  @compl_symmDiff_compl αᵒᵈ _ _ _
#align compl_bihimp_compl compl_bihimp_compl

/- warning: symm_diff_eq_top -> symmDiff_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (Top.top.{u1} α (BooleanAlgebra.toHasTop.{u1} α _inst_1))) (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (Top.top.{u1} α (BooleanAlgebra.toTop.{u1} α _inst_1))) (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align symm_diff_eq_top symmDiff_eq_topₓ'. -/
@[simp]
theorem symmDiff_eq_top : a ∆ b = ⊤ ↔ IsCompl a b := by
  rw [symmDiff_eq', ← compl_inf, inf_eq_top_iff, compl_eq_top, isCompl_iff, disjoint_iff,
    codisjoint_iff, and_comm]
#align symm_diff_eq_top symmDiff_eq_top

/- warning: bihimp_eq_bot -> bihimp_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (Eq.{succ u1} α (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (Bot.bot.{u1} α (BooleanAlgebra.toHasBot.{u1} α _inst_1))) (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α), Iff (Eq.{succ u1} α (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (Bot.bot.{u1} α (BooleanAlgebra.toBot.{u1} α _inst_1))) (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align bihimp_eq_bot bihimp_eq_botₓ'. -/
@[simp]
theorem bihimp_eq_bot : a ⇔ b = ⊥ ↔ IsCompl a b := by
  rw [bihimp_eq', ← compl_sup, sup_eq_bot_iff, compl_eq_bot, isCompl_iff, disjoint_iff,
    codisjoint_iff]
#align bihimp_eq_bot bihimp_eq_bot

/- warning: compl_symm_diff_self -> compl_symmDiff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) a) (Top.top.{u1} α (BooleanAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) a) (Top.top.{u1} α (BooleanAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align compl_symm_diff_self compl_symmDiff_selfₓ'. -/
@[simp]
theorem compl_symmDiff_self : aᶜ ∆ a = ⊤ :=
  hnot_symmDiff_self _
#align compl_symm_diff_self compl_symmDiff_self

/- warning: symm_diff_compl_self -> symmDiff_compl_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)) (Top.top.{u1} α (BooleanAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a)) (Top.top.{u1} α (BooleanAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align symm_diff_compl_self symmDiff_compl_selfₓ'. -/
@[simp]
theorem symmDiff_compl_self : a ∆ aᶜ = ⊤ :=
  symmDiff_hnot_self _
#align symm_diff_compl_self symmDiff_compl_self

/- warning: symm_diff_symm_diff_right' -> symmDiff_symmDiff_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a b) c) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) a (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) c))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) b) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) c))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) a b) c) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) a (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) c))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) b) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) c))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) a) (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α _inst_1) b)) c))
Case conversion may be inaccurate. Consider using '#align symm_diff_symm_diff_right' symmDiff_symmDiff_right'ₓ'. -/
theorem symmDiff_symmDiff_right' :
    a ∆ (b ∆ c) = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c :=
  calc
    a ∆ (b ∆ c) = a ⊓ (b ⊓ c ⊔ bᶜ ⊓ cᶜ) ⊔ (b ⊓ cᶜ ⊔ c ⊓ bᶜ) ⊓ aᶜ := by
      rw [symmDiff_eq, compl_symmDiff, bihimp_eq', symmDiff_eq]
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ ⊔ c ⊓ bᶜ ⊓ aᶜ := by
      rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc]
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c :=
      by
      congr 1
      · congr 1
        rw [inf_comm, inf_assoc]
      · apply inf_left_right_swap
    
#align symm_diff_symm_diff_right' symmDiff_symmDiff_right'

variable {a b c}

/- warning: disjoint.le_symm_diff_sup_symm_diff_left -> Disjoint.le_symmDiff_sup_symmDiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))))) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) b c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a c) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) b c)))
Case conversion may be inaccurate. Consider using '#align disjoint.le_symm_diff_sup_symm_diff_left Disjoint.le_symmDiff_sup_symmDiff_leftₓ'. -/
theorem Disjoint.le_symmDiff_sup_symmDiff_left (h : Disjoint a b) : c ≤ a ∆ c ⊔ b ∆ c :=
  by
  trans c \ (a ⊓ b)
  · rw [h.eq_bot, sdiff_bot]
  · rw [sdiff_inf]
    exact sup_le_sup le_sup_right le_sup_right
#align disjoint.le_symm_diff_sup_symm_diff_left Disjoint.le_symmDiff_sup_symmDiff_left

/- warning: disjoint.le_symm_diff_sup_symm_diff_right -> Disjoint.le_symmDiff_sup_symmDiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a b) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BooleanAlgebra.toSDiff.{u1} α _inst_1) a c)))
Case conversion may be inaccurate. Consider using '#align disjoint.le_symm_diff_sup_symm_diff_right Disjoint.le_symmDiff_sup_symmDiff_rightₓ'. -/
theorem Disjoint.le_symmDiff_sup_symmDiff_right (h : Disjoint b c) : a ≤ a ∆ b ⊔ a ∆ c :=
  by
  simp_rw [symmDiff_comm a]
  exact h.le_symm_diff_sup_symm_diff_left
#align disjoint.le_symm_diff_sup_symm_diff_right Disjoint.le_symmDiff_sup_symmDiff_right

/- warning: codisjoint.bihimp_inf_bihimp_le_left -> Codisjoint.bihimp_inf_bihimp_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a c) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) b c)) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a c) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) b c)) c)
Case conversion may be inaccurate. Consider using '#align codisjoint.bihimp_inf_bihimp_le_left Codisjoint.bihimp_inf_bihimp_le_leftₓ'. -/
theorem Codisjoint.bihimp_inf_bihimp_le_left (h : Codisjoint a b) : a ⇔ c ⊓ b ⇔ c ≤ c :=
  h.dual.le_symmDiff_sup_symmDiff_left
#align codisjoint.bihimp_inf_bihimp_le_left Codisjoint.bihimp_inf_bihimp_le_left

/- warning: codisjoint.bihimp_inf_bihimp_le_right -> Codisjoint.bihimp_inf_bihimp_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a b) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a c)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BooleanAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a b) (bihimp.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BooleanAlgebra.toHImp.{u1} α _inst_1) a c)) a)
Case conversion may be inaccurate. Consider using '#align codisjoint.bihimp_inf_bihimp_le_right Codisjoint.bihimp_inf_bihimp_le_rightₓ'. -/
theorem Codisjoint.bihimp_inf_bihimp_le_right (h : Codisjoint b c) : a ⇔ b ⊓ a ⇔ c ≤ a :=
  h.dual.le_symmDiff_sup_symmDiff_right
#align codisjoint.bihimp_inf_bihimp_le_right Codisjoint.bihimp_inf_bihimp_le_right

end BooleanAlgebra

/-! ### Prod -/


section Prod

/- warning: symm_diff_fst -> symmDiff_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] [_inst_2 : GeneralizedCoheytingAlgebra.{u2} β] (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (symmDiff.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β _inst_2)))) (Prod.hasSdiff.{u1, u2} α β (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (GeneralizedCoheytingAlgebra.toHasSdiff.{u2} β _inst_2)) a b)) (symmDiff.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (Prod.fst.{u1, u2} α β a) (Prod.fst.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u2} α] [_inst_2 : GeneralizedCoheytingAlgebra.{u1} β] (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (symmDiff.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instHasSupProd.{u2, u1} α β (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (GeneralizedCoheytingAlgebra.toLattice.{u2} α _inst_1))) (SemilatticeSup.toHasSup.{u1} β (Lattice.toSemilatticeSup.{u1} β (GeneralizedCoheytingAlgebra.toLattice.{u1} β _inst_2)))) (Prod.sdiff.{u2, u1} α β (GeneralizedCoheytingAlgebra.toSDiff.{u2} α _inst_1) (GeneralizedCoheytingAlgebra.toSDiff.{u1} β _inst_2)) a b)) (symmDiff.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (GeneralizedCoheytingAlgebra.toLattice.{u2} α _inst_1))) (GeneralizedCoheytingAlgebra.toSDiff.{u2} α _inst_1) (Prod.fst.{u2, u1} α β a) (Prod.fst.{u2, u1} α β b))
Case conversion may be inaccurate. Consider using '#align symm_diff_fst symmDiff_fstₓ'. -/
@[simp]
theorem symmDiff_fst [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β] (a b : α × β) :
    (a ∆ b).1 = a.1 ∆ b.1 :=
  rfl
#align symm_diff_fst symmDiff_fst

/- warning: symm_diff_snd -> symmDiff_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] [_inst_2 : GeneralizedCoheytingAlgebra.{u2} β] (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (symmDiff.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β _inst_2)))) (Prod.hasSdiff.{u1, u2} α β (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (GeneralizedCoheytingAlgebra.toHasSdiff.{u2} β _inst_2)) a b)) (symmDiff.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β _inst_2))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u2} β _inst_2) (Prod.snd.{u1, u2} α β a) (Prod.snd.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u2} α] [_inst_2 : GeneralizedCoheytingAlgebra.{u1} β] (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (symmDiff.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instHasSupProd.{u2, u1} α β (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (GeneralizedCoheytingAlgebra.toLattice.{u2} α _inst_1))) (SemilatticeSup.toHasSup.{u1} β (Lattice.toSemilatticeSup.{u1} β (GeneralizedCoheytingAlgebra.toLattice.{u1} β _inst_2)))) (Prod.sdiff.{u2, u1} α β (GeneralizedCoheytingAlgebra.toSDiff.{u2} α _inst_1) (GeneralizedCoheytingAlgebra.toSDiff.{u1} β _inst_2)) a b)) (symmDiff.{u1} β (SemilatticeSup.toHasSup.{u1} β (Lattice.toSemilatticeSup.{u1} β (GeneralizedCoheytingAlgebra.toLattice.{u1} β _inst_2))) (GeneralizedCoheytingAlgebra.toSDiff.{u1} β _inst_2) (Prod.snd.{u2, u1} α β a) (Prod.snd.{u2, u1} α β b))
Case conversion may be inaccurate. Consider using '#align symm_diff_snd symmDiff_sndₓ'. -/
@[simp]
theorem symmDiff_snd [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β] (a b : α × β) :
    (a ∆ b).2 = a.2 ∆ b.2 :=
  rfl
#align symm_diff_snd symmDiff_snd

/- warning: bihimp_fst -> bihimp_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] [_inst_2 : GeneralizedHeytingAlgebra.{u2} β] (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (bihimp.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β _inst_2)))) (Prod.hasHimp.{u1, u2} α β (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (GeneralizedHeytingAlgebra.toHasHimp.{u2} β _inst_2)) a b)) (bihimp.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (Prod.fst.{u1, u2} α β a) (Prod.fst.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u2} α] [_inst_2 : GeneralizedHeytingAlgebra.{u1} β] (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (bihimp.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instHasInfProd.{u2, u1} α β (Lattice.toHasInf.{u2} α (GeneralizedHeytingAlgebra.toLattice.{u2} α _inst_1)) (Lattice.toHasInf.{u1} β (GeneralizedHeytingAlgebra.toLattice.{u1} β _inst_2))) (Prod.himp.{u2, u1} α β (GeneralizedHeytingAlgebra.toHImp.{u2} α _inst_1) (GeneralizedHeytingAlgebra.toHImp.{u1} β _inst_2)) a b)) (bihimp.{u2} α (Lattice.toHasInf.{u2} α (GeneralizedHeytingAlgebra.toLattice.{u2} α _inst_1)) (GeneralizedHeytingAlgebra.toHImp.{u2} α _inst_1) (Prod.fst.{u2, u1} α β a) (Prod.fst.{u2, u1} α β b))
Case conversion may be inaccurate. Consider using '#align bihimp_fst bihimp_fstₓ'. -/
@[simp]
theorem bihimp_fst [GeneralizedHeytingAlgebra α] [GeneralizedHeytingAlgebra β] (a b : α × β) :
    (a ⇔ b).1 = a.1 ⇔ b.1 :=
  rfl
#align bihimp_fst bihimp_fst

/- warning: bihimp_snd -> bihimp_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] [_inst_2 : GeneralizedHeytingAlgebra.{u2} β] (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (bihimp.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β _inst_2)))) (Prod.hasHimp.{u1, u2} α β (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (GeneralizedHeytingAlgebra.toHasHimp.{u2} β _inst_2)) a b)) (bihimp.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β _inst_2))) (GeneralizedHeytingAlgebra.toHasHimp.{u2} β _inst_2) (Prod.snd.{u1, u2} α β a) (Prod.snd.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u2} α] [_inst_2 : GeneralizedHeytingAlgebra.{u1} β] (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (bihimp.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instHasInfProd.{u2, u1} α β (Lattice.toHasInf.{u2} α (GeneralizedHeytingAlgebra.toLattice.{u2} α _inst_1)) (Lattice.toHasInf.{u1} β (GeneralizedHeytingAlgebra.toLattice.{u1} β _inst_2))) (Prod.himp.{u2, u1} α β (GeneralizedHeytingAlgebra.toHImp.{u2} α _inst_1) (GeneralizedHeytingAlgebra.toHImp.{u1} β _inst_2)) a b)) (bihimp.{u1} β (Lattice.toHasInf.{u1} β (GeneralizedHeytingAlgebra.toLattice.{u1} β _inst_2)) (GeneralizedHeytingAlgebra.toHImp.{u1} β _inst_2) (Prod.snd.{u2, u1} α β a) (Prod.snd.{u2, u1} α β b))
Case conversion may be inaccurate. Consider using '#align bihimp_snd bihimp_sndₓ'. -/
@[simp]
theorem bihimp_snd [GeneralizedHeytingAlgebra α] [GeneralizedHeytingAlgebra β] (a b : α × β) :
    (a ⇔ b).2 = a.2 ⇔ b.2 :=
  rfl
#align bihimp_snd bihimp_snd

end Prod

/-! ### Pi -/


namespace Pi

/- warning: pi.symm_diff_def -> Pi.symmDiff_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), GeneralizedCoheytingAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (b : forall (i : ι), π i), Eq.{succ (max u1 u2)} (forall (i : ι), π i) (symmDiff.{max u1 u2} (forall (i : ι), π i) (Pi.hasSup.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => SemilatticeSup.toHasSup.{u2} (π i) (Lattice.toSemilatticeSup.{u2} (π i) (GeneralizedCoheytingAlgebra.toLattice.{u2} (π i) (_inst_1 i))))) (Pi.sdiff.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => GeneralizedCoheytingAlgebra.toHasSdiff.{u2} (π i) (_inst_1 i))) a b) (fun (i : ι) => symmDiff.{u2} (π i) (SemilatticeSup.toHasSup.{u2} (π i) (Lattice.toSemilatticeSup.{u2} (π i) (GeneralizedCoheytingAlgebra.toLattice.{u2} (π i) (_inst_1 i)))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u2} (π i) (_inst_1 i)) (a i) (b i))
but is expected to have type
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), GeneralizedCoheytingAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (b : forall (i : ι), π i), Eq.{max (succ u1) (succ u2)} (forall (i : ι), π i) (symmDiff.{max u1 u2} (forall (i : ι), π i) (Pi.instHasSupForAll.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => SemilatticeSup.toHasSup.{u2} (π i) (Lattice.toSemilatticeSup.{u2} (π i) (GeneralizedCoheytingAlgebra.toLattice.{u2} (π i) (_inst_1 i))))) (Pi.sdiff.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => GeneralizedCoheytingAlgebra.toSDiff.{u2} (π i) (_inst_1 i))) a b) (fun (i : ι) => symmDiff.{u2} (π i) (SemilatticeSup.toHasSup.{u2} (π i) (Lattice.toSemilatticeSup.{u2} (π i) (GeneralizedCoheytingAlgebra.toLattice.{u2} (π i) (_inst_1 i)))) (GeneralizedCoheytingAlgebra.toSDiff.{u2} (π i) (_inst_1 i)) (a i) (b i))
Case conversion may be inaccurate. Consider using '#align pi.symm_diff_def Pi.symmDiff_defₓ'. -/
theorem symmDiff_def [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ∆ b = fun i => a i ∆ b i :=
  rfl
#align pi.symm_diff_def Pi.symmDiff_def

/- warning: pi.bihimp_def -> Pi.bihimp_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), GeneralizedHeytingAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (b : forall (i : ι), π i), Eq.{succ (max u1 u2)} (forall (i : ι), π i) (bihimp.{max u1 u2} (forall (i : ι), π i) (Pi.hasInf.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => SemilatticeInf.toHasInf.{u2} (π i) (Lattice.toSemilatticeInf.{u2} (π i) (GeneralizedHeytingAlgebra.toLattice.{u2} (π i) (_inst_1 i))))) (Pi.hasHimp.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => GeneralizedHeytingAlgebra.toHasHimp.{u2} (π i) (_inst_1 i))) a b) (fun (i : ι) => bihimp.{u2} (π i) (SemilatticeInf.toHasInf.{u2} (π i) (Lattice.toSemilatticeInf.{u2} (π i) (GeneralizedHeytingAlgebra.toLattice.{u2} (π i) (_inst_1 i)))) (GeneralizedHeytingAlgebra.toHasHimp.{u2} (π i) (_inst_1 i)) (a i) (b i))
but is expected to have type
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), GeneralizedHeytingAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (b : forall (i : ι), π i), Eq.{max (succ u1) (succ u2)} (forall (i : ι), π i) (bihimp.{max u1 u2} (forall (i : ι), π i) (Pi.instHasInfForAll.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => Lattice.toHasInf.{u2} (π i) (GeneralizedHeytingAlgebra.toLattice.{u2} (π i) (_inst_1 i)))) (Pi.instHImpForAll.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => GeneralizedHeytingAlgebra.toHImp.{u2} (π i) (_inst_1 i))) a b) (fun (i : ι) => bihimp.{u2} (π i) (Lattice.toHasInf.{u2} (π i) (GeneralizedHeytingAlgebra.toLattice.{u2} (π i) (_inst_1 i))) (GeneralizedHeytingAlgebra.toHImp.{u2} (π i) (_inst_1 i)) (a i) (b i))
Case conversion may be inaccurate. Consider using '#align pi.bihimp_def Pi.bihimp_defₓ'. -/
theorem bihimp_def [∀ i, GeneralizedHeytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ⇔ b = fun i => a i ⇔ b i :=
  rfl
#align pi.bihimp_def Pi.bihimp_def

/- warning: pi.symm_diff_apply -> Pi.symmDiff_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), GeneralizedCoheytingAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (b : forall (i : ι), π i) (i : ι), Eq.{succ u2} (π i) (symmDiff.{max u1 u2} (forall (i : ι), π i) (Pi.hasSup.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => SemilatticeSup.toHasSup.{u2} (π i) (Lattice.toSemilatticeSup.{u2} (π i) (GeneralizedCoheytingAlgebra.toLattice.{u2} (π i) (_inst_1 i))))) (Pi.sdiff.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => GeneralizedCoheytingAlgebra.toHasSdiff.{u2} (π i) (_inst_1 i))) a b i) (symmDiff.{u2} (π i) (SemilatticeSup.toHasSup.{u2} (π i) (Lattice.toSemilatticeSup.{u2} (π i) (GeneralizedCoheytingAlgebra.toLattice.{u2} (π i) (_inst_1 i)))) (GeneralizedCoheytingAlgebra.toHasSdiff.{u2} (π i) (_inst_1 i)) (a i) (b i))
but is expected to have type
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), GeneralizedCoheytingAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (b : forall (i : ι), π i) (i : ι), Eq.{succ u2} (π i) (symmDiff.{max u1 u2} (forall (i : ι), π i) (Pi.instHasSupForAll.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => SemilatticeSup.toHasSup.{u2} (π i) (Lattice.toSemilatticeSup.{u2} (π i) (GeneralizedCoheytingAlgebra.toLattice.{u2} (π i) (_inst_1 i))))) (Pi.sdiff.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => GeneralizedCoheytingAlgebra.toSDiff.{u2} (π i) (_inst_1 i))) a b i) (symmDiff.{u2} (π i) (SemilatticeSup.toHasSup.{u2} (π i) (Lattice.toSemilatticeSup.{u2} (π i) (GeneralizedCoheytingAlgebra.toLattice.{u2} (π i) (_inst_1 i)))) (GeneralizedCoheytingAlgebra.toSDiff.{u2} (π i) (_inst_1 i)) (a i) (b i))
Case conversion may be inaccurate. Consider using '#align pi.symm_diff_apply Pi.symmDiff_applyₓ'. -/
@[simp]
theorem symmDiff_apply [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ∆ b) i = a i ∆ b i :=
  rfl
#align pi.symm_diff_apply Pi.symmDiff_apply

/- warning: pi.bihimp_apply -> Pi.bihimp_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), GeneralizedHeytingAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (b : forall (i : ι), π i) (i : ι), Eq.{succ u2} (π i) (bihimp.{max u1 u2} (forall (i : ι), π i) (Pi.hasInf.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => SemilatticeInf.toHasInf.{u2} (π i) (Lattice.toSemilatticeInf.{u2} (π i) (GeneralizedHeytingAlgebra.toLattice.{u2} (π i) (_inst_1 i))))) (Pi.hasHimp.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => GeneralizedHeytingAlgebra.toHasHimp.{u2} (π i) (_inst_1 i))) a b i) (bihimp.{u2} (π i) (SemilatticeInf.toHasInf.{u2} (π i) (Lattice.toSemilatticeInf.{u2} (π i) (GeneralizedHeytingAlgebra.toLattice.{u2} (π i) (_inst_1 i)))) (GeneralizedHeytingAlgebra.toHasHimp.{u2} (π i) (_inst_1 i)) (a i) (b i))
but is expected to have type
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), GeneralizedHeytingAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (b : forall (i : ι), π i) (i : ι), Eq.{succ u2} (π i) (bihimp.{max u1 u2} (forall (i : ι), π i) (Pi.instHasInfForAll.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => Lattice.toHasInf.{u2} (π i) (GeneralizedHeytingAlgebra.toLattice.{u2} (π i) (_inst_1 i)))) (Pi.instHImpForAll.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => GeneralizedHeytingAlgebra.toHImp.{u2} (π i) (_inst_1 i))) a b i) (bihimp.{u2} (π i) (Lattice.toHasInf.{u2} (π i) (GeneralizedHeytingAlgebra.toLattice.{u2} (π i) (_inst_1 i))) (GeneralizedHeytingAlgebra.toHImp.{u2} (π i) (_inst_1 i)) (a i) (b i))
Case conversion may be inaccurate. Consider using '#align pi.bihimp_apply Pi.bihimp_applyₓ'. -/
@[simp]
theorem bihimp_apply [∀ i, GeneralizedHeytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ⇔ b) i = a i ⇔ b i :=
  rfl
#align pi.bihimp_apply Pi.bihimp_apply

end Pi

