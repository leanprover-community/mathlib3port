/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Yaël Dillies

! This file was ported from Lean 3 source module order.modular_lattice
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Cover
import Mathbin.Order.LatticeIntervals

/-!
# Modular Lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines (semi)modular lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Typeclasses

We define (semi)modularity typeclasses as Prop-valued mixins.

* `is_weak_upper_modular_lattice`: Weakly upper modular lattices. Lattice where `a ⊔ b` covers `a`
  and `b` if `a` and `b` both cover `a ⊓ b`.
* `is_weak_lower_modular_lattice`: Weakly lower modular lattices. Lattice where `a` and `b` cover
  `a ⊓ b` if `a ⊔ b` covers both `a` and `b`
* `is_upper_modular_lattice`: Upper modular lattices. Lattices where `a ⊔ b` covers `a` if `b`
  covers `a ⊓ b`.
* `is_lower_modular_lattice`: Lower modular lattices. Lattices where `a` covers `a ⊓ b` if `a ⊔ b`
  covers `b`.
- `is_modular_lattice`: Modular lattices. Lattices where `a ≤ c → (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c)`. We
  only require an inequality because the other direction holds in all lattices.

## Main Definitions

- `inf_Icc_order_iso_Icc_sup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results

- `is_modular_lattice_iff_inf_sup_inf_assoc`:
  Modularity is equivalent to the `inf_sup_inf_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `distrib_lattice.is_modular_lattice`: Distributive lattices are modular.

## References

* [Manfred Stern, *Semimodular lattices. {Theory} and applications*][stern2009]
* [Wikipedia, *Modular Lattice*][https://en.wikipedia.org/wiki/Modular_lattice]

## TODO

- Relate atoms and coatoms in modular lattices
-/


open Set

variable {α : Type _}

#print IsWeakUpperModularLattice /-
/-- A weakly upper modular lattice is a lattice where `a ⊔ b` covers `a` and `b` if `a` and `b` both
cover `a ⊓ b`. -/
class IsWeakUpperModularLattice (α : Type _) [Lattice α] : Prop where
  covby_sup_of_inf_covby_covby {a b : α} : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b
#align is_weak_upper_modular_lattice IsWeakUpperModularLattice
-/

#print IsWeakLowerModularLattice /-
/-- A weakly lower modular lattice is a lattice where `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers
both `a` and `b`. -/
class IsWeakLowerModularLattice (α : Type _) [Lattice α] : Prop where
  inf_covby_of_covby_covby_sup {a b : α} : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a
#align is_weak_lower_modular_lattice IsWeakLowerModularLattice
-/

#print IsUpperModularLattice /-
/-- An upper modular lattice, aka semimodular lattice, is a lattice where `a ⊔ b` covers `a` and `b`
if either `a` or `b` covers `a ⊓ b`. -/
class IsUpperModularLattice (α : Type _) [Lattice α] : Prop where
  covby_sup_of_inf_covby {a b : α} : a ⊓ b ⋖ a → b ⋖ a ⊔ b
#align is_upper_modular_lattice IsUpperModularLattice
-/

#print IsLowerModularLattice /-
/-- A lower modular lattice is a lattice where `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers
either `a` or `b`. -/
class IsLowerModularLattice (α : Type _) [Lattice α] : Prop where
  inf_covby_of_covby_sup {a b : α} : a ⋖ a ⊔ b → a ⊓ b ⋖ b
#align is_lower_modular_lattice IsLowerModularLattice
-/

#print IsModularLattice /-
/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class IsModularLattice (α : Type _) [Lattice α] : Prop where
  sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z
#align is_modular_lattice IsModularLattice
-/

section WeakUpperModular

variable [Lattice α] [IsWeakUpperModularLattice α] {a b : α}

#print covby_sup_of_inf_covby_of_inf_covby_left /-
theorem covby_sup_of_inf_covby_of_inf_covby_left : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b :=
  IsWeakUpperModularLattice.covby_sup_of_inf_covby_covby
#align covby_sup_of_inf_covby_of_inf_covby_left covby_sup_of_inf_covby_of_inf_covby_left
-/

#print covby_sup_of_inf_covby_of_inf_covby_right /-
theorem covby_sup_of_inf_covby_of_inf_covby_right : a ⊓ b ⋖ a → a ⊓ b ⋖ b → b ⋖ a ⊔ b :=
  by
  rw [inf_comm, sup_comm]
  exact fun ha hb => covby_sup_of_inf_covby_of_inf_covby_left hb ha
#align covby_sup_of_inf_covby_of_inf_covby_right covby_sup_of_inf_covby_of_inf_covby_right
-/

alias covby_sup_of_inf_covby_of_inf_covby_left ← Covby.sup_of_inf_of_inf_left

alias covby_sup_of_inf_covby_of_inf_covby_right ← Covby.sup_of_inf_of_inf_right

instance : IsWeakLowerModularLattice (OrderDual α) :=
  ⟨fun a b ha hb => (ha.ofDual.sup_of_inf_of_inf_left hb.ofDual).toDual⟩

end WeakUpperModular

section WeakLowerModular

variable [Lattice α] [IsWeakLowerModularLattice α] {a b : α}

#print inf_covby_of_covby_sup_of_covby_sup_left /-
theorem inf_covby_of_covby_sup_of_covby_sup_left : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a :=
  IsWeakLowerModularLattice.inf_covby_of_covby_covby_sup
#align inf_covby_of_covby_sup_of_covby_sup_left inf_covby_of_covby_sup_of_covby_sup_left
-/

#print inf_covby_of_covby_sup_of_covby_sup_right /-
theorem inf_covby_of_covby_sup_of_covby_sup_right : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ b :=
  by
  rw [sup_comm, inf_comm]
  exact fun ha hb => inf_covby_of_covby_sup_of_covby_sup_left hb ha
#align inf_covby_of_covby_sup_of_covby_sup_right inf_covby_of_covby_sup_of_covby_sup_right
-/

alias inf_covby_of_covby_sup_of_covby_sup_left ← Covby.inf_of_sup_of_sup_left

alias inf_covby_of_covby_sup_of_covby_sup_right ← Covby.inf_of_sup_of_sup_right

instance : IsWeakUpperModularLattice (OrderDual α) :=
  ⟨fun a b ha hb => (ha.ofDual.inf_of_sup_of_sup_left hb.ofDual).toDual⟩

end WeakLowerModular

section UpperModular

variable [Lattice α] [IsUpperModularLattice α] {a b : α}

#print covby_sup_of_inf_covby_left /-
theorem covby_sup_of_inf_covby_left : a ⊓ b ⋖ a → b ⋖ a ⊔ b :=
  IsUpperModularLattice.covby_sup_of_inf_covby
#align covby_sup_of_inf_covby_left covby_sup_of_inf_covby_left
-/

#print covby_sup_of_inf_covby_right /-
theorem covby_sup_of_inf_covby_right : a ⊓ b ⋖ b → a ⋖ a ⊔ b :=
  by
  rw [sup_comm, inf_comm]
  exact covby_sup_of_inf_covby_left
#align covby_sup_of_inf_covby_right covby_sup_of_inf_covby_right
-/

alias covby_sup_of_inf_covby_left ← Covby.sup_of_inf_left

alias covby_sup_of_inf_covby_right ← Covby.sup_of_inf_right

#print IsUpperModularLattice.to_isWeakUpperModularLattice /-
-- See note [lower instance priority]
instance (priority := 100) IsUpperModularLattice.to_isWeakUpperModularLattice :
    IsWeakUpperModularLattice α :=
  ⟨fun a b _ => Covby.sup_of_inf_right⟩
#align
  is_upper_modular_lattice.to_is_weak_upper_modular_lattice IsUpperModularLattice.to_isWeakUpperModularLattice
-/

instance : IsLowerModularLattice (OrderDual α) :=
  ⟨fun a b h => h.ofDual.sup_of_inf_left.toDual⟩

end UpperModular

section LowerModular

variable [Lattice α] [IsLowerModularLattice α] {a b : α}

#print inf_covby_of_covby_sup_left /-
theorem inf_covby_of_covby_sup_left : a ⋖ a ⊔ b → a ⊓ b ⋖ b :=
  IsLowerModularLattice.inf_covby_of_covby_sup
#align inf_covby_of_covby_sup_left inf_covby_of_covby_sup_left
-/

#print inf_covby_of_covby_sup_right /-
theorem inf_covby_of_covby_sup_right : b ⋖ a ⊔ b → a ⊓ b ⋖ a :=
  by
  rw [inf_comm, sup_comm]
  exact inf_covby_of_covby_sup_left
#align inf_covby_of_covby_sup_right inf_covby_of_covby_sup_right
-/

alias inf_covby_of_covby_sup_left ← Covby.inf_of_sup_left

alias inf_covby_of_covby_sup_right ← Covby.inf_of_sup_right

#print IsLowerModularLattice.to_isWeakLowerModularLattice /-
-- See note [lower instance priority]
instance (priority := 100) IsLowerModularLattice.to_isWeakLowerModularLattice :
    IsWeakLowerModularLattice α :=
  ⟨fun a b _ => Covby.inf_of_sup_right⟩
#align
  is_lower_modular_lattice.to_is_weak_lower_modular_lattice IsLowerModularLattice.to_isWeakLowerModularLattice
-/

instance : IsUpperModularLattice (OrderDual α) :=
  ⟨fun a b h => h.ofDual.inf_of_sup_left.toDual⟩

end LowerModular

section IsModularLattice

variable [Lattice α] [IsModularLattice α]

#print sup_inf_assoc_of_le /-
theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x ≤ z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z :=
  le_antisymm (IsModularLattice.sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))
#align sup_inf_assoc_of_le sup_inf_assoc_of_le
-/

#print IsModularLattice.inf_sup_inf_assoc /-
theorem IsModularLattice.inf_sup_inf_assoc {x y z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  (sup_inf_assoc_of_le y inf_le_right).symm
#align is_modular_lattice.inf_sup_inf_assoc IsModularLattice.inf_sup_inf_assoc
-/

#print inf_sup_assoc_of_le /-
theorem inf_sup_assoc_of_le {x : α} (y : α) {z : α} (h : z ≤ x) : x ⊓ y ⊔ z = x ⊓ (y ⊔ z) := by
  rw [inf_comm, sup_comm, ← sup_inf_assoc_of_le y h, inf_comm, sup_comm]
#align inf_sup_assoc_of_le inf_sup_assoc_of_le
-/

instance : IsModularLattice αᵒᵈ :=
  ⟨fun x y z xz =>
    le_of_eq
      (by
        rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm]
        exact @sup_inf_assoc_of_le α _ _ _ y _ xz)⟩

variable {x y z : α}

#print IsModularLattice.sup_inf_sup_assoc /-
theorem IsModularLattice.sup_inf_sup_assoc : (x ⊔ z) ⊓ (y ⊔ z) = (x ⊔ z) ⊓ y ⊔ z :=
  @IsModularLattice.inf_sup_inf_assoc αᵒᵈ _ _ _ _ _
#align is_modular_lattice.sup_inf_sup_assoc IsModularLattice.sup_inf_sup_assoc
-/

#print eq_of_le_of_inf_le_of_sup_le /-
theorem eq_of_le_of_inf_le_of_sup_le (hxy : x ≤ y) (hinf : y ⊓ z ≤ x ⊓ z) (hsup : y ⊔ z ≤ x ⊔ z) :
    x = y :=
  le_antisymm hxy <|
    have h : y ≤ x ⊔ z :=
      calc
        y ≤ y ⊔ z := le_sup_left
        _ ≤ x ⊔ z := hsup
        
    calc
      y ≤ (x ⊔ z) ⊓ y := le_inf h le_rfl
      _ = x ⊔ z ⊓ y := sup_inf_assoc_of_le _ hxy
      _ ≤ x ⊔ z ⊓ x := sup_le_sup_left (by rw [inf_comm, @inf_comm _ _ z] <;> exact hinf) _
      _ ≤ x := sup_le le_rfl inf_le_right
      
#align eq_of_le_of_inf_le_of_sup_le eq_of_le_of_inf_le_of_sup_le
-/

#print sup_lt_sup_of_lt_of_inf_le_inf /-
theorem sup_lt_sup_of_lt_of_inf_le_inf (hxy : x < y) (hinf : y ⊓ z ≤ x ⊓ z) : x ⊔ z < y ⊔ z :=
  lt_of_le_of_ne (sup_le_sup_right (le_of_lt hxy) _) fun hsup =>
    ne_of_lt hxy <| eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf (le_of_eq hsup.symm)
#align sup_lt_sup_of_lt_of_inf_le_inf sup_lt_sup_of_lt_of_inf_le_inf
-/

#print inf_lt_inf_of_lt_of_sup_le_sup /-
theorem inf_lt_inf_of_lt_of_sup_le_sup (hxy : x < y) (hinf : y ⊔ z ≤ x ⊔ z) : x ⊓ z < y ⊓ z :=
  @sup_lt_sup_of_lt_of_inf_le_inf αᵒᵈ _ _ _ _ _ hxy hinf
#align inf_lt_inf_of_lt_of_sup_le_sup inf_lt_inf_of_lt_of_sup_le_sup
-/

/- warning: well_founded_lt_exact_sequence -> wellFounded_lt_exact_sequence is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α _inst_1] {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : PartialOrder.{u2} β] [_inst_4 : Preorder.{u3} γ], (WellFounded.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_3)))) -> (WellFounded.{succ u3} γ (LT.lt.{u3} γ (Preorder.toLT.{u3} γ _inst_4))) -> (forall (K : α) (f₁ : β -> α) (f₂ : α -> β) (g₁ : γ -> α) (g₂ : α -> γ), (GaloisCoinsertion.{u2, u1} β α (PartialOrder.toPreorder.{u2} β _inst_3) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) f₁ f₂) -> (GaloisInsertion.{u1, u3} α γ (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) _inst_4 g₂ g₁) -> (forall (a : α), Eq.{succ u1} α (f₁ (f₂ a)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a K)) -> (forall (a : α), Eq.{succ u1} α (g₁ (g₂ a)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a K)) -> (WellFounded.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α _inst_1] {β : Type.{u3}} {γ : Type.{u2}} [_inst_3 : PartialOrder.{u3} β] [_inst_4 : Preorder.{u2} γ], (WellFounded.{succ u3} β (fun (x._@.Mathlib.Order.ModularLattice._hyg.1560 : β) (x._@.Mathlib.Order.ModularLattice._hyg.1562 : β) => LT.lt.{u3} β (Preorder.toLT.{u3} β (PartialOrder.toPreorder.{u3} β _inst_3)) x._@.Mathlib.Order.ModularLattice._hyg.1560 x._@.Mathlib.Order.ModularLattice._hyg.1562)) -> (WellFounded.{succ u2} γ (fun (x._@.Mathlib.Order.ModularLattice._hyg.1583 : γ) (x._@.Mathlib.Order.ModularLattice._hyg.1585 : γ) => LT.lt.{u2} γ (Preorder.toLT.{u2} γ _inst_4) x._@.Mathlib.Order.ModularLattice._hyg.1583 x._@.Mathlib.Order.ModularLattice._hyg.1585)) -> (forall (K : α) (f₁ : β -> α) (f₂ : α -> β) (g₁ : γ -> α) (g₂ : α -> γ), (GaloisCoinsertion.{u3, u1} β α (PartialOrder.toPreorder.{u3} β _inst_3) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) f₁ f₂) -> (GaloisInsertion.{u1, u2} α γ (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) _inst_4 g₂ g₁) -> (forall (a : α), Eq.{succ u1} α (f₁ (f₂ a)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a K)) -> (forall (a : α), Eq.{succ u1} α (g₁ (g₂ a)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a K)) -> (WellFounded.{succ u1} α (fun (x._@.Mathlib.Order.ModularLattice._hyg.1659 : α) (x._@.Mathlib.Order.ModularLattice._hyg.1661 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.ModularLattice._hyg.1659 x._@.Mathlib.Order.ModularLattice._hyg.1661)))
Case conversion may be inaccurate. Consider using '#align well_founded_lt_exact_sequence wellFounded_lt_exact_sequenceₓ'. -/
/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Artinian, then `M` is Artinian. -/
theorem wellFounded_lt_exact_sequence {β γ : Type _} [PartialOrder β] [Preorder γ]
    (h₁ : WellFounded ((· < ·) : β → β → Prop)) (h₂ : WellFounded ((· < ·) : γ → γ → Prop)) (K : α)
    (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : ∀ a, f₁ (f₂ a) = a ⊓ K) (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
    WellFounded ((· < ·) : α → α → Prop) :=
  Subrelation.wf
    (fun A B hAB =>
      show Prod.Lex (· < ·) (· < ·) (f₂ A, g₂ A) (f₂ B, g₂ B)
        by
        simp only [Prod.lex_def, lt_iff_le_not_le, ← gci.l_le_l_iff, ← gi.u_le_u_iff, hf, hg,
          le_antisymm_iff]
        simp only [gci.l_le_l_iff, gi.u_le_u_iff, ← lt_iff_le_not_le, ← le_antisymm_iff]
        cases' lt_or_eq_of_le (inf_le_inf_right K (le_of_lt hAB)) with h h
        · exact Or.inl h
        · exact Or.inr ⟨h, sup_lt_sup_of_lt_of_inf_le_inf hAB (le_of_eq h.symm)⟩)
    (InvImage.wf _ (Prod.lex_wf h₁ h₂))
#align well_founded_lt_exact_sequence wellFounded_lt_exact_sequence

/- warning: well_founded_gt_exact_sequence -> wellFounded_gt_exact_sequence is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α _inst_1] {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : Preorder.{u2} β] [_inst_4 : PartialOrder.{u3} γ], (WellFounded.{succ u2} β (GT.gt.{u2} β (Preorder.toLT.{u2} β _inst_3))) -> (WellFounded.{succ u3} γ (GT.gt.{u3} γ (Preorder.toLT.{u3} γ (PartialOrder.toPreorder.{u3} γ _inst_4)))) -> (forall (K : α) (f₁ : β -> α) (f₂ : α -> β) (g₁ : γ -> α) (g₂ : α -> γ), (GaloisCoinsertion.{u2, u1} β α _inst_3 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) f₁ f₂) -> (GaloisInsertion.{u1, u3} α γ (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u3} γ _inst_4) g₂ g₁) -> (forall (a : α), Eq.{succ u1} α (f₁ (f₂ a)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a K)) -> (forall (a : α), Eq.{succ u1} α (g₁ (g₂ a)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a K)) -> (WellFounded.{succ u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α _inst_1] {β : Type.{u3}} {γ : Type.{u2}} [_inst_3 : Preorder.{u3} β] [_inst_4 : PartialOrder.{u2} γ], (WellFounded.{succ u3} β (fun (x._@.Mathlib.Order.ModularLattice._hyg.1820 : β) (x._@.Mathlib.Order.ModularLattice._hyg.1822 : β) => GT.gt.{u3} β (Preorder.toLT.{u3} β _inst_3) x._@.Mathlib.Order.ModularLattice._hyg.1820 x._@.Mathlib.Order.ModularLattice._hyg.1822)) -> (WellFounded.{succ u2} γ (fun (x._@.Mathlib.Order.ModularLattice._hyg.1843 : γ) (x._@.Mathlib.Order.ModularLattice._hyg.1845 : γ) => GT.gt.{u2} γ (Preorder.toLT.{u2} γ (PartialOrder.toPreorder.{u2} γ _inst_4)) x._@.Mathlib.Order.ModularLattice._hyg.1843 x._@.Mathlib.Order.ModularLattice._hyg.1845)) -> (forall (K : α) (f₁ : β -> α) (f₂ : α -> β) (g₁ : γ -> α) (g₂ : α -> γ), (GaloisCoinsertion.{u3, u1} β α _inst_3 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) f₁ f₂) -> (GaloisInsertion.{u1, u2} α γ (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} γ _inst_4) g₂ g₁) -> (forall (a : α), Eq.{succ u1} α (f₁ (f₂ a)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a K)) -> (forall (a : α), Eq.{succ u1} α (g₁ (g₂ a)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a K)) -> (WellFounded.{succ u1} α (fun (x._@.Mathlib.Order.ModularLattice._hyg.1919 : α) (x._@.Mathlib.Order.ModularLattice._hyg.1921 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.ModularLattice._hyg.1919 x._@.Mathlib.Order.ModularLattice._hyg.1921)))
Case conversion may be inaccurate. Consider using '#align well_founded_gt_exact_sequence wellFounded_gt_exact_sequenceₓ'. -/
/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Noetherian, then `M` is Noetherian.  -/
theorem wellFounded_gt_exact_sequence {β γ : Type _} [Preorder β] [PartialOrder γ]
    (h₁ : WellFounded ((· > ·) : β → β → Prop)) (h₂ : WellFounded ((· > ·) : γ → γ → Prop)) (K : α)
    (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : ∀ a, f₁ (f₂ a) = a ⊓ K) (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
    WellFounded ((· > ·) : α → α → Prop) :=
  @wellFounded_lt_exact_sequence αᵒᵈ _ _ γᵒᵈ βᵒᵈ _ _ h₂ h₁ K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf
#align well_founded_gt_exact_sequence wellFounded_gt_exact_sequence

#print infIccOrderIsoIccSup /-
/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
@[simps]
def infIccOrderIsoIccSup (a b : α) : Set.Icc (a ⊓ b) a ≃o Set.Icc b (a ⊔ b)
    where
  toFun x := ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.Prop.2 b⟩⟩
  invFun x := ⟨a ⊓ x, ⟨inf_le_inf_left a x.Prop.1, inf_le_left⟩⟩
  left_inv x :=
    Subtype.ext
      (by
        change a ⊓ (↑x ⊔ b) = ↑x
        rw [sup_comm, ← inf_sup_assoc_of_le _ x.prop.2, sup_eq_right.2 x.prop.1])
  right_inv x :=
    Subtype.ext
      (by
        change a ⊓ ↑x ⊔ b = ↑x
        rw [inf_comm, inf_sup_assoc_of_le _ x.prop.1, inf_eq_left.2 x.prop.2])
  map_rel_iff' x y :=
    by
    simp only [Subtype.mk_le_mk, Equiv.coe_fn_mk, and_true_iff, le_sup_right]
    rw [← Subtype.coe_le_coe]
    refine' ⟨fun h => _, fun h => sup_le_sup_right h _⟩
    rw [← sup_eq_right.2 x.prop.1, inf_sup_assoc_of_le _ x.prop.2, sup_comm, ←
      sup_eq_right.2 y.prop.1, inf_sup_assoc_of_le _ y.prop.2, @sup_comm _ _ b]
    exact inf_le_inf_left _ h
#align inf_Icc_order_iso_Icc_sup infIccOrderIsoIccSup
-/

#print inf_strictMonoOn_Icc_sup /-
theorem inf_strictMonoOn_Icc_sup {a b : α} : StrictMonoOn (fun c => a ⊓ c) (Icc b (a ⊔ b)) :=
  StrictMono.of_restrict (infIccOrderIsoIccSup a b).symm.StrictMono
#align inf_strict_mono_on_Icc_sup inf_strictMonoOn_Icc_sup
-/

#print sup_strictMonoOn_Icc_inf /-
theorem sup_strictMonoOn_Icc_inf {a b : α} : StrictMonoOn (fun c => c ⊔ b) (Icc (a ⊓ b) a) :=
  StrictMono.of_restrict (infIccOrderIsoIccSup a b).StrictMono
#align sup_strict_mono_on_Icc_inf sup_strictMonoOn_Icc_inf
-/

#print infIooOrderIsoIooSup /-
/-- The diamond isomorphism between the intervals `]a ⊓ b, a[` and `}b, a ⊔ b[`. -/
@[simps]
def infIooOrderIsoIooSup (a b : α) : Ioo (a ⊓ b) a ≃o Ioo b (a ⊔ b)
    where
  toFun c :=
    ⟨c ⊔ b,
      le_sup_right.trans_lt <|
        sup_strictMonoOn_Icc_inf (left_mem_Icc.2 inf_le_left) (Ioo_subset_Icc_self c.2) c.2.1,
      sup_strictMonoOn_Icc_inf (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 inf_le_left) c.2.2⟩
  invFun c :=
    ⟨a ⊓ c, inf_strictMonoOn_Icc_sup (left_mem_Icc.2 le_sup_right) (Ioo_subset_Icc_self c.2) c.2.1,
      inf_le_left.trans_lt' <|
        inf_strictMonoOn_Icc_sup (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 le_sup_right) c.2.2⟩
  left_inv c :=
    Subtype.ext <| by
      dsimp
      rw [sup_comm, ← inf_sup_assoc_of_le _ c.prop.2.le, sup_eq_right.2 c.prop.1.le]
  right_inv c :=
    Subtype.ext <| by
      dsimp
      rw [inf_comm, inf_sup_assoc_of_le _ c.prop.1.le, inf_eq_left.2 c.prop.2.le]
  map_rel_iff' c d :=
    @OrderIso.le_iff_le _ _ _ _ (infIccOrderIsoIccSup _ _) ⟨c.1, Ioo_subset_Icc_self c.2⟩
      ⟨d.1, Ioo_subset_Icc_self d.2⟩
#align inf_Ioo_order_iso_Ioo_sup infIooOrderIsoIooSup
-/

#print IsModularLattice.to_isLowerModularLattice /-
-- See note [lower instance priority]
instance (priority := 100) IsModularLattice.to_isLowerModularLattice : IsLowerModularLattice α :=
  ⟨fun a b =>
    by
    simp_rw [covby_iff_Ioo_eq, @sup_comm _ _ a, @inf_comm _ _ a, ← is_empty_coe_sort, right_lt_sup,
      inf_lt_left, (infIooOrderIsoIooSup _ _).symm.toEquiv.is_empty_congr]
    exact id⟩
#align is_modular_lattice.to_is_lower_modular_lattice IsModularLattice.to_isLowerModularLattice
-/

#print IsModularLattice.to_isUpperModularLattice /-
-- See note [lower instance priority]
instance (priority := 100) IsModularLattice.to_isUpperModularLattice : IsUpperModularLattice α :=
  ⟨fun a b =>
    by
    simp_rw [covby_iff_Ioo_eq, ← is_empty_coe_sort, right_lt_sup, inf_lt_left,
      (infIooOrderIsoIooSup _ _).toEquiv.is_empty_congr]
    exact id⟩
#align is_modular_lattice.to_is_upper_modular_lattice IsModularLattice.to_isUpperModularLattice
-/

end IsModularLattice

namespace IsCompl

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

#print IsCompl.IicOrderIsoIci /-
/-- The diamond isomorphism between the intervals `set.Iic a` and `set.Ici b`. -/
def IicOrderIsoIci {a b : α} (h : IsCompl a b) : Set.Iic a ≃o Set.Ici b :=
  (OrderIso.setCongr (Set.Iic a) (Set.Icc (a ⊓ b) a)
        (h.inf_eq_bot.symm ▸ Set.Icc_bot.symm)).trans <|
    (infIccOrderIsoIccSup a b).trans
      (OrderIso.setCongr (Set.Icc b (a ⊔ b)) (Set.Ici b) (h.sup_eq_top.symm ▸ Set.Icc_top))
#align is_compl.Iic_order_iso_Ici IsCompl.IicOrderIsoIci
-/

end IsCompl

#print isModularLattice_iff_inf_sup_inf_assoc /-
theorem isModularLattice_iff_inf_sup_inf_assoc [Lattice α] :
    IsModularLattice α ↔ ∀ x y z : α, x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  ⟨fun h => @IsModularLattice.inf_sup_inf_assoc _ _ h, fun h =>
    ⟨fun x y z xz => by rw [← inf_eq_left.2 xz, h]⟩⟩
#align is_modular_lattice_iff_inf_sup_inf_assoc isModularLattice_iff_inf_sup_inf_assoc
-/

namespace DistribLattice

instance (priority := 100) [DistribLattice α] : IsModularLattice α :=
  ⟨fun x y z xz => by rw [inf_sup_right, inf_eq_left.2 xz]⟩

end DistribLattice

#print Disjoint.disjoint_sup_right_of_disjoint_sup_left /-
theorem Disjoint.disjoint_sup_right_of_disjoint_sup_left [Lattice α] [OrderBot α]
    [IsModularLattice α] {a b c : α} (h : Disjoint a b) (hsup : Disjoint (a ⊔ b) c) :
    Disjoint a (b ⊔ c) := by
  rw [disjoint_iff_inf_le, ← h.eq_bot, sup_comm]
  apply le_inf inf_le_left
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans
  rw [sup_comm, IsModularLattice.sup_inf_sup_assoc, hsup.eq_bot, bot_sup_eq]
#align
  disjoint.disjoint_sup_right_of_disjoint_sup_left Disjoint.disjoint_sup_right_of_disjoint_sup_left
-/

#print Disjoint.disjoint_sup_left_of_disjoint_sup_right /-
theorem Disjoint.disjoint_sup_left_of_disjoint_sup_right [Lattice α] [OrderBot α]
    [IsModularLattice α] {a b c : α} (h : Disjoint b c) (hsup : Disjoint a (b ⊔ c)) :
    Disjoint (a ⊔ b) c := by
  rw [Disjoint.comm, sup_comm]
  apply Disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm
  rwa [sup_comm, Disjoint.comm] at hsup
#align
  disjoint.disjoint_sup_left_of_disjoint_sup_right Disjoint.disjoint_sup_left_of_disjoint_sup_right
-/

namespace IsModularLattice

variable [Lattice α] [IsModularLattice α] {a : α}

/- warning: is_modular_lattice.is_modular_lattice_Iic -> IsModularLattice.isModularLattice_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α _inst_1] {a : α}, IsModularLattice.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) a)) (Set.Iic.lattice.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α _inst_1] {a : α}, IsModularLattice.{u1} (Set.Elem.{u1} α (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) a)) (Set.Iic.instLatticeElemIicToPreorderToPartialOrderToSemilatticeInf.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align is_modular_lattice.is_modular_lattice_Iic IsModularLattice.isModularLattice_Iicₓ'. -/
instance isModularLattice_Iic : IsModularLattice (Set.Iic a) :=
  ⟨fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩
#align is_modular_lattice.is_modular_lattice_Iic IsModularLattice.isModularLattice_Iic

#print IsModularLattice.isModularLattice_Ici /-
instance isModularLattice_Ici : IsModularLattice (Set.Ici a) :=
  ⟨fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩
#align is_modular_lattice.is_modular_lattice_Ici IsModularLattice.isModularLattice_Ici
-/

section ComplementedLattice

variable [BoundedOrder α] [ComplementedLattice α]

/- warning: is_modular_lattice.complemented_lattice_Iic -> IsModularLattice.complementedLattice_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α _inst_1] {a : α} [_inst_3 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] [_inst_4 : ComplementedLattice.{u1} α _inst_1 _inst_3], ComplementedLattice.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) a)) (Set.Iic.lattice.{u1} α _inst_1 a) (Set.Iic.boundedOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) _inst_3) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α _inst_1] {a : α} [_inst_3 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] [_inst_4 : ComplementedLattice.{u1} α _inst_1 _inst_3], ComplementedLattice.{u1} (Set.Elem.{u1} α (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) a)) (Set.Iic.instLatticeElemIicToPreorderToPartialOrderToSemilatticeInf.{u1} α _inst_1 a) (Set.Iic.instBoundedOrderElemIicLeToLEMemSetInstMembershipSet.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) _inst_3) a)
Case conversion may be inaccurate. Consider using '#align is_modular_lattice.complemented_lattice_Iic IsModularLattice.complementedLattice_Iicₓ'. -/
instance complementedLattice_Iic : ComplementedLattice (Set.Iic a) :=
  ⟨fun ⟨x, hx⟩ =>
    let ⟨y, hy⟩ := exists_is_compl x
    ⟨⟨y ⊓ a, Set.mem_Iic.2 inf_le_right⟩, by
      constructor
      · rw [disjoint_iff_inf_le]
        change x ⊓ (y ⊓ a) ≤ ⊥
        -- improve lattice subtype API
        rw [← inf_assoc]
        exact le_trans inf_le_left hy.1.le_bot
      · rw [codisjoint_iff_le_sup]
        change a ≤ x ⊔ y ⊓ a
        -- improve lattice subtype API
        rw [← sup_inf_assoc_of_le _ (Set.mem_Iic.1 hx), hy.2.eq_top, top_inf_eq]⟩⟩
#align is_modular_lattice.complemented_lattice_Iic IsModularLattice.complementedLattice_Iic

#print IsModularLattice.complementedLattice_Ici /-
instance complementedLattice_Ici : ComplementedLattice (Set.Ici a) :=
  ⟨fun ⟨x, hx⟩ =>
    let ⟨y, hy⟩ := exists_is_compl x
    ⟨⟨y ⊔ a, Set.mem_Ici.2 le_sup_right⟩, by
      constructor
      · rw [disjoint_iff_inf_le]
        change x ⊓ (y ⊔ a) ≤ a
        -- improve lattice subtype API
        rw [← inf_sup_assoc_of_le _ (Set.mem_Ici.1 hx), hy.1.eq_bot, bot_sup_eq]
      · rw [codisjoint_iff_le_sup]
        change ⊤ ≤ x ⊔ (y ⊔ a)
        -- improve lattice subtype API
        rw [← sup_assoc]
        exact le_trans hy.2.top_le le_sup_left⟩⟩
#align is_modular_lattice.complemented_lattice_Ici IsModularLattice.complementedLattice_Ici
-/

end ComplementedLattice

end IsModularLattice

