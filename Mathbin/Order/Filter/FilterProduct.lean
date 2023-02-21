/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.filter_product
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Ultrafilter
import Mathbin.Order.Filter.Germ

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `order.filter.germ`.

## Tags

ultrafilter, ultraproduct
-/


universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

open Classical

namespace Filter

-- mathport name: «expr∀* , »
local notation3"∀* "(...)", "r:(scoped p => Filter.Eventually p φ) => r

namespace Germ

open Ultrafilter

-- mathport name: «exprβ*»
local notation "β*" => Germ (φ : Filter α) β

instance [DivisionSemiring β] : DivisionSemiring β* :=
  { Germ.semiring, Germ.divInvMonoid,
    Germ.nontrivial with
    mul_inv_cancel := fun f =>
      inductionOn f fun f hf =>
        coe_eq.2 <|
          (φ.em fun y => f y = 0).elim (fun H => (hf <| coe_eq.2 H).elim) fun H =>
            H.mono fun x => mul_inv_cancel
    inv_zero := coe_eq.2 <| by simp only [(· ∘ ·), inv_zero] }

instance [DivisionRing β] : DivisionRing β* :=
  { Germ.ring, Germ.divisionSemiring with }

instance [Semifield β] : Semifield β* :=
  { Germ.commSemiring, Germ.divisionSemiring with }

instance [Field β] : Field β* :=
  { Germ.commRing, Germ.divisionRing with }

#print Filter.Germ.coe_lt /-
theorem coe_lt [Preorder β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x := by
  simp only [lt_iff_le_not_le, eventually_and, coe_le, eventually_not, eventually_le]
#align filter.germ.coe_lt Filter.Germ.coe_lt
-/

#print Filter.Germ.coe_pos /-
theorem coe_pos [Preorder β] [Zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x :=
  coe_lt
#align filter.germ.coe_pos Filter.Germ.coe_pos
-/

#print Filter.Germ.const_lt /-
theorem const_lt [Preorder β] {x y : β} : x < y → (↑x : β*) < ↑y :=
  coe_lt.mpr ∘ liftRel_const
#align filter.germ.const_lt Filter.Germ.const_lt
-/

#print Filter.Germ.const_lt_iff /-
@[simp, norm_cast]
theorem const_lt_iff [Preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
  coe_lt.trans liftRel_const_iff
#align filter.germ.const_lt_iff Filter.Germ.const_lt_iff
-/

#print Filter.Germ.lt_def /-
theorem lt_def [Preorder β] : ((· < ·) : β* → β* → Prop) = LiftRel (· < ·) :=
  by
  ext (⟨f⟩⟨g⟩)
  exact coe_lt
#align filter.germ.lt_def Filter.Germ.lt_def
-/

instance [HasSup β] : HasSup β* :=
  ⟨map₂ (· ⊔ ·)⟩

instance [HasInf β] : HasInf β* :=
  ⟨map₂ (· ⊓ ·)⟩

#print Filter.Germ.const_sup /-
@[simp, norm_cast]
theorem const_sup [HasSup β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : β*) :=
  rfl
#align filter.germ.const_sup Filter.Germ.const_sup
-/

#print Filter.Germ.const_inf /-
@[simp, norm_cast]
theorem const_inf [HasInf β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : β*) :=
  rfl
#align filter.germ.const_inf Filter.Germ.const_inf
-/

instance [SemilatticeSup β] : SemilatticeSup β* :=
  { Germ.partialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun f g => inductionOn₂ f g fun f g => eventually_of_forall fun x => le_sup_left
    le_sup_right := fun f g =>
      inductionOn₂ f g fun f g => eventually_of_forall fun x => le_sup_right
    sup_le := fun f₁ f₂ g =>
      inductionOn₃ f₁ f₂ g fun f₁ f₂ g h₁ h₂ => h₂.mp <| h₁.mono fun x => sup_le }

instance [SemilatticeInf β] : SemilatticeInf β* :=
  { Germ.partialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun f g => inductionOn₂ f g fun f g => eventually_of_forall fun x => inf_le_left
    inf_le_right := fun f g =>
      inductionOn₂ f g fun f g => eventually_of_forall fun x => inf_le_right
    le_inf := fun f₁ f₂ g =>
      inductionOn₃ f₁ f₂ g fun f₁ f₂ g h₁ h₂ => h₂.mp <| h₁.mono fun x => le_inf }

instance [Lattice β] : Lattice β* :=
  { Germ.semilatticeSup, Germ.semilatticeInf with }

instance [DistribLattice β] : DistribLattice β* :=
  { Germ.semilatticeSup, Germ.semilatticeInf with
    le_sup_inf := fun f g h =>
      inductionOn₃ f g h fun f g h => eventually_of_forall fun _ => le_sup_inf }

instance [LE β] [IsTotal β (· ≤ ·)] : IsTotal β* (· ≤ ·) :=
  ⟨fun f g =>
    inductionOn₂ f g fun f g => eventually_or.1 <| eventually_of_forall fun x => total_of _ _ _⟩

/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
noncomputable instance [LinearOrder β] : LinearOrder β* :=
  Lattice.toLinearOrder _

@[to_additive]
instance [OrderedCommMonoid β] : OrderedCommMonoid β* :=
  { Germ.partialOrder, Germ.commMonoid with
    mul_le_mul_left := fun f g =>
      inductionOn₂ f g fun f g H h =>
        inductionOn h fun h => H.mono fun x H => mul_le_mul_left' H _ }

@[to_additive]
instance [OrderedCancelCommMonoid β] : OrderedCancelCommMonoid β* :=
  { Germ.partialOrder, Germ.orderedCommMonoid with
    le_of_mul_le_mul_left := fun f g h =>
      inductionOn₃ f g h fun f g h H => H.mono fun x => le_of_mul_le_mul_left' }

@[to_additive]
instance [OrderedCommGroup β] : OrderedCommGroup β* :=
  { Germ.orderedCancelCommMonoid, Germ.commGroup with }

@[to_additive]
noncomputable instance [LinearOrderedCommGroup β] : LinearOrderedCommGroup β* :=
  { Germ.orderedCommGroup, Germ.linearOrder with }

instance [OrderedSemiring β] : OrderedSemiring β* :=
  { Germ.semiring,
    Germ.orderedAddCommMonoid with
    zero_le_one := const_le zero_le_one
    mul_le_mul_of_nonneg_left := fun x y z =>
      inductionOn₃ x y z fun f g h hfg hh => hh.mp <| hfg.mono fun a => mul_le_mul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun x y z =>
      inductionOn₃ x y z fun f g h hfg hh => hh.mp <| hfg.mono fun a => mul_le_mul_of_nonneg_right }

instance [OrderedCommSemiring β] : OrderedCommSemiring β* :=
  { Germ.orderedSemiring, Germ.commSemiring with }

instance [OrderedRing β] : OrderedRing β* :=
  { Germ.ring,
    Germ.orderedAddCommGroup with
    zero_le_one := const_le zero_le_one
    mul_nonneg := fun x y =>
      inductionOn₂ x y fun f g hf hg => hg.mp <| hf.mono fun a => mul_nonneg }

instance [OrderedCommRing β] : OrderedCommRing β* :=
  { Germ.orderedRing, Germ.orderedCommSemiring with }

instance [StrictOrderedSemiring β] : StrictOrderedSemiring β* :=
  { Germ.orderedSemiring, Germ.orderedCancelAddCommMonoid,
    Germ.nontrivial with
    mul_lt_mul_of_pos_left := fun x y z =>
      inductionOn₃ x y z fun f g h hfg hh =>
        coe_lt.2 <| (coe_lt.1 hh).mp <| (coe_lt.1 hfg).mono fun a => mul_lt_mul_of_pos_left
    mul_lt_mul_of_pos_right := fun x y z =>
      inductionOn₃ x y z fun f g h hfg hh =>
        coe_lt.2 <| (coe_lt.1 hh).mp <| (coe_lt.1 hfg).mono fun a => mul_lt_mul_of_pos_right }

instance [StrictOrderedCommSemiring β] : StrictOrderedCommSemiring β* :=
  { Germ.strictOrderedSemiring, Germ.orderedCommSemiring with }

instance [StrictOrderedRing β] : StrictOrderedRing β* :=
  { Germ.ring,
    Germ.strictOrderedSemiring with
    zero_le_one := const_le zero_le_one
    mul_pos := fun x y =>
      inductionOn₂ x y fun f g hf hg =>
        coe_pos.2 <| (coe_pos.1 hg).mp <| (coe_pos.1 hf).mono fun x => mul_pos }

instance [StrictOrderedCommRing β] : StrictOrderedCommRing β* :=
  { Germ.strictOrderedRing, Germ.orderedCommRing with }

noncomputable instance [LinearOrderedRing β] : LinearOrderedRing β* :=
  { Germ.strictOrderedRing, Germ.linearOrder with }

noncomputable instance [LinearOrderedField β] : LinearOrderedField β* :=
  { Germ.linearOrderedRing, Germ.field with }

noncomputable instance [LinearOrderedCommRing β] : LinearOrderedCommRing β* :=
  { Germ.linearOrderedRing, Germ.commMonoid with }

/- warning: filter.germ.max_def -> Filter.Germ.max_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrder.{u2} β] (x : Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (y : Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (LinearOrder.max.{max u1 u2} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.linearOrder.{u1, u2} α β φ _inst_1) x y) (Filter.Germ.map₂.{u1, u2, u2, u2} α β β β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) (LinearOrder.max.{u2} β _inst_1) x y)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrder.{u2} β] (x : Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (y : Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Max.max.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (LinearOrder.toMax.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.linearOrder.{u1, u2} α β φ _inst_1)) x y) (Filter.Germ.map₂.{u1, u2, u2, u2} α β β β (Ultrafilter.toFilter.{u1} α φ) (Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_1)) x y)
Case conversion may be inaccurate. Consider using '#align filter.germ.max_def Filter.Germ.max_defₓ'. -/
theorem max_def [LinearOrder β] (x y : β*) : max x y = map₂ max x y :=
  inductionOn₂ x y fun a b => by
    cases le_total (a : β*) b
    · rw [max_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_right hi).symm
    · rw [max_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_left hi).symm
#align filter.germ.max_def Filter.Germ.max_def

/- warning: filter.germ.min_def -> Filter.Germ.min_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [K : LinearOrder.{u2} β] (x : Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (y : Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (LinearOrder.min.{max u1 u2} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.linearOrder.{u1, u2} α β φ K) x y) (Filter.Germ.map₂.{u1, u2, u2, u2} α β β β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) (LinearOrder.min.{u2} β K) x y)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [K : LinearOrder.{u2} β] (x : Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (y : Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Min.min.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (LinearOrder.toMin.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.linearOrder.{u1, u2} α β φ K)) x y) (Filter.Germ.map₂.{u1, u2, u2, u2} α β β β (Ultrafilter.toFilter.{u1} α φ) (Min.min.{u2} β (LinearOrder.toMin.{u2} β K)) x y)
Case conversion may be inaccurate. Consider using '#align filter.germ.min_def Filter.Germ.min_defₓ'. -/
theorem min_def [K : LinearOrder β] (x y : β*) : min x y = map₂ min x y :=
  inductionOn₂ x y fun a b => by
    cases le_total (a : β*) b
    · rw [min_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_left hi).symm
    · rw [min_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_right hi).symm
#align filter.germ.min_def Filter.Germ.min_def

/- warning: filter.germ.abs_def -> Filter.Germ.abs_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrderedAddCommGroup.{u2} β] (x : Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Abs.abs.{max u1 u2} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Neg.toHasAbs.{max u1 u2} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasNeg.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} β _inst_1)))))) (Filter.Germ.hasSup.{u1, u2} α β φ (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β (LinearOrderedAddCommGroup.toLinearOrder.{u2} β _inst_1)))))) x) (Filter.Germ.map.{u1, u2, u2} α β β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) (Abs.abs.{u2} β (Neg.toHasAbs.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} β _inst_1))))) (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β (LinearOrderedAddCommGroup.toLinearOrder.{u2} β _inst_1)))))) x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrderedAddCommGroup.{u2} β] (x : Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Abs.abs.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Neg.toHasAbs.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.neg.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} β _inst_1)))))))) (Filter.Germ.hasSup.{u1, u2} α β φ (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β (LinearOrderedAddCommGroup.toLinearOrder.{u2} β _inst_1))))))) x) (Filter.Germ.map.{u1, u2, u2} α β β (Ultrafilter.toFilter.{u1} α φ) (Abs.abs.{u2} β (Neg.toHasAbs.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} β _inst_1))))))) (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β (LinearOrderedAddCommGroup.toLinearOrder.{u2} β _inst_1))))))) x)
Case conversion may be inaccurate. Consider using '#align filter.germ.abs_def Filter.Germ.abs_defₓ'. -/
theorem abs_def [LinearOrderedAddCommGroup β] (x : β*) : |x| = map abs x :=
  inductionOn x fun a => rfl
#align filter.germ.abs_def Filter.Germ.abs_def

/- warning: filter.germ.const_max -> Filter.Germ.const_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrder.{u2} β] (x : β) (y : β), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasLiftT.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ)) (LinearOrder.max.{u2} β _inst_1 x y)) (LinearOrder.max.{max u1 u2} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.linearOrder.{u1, u2} α β φ _inst_1) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasLiftT.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ)) x) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasLiftT.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ)) y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrder.{u2} β] (x : β) (y : β), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.const.{u1, u2} α β (Ultrafilter.toFilter.{u1} α φ) (Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_1) x y)) (Max.max.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (LinearOrder.toMax.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.linearOrder.{u1, u2} α β φ _inst_1)) (Filter.Germ.const.{u1, u2} α β (Ultrafilter.toFilter.{u1} α φ) x) (Filter.Germ.const.{u1, u2} α β (Ultrafilter.toFilter.{u1} α φ) y))
Case conversion may be inaccurate. Consider using '#align filter.germ.const_max Filter.Germ.const_maxₓ'. -/
@[simp]
theorem const_max [LinearOrder β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y := by
  rw [max_def, map₂_const]
#align filter.germ.const_max Filter.Germ.const_max

/- warning: filter.germ.const_min -> Filter.Germ.const_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrder.{u2} β] (x : β) (y : β), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasLiftT.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ)) (LinearOrder.min.{u2} β _inst_1 x y)) (LinearOrder.min.{max u1 u2} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.linearOrder.{u1, u2} α β φ _inst_1) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasLiftT.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ)) x) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasLiftT.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ)) y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrder.{u2} β] (x : β) (y : β), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.const.{u1, u2} α β (Ultrafilter.toFilter.{u1} α φ) (Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_1) x y)) (Min.min.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (LinearOrder.toMin.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.linearOrder.{u1, u2} α β φ _inst_1)) (Filter.Germ.const.{u1, u2} α β (Ultrafilter.toFilter.{u1} α φ) x) (Filter.Germ.const.{u1, u2} α β (Ultrafilter.toFilter.{u1} α φ) y))
Case conversion may be inaccurate. Consider using '#align filter.germ.const_min Filter.Germ.const_minₓ'. -/
@[simp]
theorem const_min [LinearOrder β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y := by
  rw [min_def, map₂_const]
#align filter.germ.const_min Filter.Germ.const_min

/- warning: filter.germ.const_abs -> Filter.Germ.const_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrderedAddCommGroup.{u2} β] (x : β), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasLiftT.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ)) (Abs.abs.{u2} β (Neg.toHasAbs.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} β _inst_1))))) (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β (LinearOrderedAddCommGroup.toLinearOrder.{u2} β _inst_1))))) x)) (Abs.abs.{max u1 u2} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Neg.toHasAbs.{max u1 u2} (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasNeg.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} β _inst_1)))))) (Filter.Germ.hasSup.{u1, u2} α β φ (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β (LinearOrderedAddCommGroup.toLinearOrder.{u2} β _inst_1)))))) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ) β) (Filter.Germ.hasLiftT.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) φ)) x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Ultrafilter.{u1} α} [_inst_1 : LinearOrderedAddCommGroup.{u2} β] (x : β), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.const.{u1, u2} α β (Ultrafilter.toFilter.{u1} α φ) (Abs.abs.{u2} β (Neg.toHasAbs.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} β _inst_1))))))) (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β (LinearOrderedAddCommGroup.toLinearOrder.{u2} β _inst_1)))))) x)) (Abs.abs.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Neg.toHasAbs.{max u1 u2} (Filter.Germ.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β) (Filter.Germ.neg.{u1, u2} α (Ultrafilter.toFilter.{u1} α φ) β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} β _inst_1)))))))) (Filter.Germ.hasSup.{u1, u2} α β φ (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β (LinearOrderedAddCommGroup.toLinearOrder.{u2} β _inst_1))))))) (Filter.Germ.const.{u1, u2} α β (Ultrafilter.toFilter.{u1} α φ) x))
Case conversion may be inaccurate. Consider using '#align filter.germ.const_abs Filter.Germ.const_absₓ'. -/
@[simp]
theorem const_abs [LinearOrderedAddCommGroup β] (x : β) : (↑(|x|) : β*) = |↑x| := by
  rw [abs_def, map_const]
#align filter.germ.const_abs Filter.Germ.const_abs

end Germ

end Filter

