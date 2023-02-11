/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.copy
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic

/-!
# Tooling to make copies of lattice structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/


open Order

universe u

variable {α : Type u}

/- warning: bounded_order.copy -> BoundedOrder.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {h : LE.{u1} α} {h' : LE.{u1} α} (c : BoundedOrder.{u1} α h') (top : α), (Eq.{succ u1} α top (BoundedOrder.top.{u1} α h' c)) -> (forall (bot : α), (Eq.{succ u1} α bot (BoundedOrder.bot.{u1} α h' c)) -> (forall (x : α) (y : α), Iff (LE.le.{u1} α h x y) (LE.le.{u1} α h' x y)) -> (BoundedOrder.{u1} α h))
but is expected to have type
  forall {α : Type.{u1}} {h : LE.{u1} α} {h' : LE.{u1} α} (c : BoundedOrder.{u1} α h') (top : α), (Eq.{succ u1} α top (Top.top.{u1} α (inferInstance.{succ u1} (Top.{u1} α) (OrderTop.toTop.{u1} α h' (BoundedOrder.toOrderTop.{u1} α h' c))))) -> (forall (bot : α), (Eq.{succ u1} α bot (Bot.bot.{u1} α (inferInstance.{succ u1} (Bot.{u1} α) (OrderBot.toBot.{u1} α h' (BoundedOrder.toOrderBot.{u1} α h' c))))) -> (forall (x : α) (y : α), Iff (LE.le.{u1} α h x y) (LE.le.{u1} α h' x y)) -> (BoundedOrder.{u1} α h))
Case conversion may be inaccurate. Consider using '#align bounded_order.copy BoundedOrder.copyₓ'. -/
/-- A function to create a provable equal copy of a bounded order
with possibly different definitional equalities. -/
def BoundedOrder.copy {h : LE α} {h' : LE α} (c : @BoundedOrder α h') (top : α)
    (eq_top : top = @BoundedOrder.top α _ c) (bot : α) (eq_bot : bot = @BoundedOrder.bot α _ c)
    (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) : @BoundedOrder α h :=
  by
  refine'
    { top
      bot.. }
  all_goals abstract subst_vars; cases c; simp_rw [le_eq]; assumption
#align bounded_order.copy BoundedOrder.copy

/- warning: lattice.copy -> Lattice.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (c : Lattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (Lattice.Le.{u1} α c)) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (Lattice.sup.{u1} α c)) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (Lattice.inf.{u1} α c)) -> (Lattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} (c : Lattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (LE.le.{u1} α (inferInstance.{succ u1} (LE.{u1} α) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α c))))))) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (HasSup.sup.{u1} α (inferInstance.{succ u1} (HasSup.{u1} α) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α c))))) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (HasInf.inf.{u1} α (inferInstance.{succ u1} (HasInf.{u1} α) (Lattice.toHasInf.{u1} α c)))) -> (Lattice.{u1} α)))
Case conversion may be inaccurate. Consider using '#align lattice.copy Lattice.copyₓ'. -/
/-- A function to create a provable equal copy of a lattice
with possibly different definitional equalities. -/
def Lattice.copy (c : Lattice α) (le : α → α → Prop) (eq_le : le = @Lattice.Le α c)
    (sup : α → α → α) (eq_sup : sup = @Lattice.sup α c) (inf : α → α → α)
    (eq_inf : inf = @Lattice.inf α c) : Lattice α :=
  by
  refine'
    { le
      sup
      inf.. }
  all_goals abstract subst_vars; cases c; assumption
#align lattice.copy Lattice.copy

/- warning: distrib_lattice.copy -> DistribLattice.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (c : DistribLattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (DistribLattice.Le.{u1} α c)) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (DistribLattice.sup.{u1} α c)) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (DistribLattice.inf.{u1} α c)) -> (DistribLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} (c : DistribLattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (LE.le.{u1} α (inferInstance.{succ u1} (LE.{u1} α) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α c)))))))) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (HasSup.sup.{u1} α (inferInstance.{succ u1} (HasSup.{u1} α) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α c)))))) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (HasInf.inf.{u1} α (inferInstance.{succ u1} (HasInf.{u1} α) (Lattice.toHasInf.{u1} α (DistribLattice.toLattice.{u1} α c))))) -> (DistribLattice.{u1} α)))
Case conversion may be inaccurate. Consider using '#align distrib_lattice.copy DistribLattice.copyₓ'. -/
/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
def DistribLattice.copy (c : DistribLattice α) (le : α → α → Prop)
    (eq_le : le = @DistribLattice.Le α c) (sup : α → α → α) (eq_sup : sup = @DistribLattice.sup α c)
    (inf : α → α → α) (eq_inf : inf = @DistribLattice.inf α c) : DistribLattice α :=
  by
  refine'
    { le
      sup
      inf.. }
  all_goals abstract subst_vars; cases c; assumption
#align distrib_lattice.copy DistribLattice.copy

/- warning: complete_lattice.copy -> CompleteLattice.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (c : CompleteLattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (CompleteLattice.Le.{u1} α c)) -> (forall (top : α), (Eq.{succ u1} α top (CompleteLattice.top.{u1} α c)) -> (forall (bot : α), (Eq.{succ u1} α bot (CompleteLattice.bot.{u1} α c)) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (CompleteLattice.sup.{u1} α c)) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (CompleteLattice.inf.{u1} α c)) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (CompleteLattice.sup.{u1} α c)) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (CompleteLattice.inf.{u1} α c)) -> (CompleteLattice.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u1}} (c : CompleteLattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (LE.le.{u1} α (inferInstance.{succ u1} (LE.{u1} α) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α c))))))) -> (forall (top : α), (Eq.{succ u1} α top (Top.top.{u1} α (inferInstance.{succ u1} (Top.{u1} α) (CompleteLattice.toTop.{u1} α c)))) -> (forall (bot : α), (Eq.{succ u1} α bot (Bot.bot.{u1} α (inferInstance.{succ u1} (Bot.{u1} α) (CompleteLattice.toBot.{u1} α c)))) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (HasSup.sup.{u1} α (inferInstance.{succ u1} (HasSup.{u1} α) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α c))))))) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (HasInf.inf.{u1} α (inferInstance.{succ u1} (HasInf.{u1} α) (Lattice.toHasInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α c)))))) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (SupSet.supₛ.{u1} α (inferInstance.{succ u1} (SupSet.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α c))))) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (InfSet.infₛ.{u1} α (inferInstance.{succ u1} (InfSet.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α c))))) -> (CompleteLattice.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.copy CompleteLattice.copyₓ'. -/
/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
def CompleteLattice.copy (c : CompleteLattice α) (le : α → α → Prop)
    (eq_le : le = @CompleteLattice.Le α c) (top : α) (eq_top : top = @CompleteLattice.top α c)
    (bot : α) (eq_bot : bot = @CompleteLattice.bot α c) (sup : α → α → α)
    (eq_sup : sup = @CompleteLattice.sup α c) (inf : α → α → α)
    (eq_inf : inf = @CompleteLattice.inf α c) (Sup : Set α → α)
    (eq_Sup : Sup = @CompleteLattice.sup α c) (Inf : Set α → α)
    (eq_Inf : Inf = @CompleteLattice.inf α c) : CompleteLattice α :=
  by
  refine'
    {
      Lattice.copy (@CompleteLattice.toLattice α c) le eq_le sup eq_sup inf
        eq_inf with
      le
      top
      bot
      sup
      inf
      supₛ
      infₛ.. }
  all_goals abstract subst_vars; cases c; assumption
#align complete_lattice.copy CompleteLattice.copy

/- warning: frame.copy -> Frame.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (c : Order.Frame.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (Order.Frame.Le.{u1} α c)) -> (forall (top : α), (Eq.{succ u1} α top (Order.Frame.top.{u1} α c)) -> (forall (bot : α), (Eq.{succ u1} α bot (Order.Frame.bot.{u1} α c)) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (Order.Frame.sup.{u1} α c)) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (Order.Frame.inf.{u1} α c)) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (Order.Frame.sup.{u1} α c)) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (Order.Frame.inf.{u1} α c)) -> (Order.Frame.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u1}} (c : Order.Frame.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (LE.le.{u1} α (inferInstance.{succ u1} (LE.{u1} α) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α c)))))))) -> (forall (top : α), (Eq.{succ u1} α top (Top.top.{u1} α (inferInstance.{succ u1} (Top.{u1} α) (CompleteLattice.toTop.{u1} α (Order.Frame.toCompleteLattice.{u1} α c))))) -> (forall (bot : α), (Eq.{succ u1} α bot (Bot.bot.{u1} α (inferInstance.{succ u1} (Bot.{u1} α) (CompleteLattice.toBot.{u1} α (Order.Frame.toCompleteLattice.{u1} α c))))) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (HasSup.sup.{u1} α (inferInstance.{succ u1} (HasSup.{u1} α) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α c)))))))) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (HasInf.inf.{u1} α (inferInstance.{succ u1} (HasInf.{u1} α) (Lattice.toHasInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α c))))))) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (SupSet.supₛ.{u1} α (inferInstance.{succ u1} (SupSet.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α c)))))) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (InfSet.infₛ.{u1} α (inferInstance.{succ u1} (InfSet.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α c)))))) -> (Order.Frame.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align frame.copy Frame.copyₓ'. -/
/-- A function to create a provable equal copy of a frame with possibly different definitional
equalities. -/
def Frame.copy (c : Frame α) (le : α → α → Prop) (eq_le : le = @Frame.Le α c) (top : α)
    (eq_top : top = @Frame.top α c) (bot : α) (eq_bot : bot = @Frame.bot α c) (sup : α → α → α)
    (eq_sup : sup = @Frame.sup α c) (inf : α → α → α) (eq_inf : inf = @Frame.inf α c)
    (Sup : Set α → α) (eq_Sup : Sup = @Frame.sup α c) (Inf : Set α → α)
    (eq_Inf : Inf = @Frame.inf α c) : Frame α :=
  by
  refine'
    {
      CompleteLattice.copy (@frame.to_complete_lattice α c) le eq_le top eq_top bot eq_bot sup
        eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf with
      le
      top
      bot
      sup
      inf
      supₛ
      infₛ.. }
  all_goals abstract subst_vars; cases c; assumption
#align frame.copy Frame.copy

/- warning: coframe.copy -> Coframe.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (c : Order.Coframe.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (Order.Coframe.Le.{u1} α c)) -> (forall (top : α), (Eq.{succ u1} α top (Order.Coframe.top.{u1} α c)) -> (forall (bot : α), (Eq.{succ u1} α bot (Order.Coframe.bot.{u1} α c)) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (Order.Coframe.sup.{u1} α c)) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (Order.Coframe.inf.{u1} α c)) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (Order.Coframe.sup.{u1} α c)) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (Order.Coframe.inf.{u1} α c)) -> (Order.Coframe.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u1}} (c : Order.Coframe.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (LE.le.{u1} α (inferInstance.{succ u1} (LE.{u1} α) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α c)))))))) -> (forall (top : α), (Eq.{succ u1} α top (Top.top.{u1} α (inferInstance.{succ u1} (Top.{u1} α) (CompleteLattice.toTop.{u1} α (Order.Coframe.toCompleteLattice.{u1} α c))))) -> (forall (bot : α), (Eq.{succ u1} α bot (Bot.bot.{u1} α (inferInstance.{succ u1} (Bot.{u1} α) (CompleteLattice.toBot.{u1} α (Order.Coframe.toCompleteLattice.{u1} α c))))) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (HasSup.sup.{u1} α (inferInstance.{succ u1} (HasSup.{u1} α) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α c)))))))) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (HasInf.inf.{u1} α (inferInstance.{succ u1} (HasInf.{u1} α) (Lattice.toHasInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α c))))))) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (SupSet.supₛ.{u1} α (inferInstance.{succ u1} (SupSet.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α c)))))) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (InfSet.infₛ.{u1} α (inferInstance.{succ u1} (InfSet.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α c)))))) -> (Order.Coframe.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align coframe.copy Coframe.copyₓ'. -/
/-- A function to create a provable equal copy of a coframe with possibly different definitional
equalities. -/
def Coframe.copy (c : Coframe α) (le : α → α → Prop) (eq_le : le = @Coframe.Le α c) (top : α)
    (eq_top : top = @Coframe.top α c) (bot : α) (eq_bot : bot = @Coframe.bot α c) (sup : α → α → α)
    (eq_sup : sup = @Coframe.sup α c) (inf : α → α → α) (eq_inf : inf = @Coframe.inf α c)
    (Sup : Set α → α) (eq_Sup : Sup = @Coframe.sup α c) (Inf : Set α → α)
    (eq_Inf : Inf = @Coframe.inf α c) : Coframe α :=
  by
  refine'
    {
      CompleteLattice.copy (@coframe.to_complete_lattice α c) le eq_le top eq_top bot eq_bot sup
        eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf with
      le
      top
      bot
      sup
      inf
      supₛ
      infₛ.. }
  all_goals abstract subst_vars; cases c; assumption
#align coframe.copy Coframe.copy

/- warning: complete_distrib_lattice.copy -> CompleteDistribLattice.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (c : CompleteDistribLattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (CompleteDistribLattice.Le.{u1} α c)) -> (forall (top : α), (Eq.{succ u1} α top (CompleteDistribLattice.top.{u1} α c)) -> (forall (bot : α), (Eq.{succ u1} α bot (CompleteDistribLattice.bot.{u1} α c)) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (CompleteDistribLattice.sup.{u1} α c)) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (CompleteDistribLattice.inf.{u1} α c)) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (CompleteDistribLattice.sup.{u1} α c)) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (CompleteDistribLattice.inf.{u1} α c)) -> (CompleteDistribLattice.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u1}} (c : CompleteDistribLattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (LE.le.{u1} α (inferInstance.{succ u1} (LE.{u1} α) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α c))))))))) -> (forall (top : α), (Eq.{succ u1} α top (Top.top.{u1} α (inferInstance.{succ u1} (Top.{u1} α) (CompleteLattice.toTop.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α c)))))) -> (forall (bot : α), (Eq.{succ u1} α bot (Bot.bot.{u1} α (inferInstance.{succ u1} (Bot.{u1} α) (CompleteLattice.toBot.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α c)))))) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (HasSup.sup.{u1} α (inferInstance.{succ u1} (HasSup.{u1} α) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α c))))))))) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (HasInf.inf.{u1} α (inferInstance.{succ u1} (HasInf.{u1} α) (Lattice.toHasInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α c)))))))) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (SupSet.supₛ.{u1} α (inferInstance.{succ u1} (SupSet.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α c))))))) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (InfSet.infₛ.{u1} α (inferInstance.{succ u1} (InfSet.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α c))))))) -> (CompleteDistribLattice.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align complete_distrib_lattice.copy CompleteDistribLattice.copyₓ'. -/
/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
def CompleteDistribLattice.copy (c : CompleteDistribLattice α) (le : α → α → Prop)
    (eq_le : le = @CompleteDistribLattice.Le α c) (top : α)
    (eq_top : top = @CompleteDistribLattice.top α c) (bot : α)
    (eq_bot : bot = @CompleteDistribLattice.bot α c) (sup : α → α → α)
    (eq_sup : sup = @CompleteDistribLattice.sup α c) (inf : α → α → α)
    (eq_inf : inf = @CompleteDistribLattice.inf α c) (Sup : Set α → α)
    (eq_Sup : Sup = @CompleteDistribLattice.sup α c) (Inf : Set α → α)
    (eq_Inf : Inf = @CompleteDistribLattice.inf α c) : CompleteDistribLattice α :=
  {
    Frame.copy (@CompleteDistribLattice.toFrame α c) le eq_le top eq_top bot eq_bot sup eq_sup inf
      eq_inf Sup eq_Sup Inf eq_Inf,
    Coframe.copy (@CompleteDistribLattice.toCoframe α c) le eq_le top eq_top bot eq_bot sup eq_sup
      inf eq_inf Sup eq_Sup Inf eq_Inf with }
#align complete_distrib_lattice.copy CompleteDistribLattice.copy

/- warning: conditionally_complete_lattice.copy -> ConditionallyCompleteLattice.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (c : ConditionallyCompleteLattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (ConditionallyCompleteLattice.Le.{u1} α c)) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (ConditionallyCompleteLattice.sup.{u1} α c)) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (ConditionallyCompleteLattice.inf.{u1} α c)) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (ConditionallyCompleteLattice.sup.{u1} α c)) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (ConditionallyCompleteLattice.inf.{u1} α c)) -> (ConditionallyCompleteLattice.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} (c : ConditionallyCompleteLattice.{u1} α) (le : α -> α -> Prop), (Eq.{succ u1} (α -> α -> Prop) le (LE.le.{u1} α (inferInstance.{succ u1} (LE.{u1} α) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α c)))))))) -> (forall (sup : α -> α -> α), (Eq.{succ u1} (α -> α -> α) sup (HasSup.sup.{u1} α (inferInstance.{succ u1} (HasSup.{u1} α) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α c)))))) -> (forall (inf : α -> α -> α), (Eq.{succ u1} (α -> α -> α) inf (HasInf.inf.{u1} α (inferInstance.{succ u1} (HasInf.{u1} α) (Lattice.toHasInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α c))))) -> (forall (Sup : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Sup (SupSet.supₛ.{u1} α (inferInstance.{succ u1} (SupSet.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} α c)))) -> (forall (Inf : (Set.{u1} α) -> α), (Eq.{succ u1} ((Set.{u1} α) -> α) Inf (InfSet.infₛ.{u1} α (inferInstance.{succ u1} (InfSet.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} α c)))) -> (ConditionallyCompleteLattice.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align conditionally_complete_lattice.copy ConditionallyCompleteLattice.copyₓ'. -/
/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
def ConditionallyCompleteLattice.copy (c : ConditionallyCompleteLattice α) (le : α → α → Prop)
    (eq_le : le = @ConditionallyCompleteLattice.Le α c) (sup : α → α → α)
    (eq_sup : sup = @ConditionallyCompleteLattice.sup α c) (inf : α → α → α)
    (eq_inf : inf = @ConditionallyCompleteLattice.inf α c) (Sup : Set α → α)
    (eq_Sup : Sup = @ConditionallyCompleteLattice.sup α c) (Inf : Set α → α)
    (eq_Inf : Inf = @ConditionallyCompleteLattice.inf α c) : ConditionallyCompleteLattice α :=
  by
  refine'
    { le
      sup
      inf
      supₛ
      infₛ.. }
  all_goals abstract subst_vars; cases c; assumption
#align conditionally_complete_lattice.copy ConditionallyCompleteLattice.copy

