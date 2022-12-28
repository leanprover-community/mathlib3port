/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module order.lattice_intervals
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Bounds.Basic

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions
In the following, `*` can represent either `c`, `o`, or `i`.
  * `set.Ic*.order_bot`
  * `set.Ii*.semillatice_inf`
  * `set.I*c.order_top`
  * `set.I*c.semillatice_inf`
  * `set.I**.lattice`
  * `set.Iic.bounded_order`, within an `order_bot`
  * `set.Ici.bounded_order`, within an `order_top`

-/


variable {α : Type _}

namespace Set

namespace IcoCat

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

#print Set.Ico.orderBot /-
/-- `Ico a b` has a bottom element whenever `a < b`. -/
@[reducible]
protected def orderBot [PartialOrder α] {a b : α} (h : a < b) : OrderBot (Ico a b) :=
  (isLeast_Ico h).OrderBot
#align set.Ico.order_bot Set.Ico.orderBot
-/

end IcoCat

namespace IioCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun x y hx hy => lt_of_le_of_lt inf_le_left hx

end IioCat

namespace IocCat

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

#print Set.Ioc.orderTop /-
/-- `Ioc a b` has a top element whenever `a < b`. -/
@[reducible]
protected def orderTop [PartialOrder α] {a b : α} (h : a < b) : OrderTop (Ioc a b) :=
  (isGreatest_Ioc h).OrderTop
#align set.Ioc.order_top Set.Ioc.orderTop
-/

end IocCat

namespace IoiCat

instance [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun x y hx hy => lt_of_lt_of_le hx le_sup_left

end IoiCat

namespace IicCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun x y hx hy => le_trans inf_le_left hx

instance [SemilatticeSup α] {a : α} : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun x y hx hy => sup_le hx hy

instance [Lattice α] {a : α} : Lattice (Iic a) :=
  { Iic.semilatticeInf, Iic.semilatticeSup with }

instance [Preorder α] {a : α} : OrderTop (Iic a)
    where
  top := ⟨a, le_refl a⟩
  le_top x := x.Prop

/- warning: set.Iic.coe_top -> Set.Iic.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Iic.{u1} α _inst_1 a)))))) (Top.top.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) (OrderTop.toHasTop.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Iic.{u1} α _inst_1 a))) (Set.Iic.orderTop.{u1} α _inst_1 a)))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, Eq.{succ u1} α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Iic.{u1} α _inst_1 a)) (Top.top.{u1} (Set.Elem.{u1} α (Set.Iic.{u1} α _inst_1 a)) (OrderTop.toTop.{u1} (Set.Elem.{u1} α (Set.Iic.{u1} α _inst_1 a)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Iic.{u1} α _inst_1 a))) (Set.Iic.orderTop.{u1} α _inst_1 a)))) a
Case conversion may be inaccurate. Consider using '#align set.Iic.coe_top Set.Iic.coe_topₓ'. -/
@[simp]
theorem coe_top [Preorder α] {a : α} : ↑(⊤ : Iic a) = a :=
  rfl
#align set.Iic.coe_top Set.Iic.coe_top

instance [Preorder α] [OrderBot α] {a : α} : OrderBot (Iic a)
    where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

/- warning: set.Iic.coe_bot -> Set.Iic.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] {a : α}, Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Iic.{u1} α _inst_1 a)))))) (Bot.bot.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) (OrderBot.toHasBot.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α _inst_1 a)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Iic.{u1} α _inst_1 a))) (Set.Iic.orderBot.{u1} α _inst_1 _inst_2 a)))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] {a : α}, Eq.{succ u1} α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Iic.{u1} α _inst_1 a)) (Bot.bot.{u1} (Set.Elem.{u1} α (Set.Iic.{u1} α _inst_1 a)) (OrderBot.toBot.{u1} (Set.Elem.{u1} α (Set.Iic.{u1} α _inst_1 a)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Iic.{u1} α _inst_1 a))) (Set.Iic.orderBot.{u1} α _inst_1 _inst_2 a)))) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
Case conversion may be inaccurate. Consider using '#align set.Iic.coe_bot Set.Iic.coe_botₓ'. -/
@[simp]
theorem coe_bot [Preorder α] [OrderBot α] {a : α} : ↑(⊥ : Iic a) = (⊥ : α) :=
  rfl
#align set.Iic.coe_bot Set.Iic.coe_bot

instance [Preorder α] [OrderBot α] {a : α} : BoundedOrder (Iic a) :=
  { Iic.orderTop, Iic.orderBot with }

end IicCat

namespace IciCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (Ici a) :=
  Subtype.semilatticeInf fun x y hx hy => le_inf hx hy

instance [SemilatticeSup α] {a : α} : SemilatticeSup (Ici a) :=
  Subtype.semilatticeSup fun x y hx hy => le_trans hx le_sup_left

instance [Lattice α] {a : α} : Lattice (Ici a) :=
  { Ici.semilatticeInf, Ici.semilatticeSup with }

instance [DistribLattice α] {a : α} : DistribLattice (Ici a) :=
  { Ici.lattice with le_sup_inf := fun a b c => le_sup_inf }

instance [Preorder α] {a : α} : OrderBot (Ici a)
    where
  bot := ⟨a, le_refl a⟩
  bot_le x := x.Prop

/- warning: set.Ici.coe_bot -> Set.Ici.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Ici.{u1} α _inst_1 a)))))) (Bot.bot.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) (OrderBot.toHasBot.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Ici.{u1} α _inst_1 a))) (Set.Ici.orderBot.{u1} α _inst_1 a)))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, Eq.{succ u1} α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Ici.{u1} α _inst_1 a)) (Bot.bot.{u1} (Set.Elem.{u1} α (Set.Ici.{u1} α _inst_1 a)) (OrderBot.toBot.{u1} (Set.Elem.{u1} α (Set.Ici.{u1} α _inst_1 a)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Ici.{u1} α _inst_1 a))) (Set.Ici.orderBot.{u1} α _inst_1 a)))) a
Case conversion may be inaccurate. Consider using '#align set.Ici.coe_bot Set.Ici.coe_botₓ'. -/
@[simp]
theorem coe_bot [Preorder α] {a : α} : ↑(⊥ : Ici a) = a :=
  rfl
#align set.Ici.coe_bot Set.Ici.coe_bot

instance [Preorder α] [OrderTop α] {a : α} : OrderTop (Ici a)
    where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

/- warning: set.Ici.coe_top -> Set.Ici.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] {a : α}, Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Ici.{u1} α _inst_1 a)))))) (Top.top.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) (OrderTop.toHasTop.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ici.{u1} α _inst_1 a)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Ici.{u1} α _inst_1 a))) (Set.Ici.orderTop.{u1} α _inst_1 _inst_2 a)))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] {a : α}, Eq.{succ u1} α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Ici.{u1} α _inst_1 a)) (Top.top.{u1} (Set.Elem.{u1} α (Set.Ici.{u1} α _inst_1 a)) (OrderTop.toTop.{u1} (Set.Elem.{u1} α (Set.Ici.{u1} α _inst_1 a)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Ici.{u1} α _inst_1 a))) (Set.Ici.orderTop.{u1} α _inst_1 _inst_2 a)))) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
Case conversion may be inaccurate. Consider using '#align set.Ici.coe_top Set.Ici.coe_topₓ'. -/
@[simp]
theorem coe_top [Preorder α] [OrderTop α] {a : α} : ↑(⊤ : Ici a) = (⊤ : α) :=
  rfl
#align set.Ici.coe_top Set.Ici.coe_top

instance [Preorder α] [OrderTop α] {a : α} : BoundedOrder (Ici a) :=
  { Ici.orderTop, Ici.orderBot with }

end IciCat

namespace IccCat

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (Icc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

instance [Lattice α] {a b : α} : Lattice (Icc a b) :=
  { Icc.semilatticeInf, Icc.semilatticeSup with }

#print Set.Icc.orderBot /-
/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
@[reducible]
protected def orderBot [Preorder α] {a b : α} (h : a ≤ b) : OrderBot (Icc a b) :=
  (isLeast_Icc h).OrderBot
#align set.Icc.order_bot Set.Icc.orderBot
-/

#print Set.Icc.orderTop /-
/-- `Icc a b` has a top element whenever `a ≤ b`. -/
@[reducible]
protected def orderTop [Preorder α] {a b : α} (h : a ≤ b) : OrderTop (Icc a b) :=
  (isGreatest_Icc h).OrderTop
#align set.Icc.order_top Set.Icc.orderTop
-/

#print Set.Icc.boundedOrder /-
/-- `Icc a b` is a `bounded_order` whenever `a ≤ b`. -/
@[reducible]
protected def boundedOrder [Preorder α] {a b : α} (h : a ≤ b) : BoundedOrder (Icc a b) :=
  { Icc.orderTop h, Icc.orderBot h with }
#align set.Icc.bounded_order Set.Icc.boundedOrder
-/

end IccCat

end Set

