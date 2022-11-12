/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
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

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (IcoCat a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

/-- `Ico a b` has a bottom element whenever `a < b`. -/
@[reducible]
protected def orderBot [PartialOrder α] {a b : α} (h : a < b) : OrderBot (IcoCat a b) :=
  (is_least_Ico h).OrderBot
#align set.Ico.order_bot Set.IcoCat.orderBot

end IcoCat

namespace IioCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (IioCat a) :=
  Subtype.semilatticeInf fun x y hx hy => lt_of_le_of_lt inf_le_left hx

end IioCat

namespace IocCat

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (IocCat a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

/-- `Ioc a b` has a top element whenever `a < b`. -/
@[reducible]
protected def orderTop [PartialOrder α] {a b : α} (h : a < b) : OrderTop (IocCat a b) :=
  (is_greatest_Ioc h).OrderTop
#align set.Ioc.order_top Set.IocCat.orderTop

end IocCat

namespace IoiCat

instance [SemilatticeSup α] {a : α} : SemilatticeSup (IoiCat a) :=
  Subtype.semilatticeSup fun x y hx hy => lt_of_lt_of_le hx le_sup_left

end IoiCat

namespace IicCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (IicCat a) :=
  Subtype.semilatticeInf fun x y hx hy => le_trans inf_le_left hx

instance [SemilatticeSup α] {a : α} : SemilatticeSup (IicCat a) :=
  Subtype.semilatticeSup fun x y hx hy => sup_le hx hy

instance [Lattice α] {a : α} : Lattice (IicCat a) :=
  { IicCat.semilatticeInf, IicCat.semilatticeSup with }

instance [Preorder α] {a : α} : OrderTop (IicCat a) where
  top := ⟨a, le_refl a⟩
  le_top x := x.Prop

@[simp]
theorem coe_top [Preorder α] {a : α} : ↑(⊤ : IicCat a) = a :=
  rfl
#align set.Iic.coe_top Set.IicCat.coe_top

instance [Preorder α] [OrderBot α] {a : α} : OrderBot (IicCat a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp]
theorem coe_bot [Preorder α] [OrderBot α] {a : α} : ↑(⊥ : IicCat a) = (⊥ : α) :=
  rfl
#align set.Iic.coe_bot Set.IicCat.coe_bot

instance [Preorder α] [OrderBot α] {a : α} : BoundedOrder (IicCat a) :=
  { IicCat.orderTop, IicCat.orderBot with }

end IicCat

namespace IciCat

instance [SemilatticeInf α] {a : α} : SemilatticeInf (IciCat a) :=
  Subtype.semilatticeInf fun x y hx hy => le_inf hx hy

instance [SemilatticeSup α] {a : α} : SemilatticeSup (IciCat a) :=
  Subtype.semilatticeSup fun x y hx hy => le_trans hx le_sup_left

instance [Lattice α] {a : α} : Lattice (IciCat a) :=
  { IciCat.semilatticeInf, IciCat.semilatticeSup with }

instance [DistribLattice α] {a : α} : DistribLattice (IciCat a) :=
  { IciCat.lattice with le_sup_inf := fun a b c => le_sup_inf }

instance [Preorder α] {a : α} : OrderBot (IciCat a) where
  bot := ⟨a, le_refl a⟩
  bot_le x := x.Prop

@[simp]
theorem coe_bot [Preorder α] {a : α} : ↑(⊥ : IciCat a) = a :=
  rfl
#align set.Ici.coe_bot Set.IciCat.coe_bot

instance [Preorder α] [OrderTop α] {a : α} : OrderTop (IciCat a) where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp]
theorem coe_top [Preorder α] [OrderTop α] {a : α} : ↑(⊤ : IciCat a) = (⊤ : α) :=
  rfl
#align set.Ici.coe_top Set.IciCat.coe_top

instance [Preorder α] [OrderTop α] {a : α} : BoundedOrder (IciCat a) :=
  { IciCat.orderTop, IciCat.orderBot with }

end IciCat

namespace IccCat

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (IccCat a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (IccCat a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

instance [Lattice α] {a b : α} : Lattice (IccCat a b) :=
  { IccCat.semilatticeInf, IccCat.semilatticeSup with }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
@[reducible]
protected def orderBot [Preorder α] {a b : α} (h : a ≤ b) : OrderBot (IccCat a b) :=
  (is_least_Icc h).OrderBot
#align set.Icc.order_bot Set.IccCat.orderBot

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
@[reducible]
protected def orderTop [Preorder α] {a b : α} (h : a ≤ b) : OrderTop (IccCat a b) :=
  (is_greatest_Icc h).OrderTop
#align set.Icc.order_top Set.IccCat.orderTop

/-- `Icc a b` is a `bounded_order` whenever `a ≤ b`. -/
@[reducible]
protected def boundedOrder [Preorder α] {a b : α} (h : a ≤ b) : BoundedOrder (IccCat a b) :=
  { IccCat.orderTop h, IccCat.orderBot h with }
#align set.Icc.bounded_order Set.IccCat.boundedOrder

end IccCat

end Set

