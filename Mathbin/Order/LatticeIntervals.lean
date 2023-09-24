/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Order.Bounds.Basic

#align_import order.lattice_intervals from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Intervals in Lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

namespace Ico

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

#print Set.Ico.orderBot /-
/-- `Ico a b` has a bottom element whenever `a < b`. -/
@[reducible]
protected def orderBot [PartialOrder α] {a b : α} (h : a < b) : OrderBot (Ico a b) :=
  (isLeast_Ico h).OrderBot
#align set.Ico.order_bot Set.Ico.orderBot
-/

end Ico

namespace Iio

instance [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun x y hx hy => lt_of_le_of_lt inf_le_left hx

end Iio

namespace Ioc

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

#print Set.Ioc.orderTop /-
/-- `Ioc a b` has a top element whenever `a < b`. -/
@[reducible]
protected def orderTop [PartialOrder α] {a b : α} (h : a < b) : OrderTop (Ioc a b) :=
  (isGreatest_Ioc h).OrderTop
#align set.Ioc.order_top Set.Ioc.orderTop
-/

end Ioc

namespace Ioi

instance [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun x y hx hy => lt_of_lt_of_le hx le_sup_left

end Ioi

namespace Iic

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

#print Set.Iic.coe_top /-
@[simp]
theorem coe_top [Preorder α] {a : α} : ↑(⊤ : Iic a) = a :=
  rfl
#align set.Iic.coe_top Set.Iic.coe_top
-/

instance [Preorder α] [OrderBot α] {a : α} : OrderBot (Iic a)
    where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

#print Set.Iic.coe_bot /-
@[simp]
theorem coe_bot [Preorder α] [OrderBot α] {a : α} : ↑(⊥ : Iic a) = (⊥ : α) :=
  rfl
#align set.Iic.coe_bot Set.Iic.coe_bot
-/

instance [Preorder α] [OrderBot α] {a : α} : BoundedOrder (Iic a) :=
  { Iic.orderTop, Iic.orderBot with }

end Iic

namespace Ici

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

#print Set.Ici.coe_bot /-
@[simp]
theorem coe_bot [Preorder α] {a : α} : ↑(⊥ : Ici a) = a :=
  rfl
#align set.Ici.coe_bot Set.Ici.coe_bot
-/

instance [Preorder α] [OrderTop α] {a : α} : OrderTop (Ici a)
    where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

#print Set.Ici.coe_top /-
@[simp]
theorem coe_top [Preorder α] [OrderTop α] {a : α} : ↑(⊤ : Ici a) = (⊤ : α) :=
  rfl
#align set.Ici.coe_top Set.Ici.coe_top
-/

instance [Preorder α] [OrderTop α] {a : α} : BoundedOrder (Ici a) :=
  { Ici.orderTop, Ici.orderBot with }

end Ici

namespace Icc

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

end Icc

end Set

