import Mathbin.Order.BoundedOrder
import Mathbin.Data.Set.Intervals.Basic

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
  * `set.Iic.bounded_order`, within a `bounded_order`
  * `set.Ici.bounded_order`, within a `bounded_order`

-/


variable {α : Type _}

namespace Set

namespace Ico

variable {a b : α}

instance [SemilatticeInf α] : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_ltₓ inf_le_left hx.2⟩

/-- `Ico a b` has a bottom element whenever `a < b`. -/
def OrderBot [PartialOrderₓ α] (h : a < b) : OrderBot (Ico a b) where
  bot := ⟨a, ⟨le_reflₓ a, h⟩⟩
  bot_le := fun x => x.prop.1

end Ico

namespace Iio

instance [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun x y hx hy => lt_of_le_of_ltₓ inf_le_left hx

end Iio

namespace Ioc

variable {a b : α}

instance [SemilatticeSup α] : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨lt_of_lt_of_leₓ hx.1 le_sup_left, sup_le hx.2 hy.2⟩

/-- `Ioc a b` has a top element whenever `a < b`. -/
def OrderTop [PartialOrderₓ α] (h : a < b) : OrderTop (Ioc a b) where
  top := ⟨b, ⟨h, le_reflₓ b⟩⟩
  le_top := fun x => x.prop.2

end Ioc

namespace Iio

instance [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun x y hx hy => lt_of_lt_of_leₓ hx le_sup_left

end Iio

namespace Iic

variable {a : α}

instance [SemilatticeInf α] : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun x y hx hy => le_transₓ inf_le_left hx

instance [SemilatticeSup α] : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun x y hx hy => sup_le hx hy

instance [Lattice α] : Lattice (Iic a) :=
  { Iic.semilattice_inf, Iic.semilattice_sup with }

instance [Preorderₓ α] : OrderTop (Iic a) where
  top := ⟨a, le_reflₓ a⟩
  le_top := fun x => x.prop

@[simp]
theorem coe_top [PartialOrderₓ α] {a : α} : ↑(⊤ : Iic a) = a :=
  rfl

instance [Preorderₓ α] [OrderBot α] : OrderBot (Iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp]
theorem coe_bot [Preorderₓ α] [OrderBot α] {a : α} : ↑(⊥ : Iic a) = (⊥ : α) :=
  rfl

instance [PartialOrderₓ α] [NoBotOrder α] {a : α} : NoBotOrder (Iic a) :=
  ⟨fun x =>
    let ⟨y, hy⟩ := no_bot x.1
    ⟨⟨y, le_transₓ hy.le x.2⟩, hy⟩⟩

instance [Preorderₓ α] [BoundedOrder α] : BoundedOrder (Iic a) :=
  { Iic.order_top, Iic.order_bot with }

end Iic

namespace Ici

variable {a : α}

instance [SemilatticeInf α] : SemilatticeInf (Ici a) :=
  Subtype.semilatticeInf fun x y hx hy => le_inf hx hy

instance [SemilatticeSup α] : SemilatticeSup (Ici a) :=
  Subtype.semilatticeSup fun x y hx hy => le_transₓ hx le_sup_left

instance [Lattice α] : Lattice (Ici a) :=
  { Ici.semilattice_inf, Ici.semilattice_sup with }

instance [Preorderₓ α] : OrderBot (Ici a) where
  bot := ⟨a, le_reflₓ a⟩
  bot_le := fun x => x.prop

@[simp]
theorem coe_bot [PartialOrderₓ α] {a : α} : ↑(⊥ : Ici a) = a :=
  rfl

instance [Preorderₓ α] [OrderTop α] : OrderTop (Ici a) where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp]
theorem coe_top [Preorderₓ α] [OrderTop α] {a : α} : ↑(⊤ : Ici a) = (⊤ : α) :=
  rfl

instance [PartialOrderₓ α] [NoTopOrder α] {a : α} : NoTopOrder (Ici a) :=
  ⟨fun x =>
    let ⟨y, hy⟩ := no_top x.1
    ⟨⟨y, le_transₓ x.2 hy.le⟩, hy⟩⟩

instance [Preorderₓ α] [BoundedOrder α] : BoundedOrder (Ici a) :=
  { Ici.order_top, Ici.order_bot with }

end Ici

namespace Icc

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, le_transₓ inf_le_left hx.2⟩

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (Icc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨le_transₓ hx.1 le_sup_left, sup_le hx.2 hy.2⟩

instance [Lattice α] {a b : α} : Lattice (Icc a b) :=
  { Icc.semilattice_inf, Icc.semilattice_sup with }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
def OrderBot [Preorderₓ α] {a b : α} (h : a ≤ b) : OrderBot (Icc a b) where
  bot := ⟨a, ⟨le_reflₓ a, h⟩⟩
  bot_le := fun x => x.prop.1

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
def OrderTop [Preorderₓ α] {a b : α} (h : a ≤ b) : OrderTop (Icc a b) where
  top := ⟨b, ⟨h, le_reflₓ b⟩⟩
  le_top := fun x => x.prop.2

/-- `Icc a b` is a `bounded_order` whenever `a ≤ b`. -/
def BoundedOrder [Preorderₓ α] {a b : α} (h : a ≤ b) : BoundedOrder (Icc a b) :=
  { Icc.order_top h, Icc.order_bot h with }

end Icc

end Set

