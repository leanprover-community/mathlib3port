import Mathbin.Order.BoundedLattice 
import Mathbin.Data.Set.Intervals.Basic

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions
In the following, `*` can represent either `c`, `o`, or `i`.
  * `set.Ic*.semilattice_inf_bot`
  * `set.Ii*.semillatice_inf`
  * `set.I*c.semilattice_sup_top`
  * `set.I*c.semillatice_inf`
  * `set.Iic.bounded_lattice`, within a `bounded_lattice`
  * `set.Ici.bounded_lattice`, within a `bounded_lattice`

-/


variable{α : Type _}

namespace Set

namespace Ico

variable{a b : α}

instance  [SemilatticeInf α] : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_ltₓ inf_le_left hx.2⟩

/-- `Ico a b` has a bottom element whenever `a < b`. -/
def OrderBot [PartialOrderₓ α] (h : a < b) : OrderBot (Ico a b) :=
  { Subtype.partialOrder _ with bot := ⟨a, ⟨le_reflₓ a, h⟩⟩, bot_le := fun x => x.prop.1 }

/-- `Ico a b` is a `semilattice_inf_bot` whenever `a < b`. -/
def SemilatticeInfBot [SemilatticeInf α] (h : a < b) : SemilatticeInfBot (Ico a b) :=
  { Ico.semilattice_inf, Ico.order_bot h with  }

end Ico

namespace Iio

instance  [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun x y hx hy => lt_of_le_of_ltₓ inf_le_left hx

end Iio

namespace Ioc

variable{a b : α}

instance  [SemilatticeSup α] : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨lt_of_lt_of_leₓ hx.1 le_sup_left, sup_le hx.2 hy.2⟩

/-- `Ioc a b` has a top element whenever `a < b`. -/
def OrderTop [PartialOrderₓ α] (h : a < b) : OrderTop (Ioc a b) :=
  { Subtype.partialOrder _ with top := ⟨b, ⟨h, le_reflₓ b⟩⟩, le_top := fun x => x.prop.2 }

/-- `Ioc a b` is a `semilattice_sup_top` whenever `a < b`. -/
def SemilatticeSupTop [SemilatticeSup α] (h : a < b) : SemilatticeSupTop (Ioc a b) :=
  { Ioc.semilattice_sup, Ioc.order_top h with  }

end Ioc

namespace Iio

instance  [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun x y hx hy => lt_of_lt_of_leₓ hx le_sup_left

end Iio

namespace Iic

variable{a : α}

instance  [SemilatticeInf α] : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun x y hx hy => le_transₓ inf_le_left hx

instance  [SemilatticeSup α] : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun x y hx hy => sup_le hx hy

instance  [Lattice α] : Lattice (Iic a) :=
  { Iic.semilattice_inf, Iic.semilattice_sup with  }

instance  [PartialOrderₓ α] : OrderTop (Iic a) :=
  { Subtype.partialOrder _ with top := ⟨a, le_reflₓ a⟩, le_top := fun x => x.prop }

@[simp]
theorem coe_top [PartialOrderₓ α] {a : α} : «expr↑ » (⊤ : Iic a) = a :=
  rfl

instance  [SemilatticeInf α] : SemilatticeInfTop (Iic a) :=
  { Iic.semilattice_inf, Iic.order_top with  }

instance  [SemilatticeSup α] : SemilatticeSupTop (Iic a) :=
  { Iic.semilattice_sup, Iic.order_top with  }

instance  [Preorderₓ α] [OrderBot α] : OrderBot (Iic a) :=
  { bot := ⟨⊥, bot_le⟩, bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le }

@[simp]
theorem coe_bot [Preorderₓ α] [OrderBot α] {a : α} : «expr↑ » (⊥ : Iic a) = (⊥ : α) :=
  rfl

instance  [PartialOrderₓ α] [NoBotOrder α] {a : α} : NoBotOrder (Iic a) :=
  ⟨fun x =>
      let ⟨y, hy⟩ := no_bot x.1
      ⟨⟨y, le_transₓ hy.le x.2⟩, hy⟩⟩

instance  [SemilatticeInfBot α] : SemilatticeInfBot (Iic a) :=
  { Iic.semilattice_inf, Iic.order_bot with  }

instance  [SemilatticeSupBot α] : SemilatticeSupBot (Iic a) :=
  { Iic.semilattice_sup, Iic.order_bot with  }

instance  [BoundedLattice α] : BoundedLattice (Iic a) :=
  { Iic.order_top, Iic.order_bot, Iic.lattice with  }

end Iic

namespace Ici

variable{a : α}

instance  [SemilatticeInf α] : SemilatticeInf (Ici a) :=
  Subtype.semilatticeInf fun x y hx hy => le_inf hx hy

instance  [SemilatticeSup α] : SemilatticeSup (Ici a) :=
  Subtype.semilatticeSup fun x y hx hy => le_transₓ hx le_sup_left

instance  [Lattice α] : Lattice (Ici a) :=
  { Ici.semilattice_inf, Ici.semilattice_sup with  }

instance  [Preorderₓ α] : OrderBot (Ici a) :=
  { bot := ⟨a, le_reflₓ a⟩, bot_le := fun x => x.prop }

@[simp]
theorem coe_bot [PartialOrderₓ α] {a : α} : «expr↑ » (⊥ : Ici a) = a :=
  rfl

instance  [SemilatticeInf α] : SemilatticeInfBot (Ici a) :=
  { Ici.semilattice_inf, Ici.order_bot with  }

instance  [SemilatticeSup α] : SemilatticeSupBot (Ici a) :=
  { Ici.semilattice_sup, Ici.order_bot with  }

instance  [Preorderₓ α] [OrderTop α] : OrderTop (Ici a) :=
  { top := ⟨⊤, le_top⟩, le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top }

@[simp]
theorem coe_top [Preorderₓ α] [OrderTop α] {a : α} : «expr↑ » (⊤ : Ici a) = (⊤ : α) :=
  rfl

instance  [PartialOrderₓ α] [NoTopOrder α] {a : α} : NoTopOrder (Ici a) :=
  ⟨fun x =>
      let ⟨y, hy⟩ := no_top x.1
      ⟨⟨y, le_transₓ x.2 hy.le⟩, hy⟩⟩

instance  [SemilatticeSupTop α] : SemilatticeSupTop (Ici a) :=
  { Ici.semilattice_sup, Ici.order_top with  }

instance  [SemilatticeInfTop α] : SemilatticeInfTop (Ici a) :=
  { Ici.semilattice_inf, Ici.order_top with  }

instance  [BoundedLattice α] : BoundedLattice (Ici a) :=
  { Ici.order_top, Ici.order_bot, Ici.lattice with  }

end Ici

namespace Icc

instance  [SemilatticeInf α] {a b : α} : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, le_transₓ inf_le_left hx.2⟩

instance  [SemilatticeSup α] {a b : α} : SemilatticeSup (Icc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨le_transₓ hx.1 le_sup_left, sup_le hx.2 hy.2⟩

instance  [Lattice α] {a b : α} : Lattice (Icc a b) :=
  { Icc.semilattice_inf, Icc.semilattice_sup with  }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
def OrderBot [PartialOrderₓ α] {a b : α} (h : a ≤ b) : OrderBot (Icc a b) :=
  { Subtype.partialOrder _ with bot := ⟨a, ⟨le_reflₓ a, h⟩⟩, bot_le := fun x => x.prop.1 }

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
def OrderTop [PartialOrderₓ α] {a b : α} (h : a ≤ b) : OrderTop (Icc a b) :=
  { Subtype.partialOrder _ with top := ⟨b, ⟨h, le_reflₓ b⟩⟩, le_top := fun x => x.prop.2 }

/-- `Icc a b` is a `semilattice_inf_bot` whenever `a ≤ b`. -/
def SemilatticeInfBot [SemilatticeInf α] {a b : α} (h : a ≤ b) : SemilatticeInfBot (Icc a b) :=
  { Icc.order_bot h, Icc.semilattice_inf with  }

/-- `Icc a b` is a `semilattice_inf_top` whenever `a ≤ b`. -/
def SemilatticeInfTop [SemilatticeInf α] {a b : α} (h : a ≤ b) : SemilatticeInfTop (Icc a b) :=
  { Icc.order_top h, Icc.semilattice_inf with  }

/-- `Icc a b` is a `semilattice_sup_bot` whenever `a ≤ b`. -/
def SemilatticeSupBot [SemilatticeSup α] {a b : α} (h : a ≤ b) : SemilatticeSupBot (Icc a b) :=
  { Icc.order_bot h, Icc.semilattice_sup with  }

/-- `Icc a b` is a `semilattice_sup_top` whenever `a ≤ b`. -/
def SemilatticeSupTop [SemilatticeSup α] {a b : α} (h : a ≤ b) : SemilatticeSupTop (Icc a b) :=
  { Icc.order_top h, Icc.semilattice_sup with  }

/-- `Icc a b` is a `bounded_lattice` whenever `a ≤ b`. -/
def BoundedLattice [Lattice α] {a b : α} (h : a ≤ b) : BoundedLattice (Icc a b) :=
  { Icc.semilattice_inf_bot h, Icc.semilattice_sup_top h with  }

end Icc

end Set

