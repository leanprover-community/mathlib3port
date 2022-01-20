import Mathbin.Data.Fintype.Basic

/-!
# Order structures on finite types

This file provides order instances on fintypes:
* A `semilattice_inf` instance on a `fintype` allows constructing an `order_bot`.
* A `semilattice_sup` instance on a `fintype` allows constructing an `order_top`.
* A `lattice` instance on a `fintype` allows constructing a `bounded_order`.
* A `lattice` instance on a `fintype` can be promoted to a `complete_lattice`.
* A `linear_order` instance on a `fintype` can be promoted to a `complete_linear_order`.

Getting to a `bounded_order` from a `lattice` is computable, but the
subsequent definitions are not, since the definitions of `Sup` and `Inf` use `set.to_finset`, which
implicitly requires a `decidable_pred` instance for every `s : set α`.

The `complete_linear_order` instance for `fin (n + 1)` is the only proper instance in this file. The
rest are `def`s to avoid loops in typeclass inference.
-/


variable {ι α : Type _} [Fintype ι] [Fintype α]

section Inhabited

variable (α) [Inhabited α]

/-- Constructs the `⊥` of a finite inhabited `semilattice_inf`. -/
@[reducible]
def Fintype.toOrderBot [SemilatticeInf α] : OrderBot α where
  bot := Finset.fold (·⊓·) (arbitrary α) id Finset.univ
  bot_le := fun a => ((Finset.fold_op_rel_iff_and (@le_inf_iff α _)).1 le_rfl).2 a (Finset.mem_univ _)

/-- Constructs the `⊤` of a finite inhabited `semilattice_sup` -/
@[reducible]
def Fintype.toOrderTop [SemilatticeSup α] : OrderTop α where
  top := Finset.fold (·⊔·) (arbitrary α) id Finset.univ
  le_top := fun a =>
    ((Finset.fold_op_rel_iff_and fun x y z => show x ≥ y⊔z ↔ _ from sup_le_iff).mp le_rfl).2 a (Finset.mem_univ a)

/-- Constructs the `⊤` and `⊥` of a finite inhabited `lattice`. -/
@[reducible]
def Fintype.toBoundedOrder [Lattice α] : BoundedOrder α :=
  { Fintype.toOrderBot α, Fintype.toOrderTop α with }

end Inhabited

section BoundedOrder

variable (α)

open_locale Classical

/-- A finite bounded lattice is complete. -/
@[reducible]
noncomputable def Fintype.toCompleteLattice [hl : Lattice α] [hb : BoundedOrder α] : CompleteLattice α :=
  { hl, hb with sup := fun s => s.to_finset.sup id, inf := fun s => s.to_finset.inf id,
    le_Sup := fun _ _ ha => Finset.le_sup (Set.mem_to_finset.mpr ha),
    Sup_le := fun s _ ha => Finset.sup_le fun b hb => ha _ $ Set.mem_to_finset.mp hb,
    Inf_le := fun _ _ ha => Finset.inf_le (Set.mem_to_finset.mpr ha),
    le_Inf := fun s _ ha => Finset.le_inf fun b hb => ha _ $ Set.mem_to_finset.mp hb }

/-- A finite bounded linear order is complete. -/
@[reducible]
noncomputable def Fintype.toCompleteLinearOrder [h : LinearOrderₓ α] [BoundedOrder α] : CompleteLinearOrder α :=
  { Fintype.toCompleteLattice α, h with }

end BoundedOrder

section Nonempty

variable (α) [Nonempty α]

/-- A nonempty finite lattice is complete. If the lattice is already a `bounded_order`, then use
`fintype.to_complete_lattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
@[reducible]
noncomputable def Fintype.toCompleteLatticeOfLattice [Lattice α] : CompleteLattice α :=
  @Fintype.toCompleteLattice _ _ _ $ @Fintype.toBoundedOrder α _ ⟨Classical.arbitrary α⟩ _

/-- A nonempty finite linear order is complete. If the linear order is already a `bounded_order`,
then use `fintype.to_complete_linear_order` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
@[reducible]
noncomputable def Fintype.toCompleteLinearOrderOfLinearOrder [h : LinearOrderₓ α] : CompleteLinearOrder α :=
  { Fintype.toCompleteLatticeOfLattice α, h with }

end Nonempty

/-! ### `fin` -/


noncomputable instance Finₓ.completeLinearOrder {n : ℕ} : CompleteLinearOrder (Finₓ (n + 1)) :=
  Fintype.toCompleteLinearOrder _

