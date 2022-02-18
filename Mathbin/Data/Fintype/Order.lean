import Mathbin.Data.Fintype.Basic
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Data.Finset.Order

/-!
# Order structures on finite types

This file provides order instances on fintypes.

## Computable instances

On a `fintype`, we can construct
* an `order_bot` from `semilattice_inf`.
* an `order_top` from `semilattice_sup`.
* a `bounded_order` from `lattice`.

Those are marked as `def` to avoid defeqness issues.

## Completion instances

Those instances are noncomputable because the definitions of `Sup` and `Inf` use `set.to_finset` and
set membership is undecidable in general.

On a `fintype`, we can promote:
* a `lattice` to a `complete_lattice`.
* a `distrib_lattice` to a `complete_distrib_lattice`.
* a `linear_order`  to a `complete_linear_order`.
* a `boolean_algebra` to a `complete_boolean_algebra`.

Those are marked as `def` to avoid typeclass loops.

## Concrete instances

We provide a few instances for concrete types:
* `fin.complete_linear_order`
* `bool.complete_linear_order`
* `bool.complete_boolean_algebra`
-/


open Finset

namespace Fintype

variable {ι α : Type _} [Fintype ι] [Fintype α]

section Nonempty

variable (α) [Nonempty α]

/-- Constructs the `⊥` of a finite nonempty `semilattice_inf`. -/
@[reducible]
def to_order_bot [SemilatticeInf α] : OrderBot α where
  bot := univ.inf' univ_nonempty id
  bot_le := fun a => inf'_le _ <| mem_univ a

/-- Constructs the `⊤` of a finite nonempty `semilattice_sup` -/
@[reducible]
def to_order_top [SemilatticeSup α] : OrderTop α where
  top := univ.sup' univ_nonempty id
  le_top := fun a => le_sup' _ <| mem_univ a

/-- Constructs the `⊤` and `⊥` of a finite nonempty `lattice`. -/
@[reducible]
def to_bounded_order [Lattice α] : BoundedOrder α :=
  { toOrderBot α, toOrderTop α with }

end Nonempty

section BoundedOrder

variable (α)

open_locale Classical

/-- A finite bounded lattice is complete. -/
@[reducible]
noncomputable def to_complete_lattice [Lattice α] [BoundedOrder α] : CompleteLattice α :=
  { ‹Lattice α›, ‹BoundedOrder α› with sup := fun s => s.toFinset.sup id, inf := fun s => s.toFinset.inf id,
    le_Sup := fun _ _ ha => Finset.le_sup (Set.mem_to_finset.mpr ha),
    Sup_le := fun s _ ha => Finset.sup_le fun b hb => ha _ <| Set.mem_to_finset.mp hb,
    Inf_le := fun _ _ ha => Finset.inf_le (Set.mem_to_finset.mpr ha),
    le_Inf := fun s _ ha => Finset.le_inf fun b hb => ha _ <| Set.mem_to_finset.mp hb }

/-- A finite bounded distributive lattice is completely distributive. -/
@[reducible]
noncomputable def to_complete_distrib_lattice [DistribLattice α] [BoundedOrder α] : CompleteDistribLattice α :=
  { toCompleteLattice α with
    infi_sup_le_sup_Inf := fun a s => by
      convert (Finset.inf_sup_distrib_left _ _ _).Ge
      convert (Finset.inf_eq_infi _ _).symm
      simp_rw [Set.mem_to_finset]
      rfl,
    inf_Sup_le_supr_inf := fun a s => by
      convert (Finset.sup_inf_distrib_left _ _ _).le
      convert (Finset.sup_eq_supr _ _).symm
      simp_rw [Set.mem_to_finset]
      rfl }

/-- A finite bounded linear order is complete. -/
@[reducible]
noncomputable def to_complete_linear_order [LinearOrderₓ α] [BoundedOrder α] : CompleteLinearOrder α :=
  { toCompleteLattice α, ‹LinearOrderₓ α› with }

/-- A finite boolean algebra is complete. -/
@[reducible]
noncomputable def to_complete_boolean_algebra [BooleanAlgebra α] : CompleteBooleanAlgebra α :=
  { Fintype.toCompleteDistribLattice α, ‹BooleanAlgebra α› with }

end BoundedOrder

section Nonempty

variable (α) [Nonempty α]

/-- A nonempty finite lattice is complete. If the lattice is already a `bounded_order`, then use
`fintype.to_complete_lattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
@[reducible]
noncomputable def to_complete_lattice_of_nonempty [Lattice α] : CompleteLattice α :=
  @toCompleteLattice _ _ _ <| @toBoundedOrder α _ ⟨Classical.arbitrary α⟩ _

/-- A nonempty finite linear order is complete. If the linear order is already a `bounded_order`,
then use `fintype.to_complete_linear_order` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
@[reducible]
noncomputable def to_complete_linear_order_of_nonempty [LinearOrderₓ α] : CompleteLinearOrder α :=
  { toCompleteLatticeOfNonempty α, ‹LinearOrderₓ α› with }

end Nonempty

end Fintype

/-! ### Concrete instances -/


noncomputable instance {n : ℕ} : CompleteLinearOrder (Finₓ (n + 1)) :=
  Fintype.toCompleteLinearOrder _

noncomputable instance : CompleteLinearOrder Bool :=
  Fintype.toCompleteLinearOrder _

noncomputable instance : CompleteBooleanAlgebra Bool :=
  Fintype.toCompleteBooleanAlgebra _

/-! ### Directed Orders -/


variable {α : Type _}

theorem Directed.fintype_le {r : α → α → Prop} [IsTrans α r] {β γ : Type _} [Nonempty γ] {f : γ → α} [Fintype β]
    (D : Directed r f) (g : β → γ) : ∃ z, ∀ i, r (f (g i)) (f z) := by
  classical
  obtain ⟨z, hz⟩ := D.finset_le (Finset.image g Finset.univ)
  exact ⟨z, fun i => hz (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))⟩

theorem Fintype.exists_le [Nonempty α] [Preorderₓ α] [IsDirected α (· ≤ ·)] {β : Type _} [Fintype β] (f : β → α) :
    ∃ M, ∀ i, f i ≤ M :=
  directed_id.fintype_le _

theorem Fintype.bdd_above_range [Nonempty α] [Preorderₓ α] [IsDirected α (· ≤ ·)] {β : Type _} [Fintype β] (f : β → α) :
    BddAbove (Set.Range f) := by
  obtain ⟨M, hM⟩ := Fintype.exists_le f
  refine' ⟨M, fun a ha => _⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

