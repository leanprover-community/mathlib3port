/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.MeasureTheory.Function.LpSpace
import Mathbin.Analysis.NormedSpace.LatticeOrderedGroup

/-!
# Order related properties of Lp spaces

### Results

- `Lp E p μ` is an `ordered_add_comm_group` when `E` is a `normed_lattice_add_comm_group`.

### TODO

- move definitions of `Lp.pos_part` and `Lp.neg_part` to this file, and define them as
  `has_pos_part.pos` and `has_pos_part.neg` given by the lattice structure.
- show that if `E` is a `normed_lattice_add_comm_group` then so is `Lp E p μ` for `1 ≤ p`. In
  particular, this shows `order_closed_topology` for `Lp`.

-/


open TopologicalSpace MeasureTheory LatticeOrderedCommGroup

open_locale Ennreal

variable {α E : Type _} {m : MeasurableSpace α} {μ : Measureₓ α} {p : ℝ≥0∞}

namespace MeasureTheory

namespace Lp

section Order

variable [NormedLatticeAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem coe_fn_le (f g : lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← ae_eq_fun.coe_fn_le, ← coe_fn_coe_base, ← coe_fn_coe_base]

theorem coe_fn_nonneg (f : lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← coe_fn_le]
  have h0 := Lp.coe_fn_zero E p μ
  constructor <;> intro h <;> filter_upwards [h, h0] with _ _ h2
  · rwa [h2]
    
  · rwa [← h2]
    

instance : CovariantClass (lp E p μ) (lp E p μ) (· + ·) (· ≤ ·) := by
  refine' ⟨fun f g₁ g₂ hg₁₂ => _⟩
  rw [← coe_fn_le] at hg₁₂⊢
  filter_upwards [coe_fn_add f g₁, coe_fn_add f g₂, hg₁₂] with _ h1 h2 h3
  rw [h1, h2, Pi.add_apply, Pi.add_apply]
  exact add_le_add le_rfl h3

instance : OrderedAddCommGroup (lp E p μ) :=
  { Subtype.partialOrder _, AddSubgroup.toAddCommGroup _ with
    add_le_add_left := fun f g hfg f' => add_le_add_left hfg f' }

end Order

end Lp

end MeasureTheory

