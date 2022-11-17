/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.Analysis.Normed.Order.Lattice
import Mathbin.MeasureTheory.Function.LpSpace

/-!
# Order related properties of Lp spaces

### Results

- `Lp E p μ` is an `ordered_add_comm_group` when `E` is a `normed_lattice_add_comm_group`.

### TODO

- move definitions of `Lp.pos_part` and `Lp.neg_part` to this file, and define them as
  `has_pos_part.pos` and `has_pos_part.neg` given by the lattice structure.

-/


open TopologicalSpace MeasureTheory LatticeOrderedCommGroup

open Ennreal

variable {α E : Type _} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

namespace MeasureTheory

namespace LpCat

section Order

variable [NormedLatticeAddCommGroup E]

theorem coe_fn_le (f g : lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← ae_eq_fun.coe_fn_le, ← coe_fn_coe_base, ← coe_fn_coe_base]
#align measure_theory.Lp.coe_fn_le MeasureTheory.lp.coe_fn_le

theorem coe_fn_nonneg (f : lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← coe_fn_le]
  have h0 := Lp.coe_fn_zero E p μ
  constructor <;> intro h <;> filter_upwards [h, h0] with _ _ h2
  · rwa [h2]
    
  · rwa [← h2]
    
#align measure_theory.Lp.coe_fn_nonneg MeasureTheory.lp.coe_fn_nonneg

instance : CovariantClass (lp E p μ) (lp E p μ) (· + ·) (· ≤ ·) := by
  refine' ⟨fun f g₁ g₂ hg₁₂ => _⟩
  rw [← coe_fn_le] at hg₁₂⊢
  filter_upwards [coe_fn_add f g₁, coe_fn_add f g₂, hg₁₂] with _ h1 h2 h3
  rw [h1, h2, Pi.add_apply, Pi.add_apply]
  exact add_le_add le_rfl h3

instance : OrderedAddCommGroup (lp E p μ) :=
  { Subtype.partialOrder _, AddSubgroup.toAddCommGroup _ with add_le_add_left := fun f g => add_le_add_left }

theorem _root_.measure_theory.mem_ℒp.sup {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f ⊔ g) p μ :=
  Memℒp.mono' (hf.norm.add hg.norm) (hf.1.sup hg.1) (Filter.eventually_of_forall fun x => norm_sup_le_add (f x) (g x))
#align measure_theory.Lp._root_.measure_theory.mem_ℒp.sup measure_theory.Lp._root_.measure_theory.mem_ℒp.sup

theorem _root_.measure_theory.mem_ℒp.inf {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f ⊓ g) p μ :=
  Memℒp.mono' (hf.norm.add hg.norm) (hf.1.inf hg.1) (Filter.eventually_of_forall fun x => norm_inf_le_add (f x) (g x))
#align measure_theory.Lp._root_.measure_theory.mem_ℒp.inf measure_theory.Lp._root_.measure_theory.mem_ℒp.inf

theorem _root_.measure_theory.mem_ℒp.abs {f : α → E} (hf : Memℒp f p μ) : Memℒp |f| p μ :=
  hf.sup hf.neg
#align measure_theory.Lp._root_.measure_theory.mem_ℒp.abs measure_theory.Lp._root_.measure_theory.mem_ℒp.abs

instance : Lattice (lp E p μ) :=
  Subtype.lattice
    (fun f g hf hg => by
      rw [mem_Lp_iff_mem_ℒp] at *
      exact (mem_ℒp_congr_ae (ae_eq_fun.coe_fn_sup _ _)).mpr (hf.sup hg))
    fun f g hf hg => by
    rw [mem_Lp_iff_mem_ℒp] at *
    exact (mem_ℒp_congr_ae (ae_eq_fun.coe_fn_inf _ _)).mpr (hf.inf hg)

theorem coe_fn_sup (f g : lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g :=
  AeEqFun.coe_fn_sup _ _
#align measure_theory.Lp.coe_fn_sup MeasureTheory.lp.coe_fn_sup

theorem coe_fn_inf (f g : lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g :=
  AeEqFun.coe_fn_inf _ _
#align measure_theory.Lp.coe_fn_inf MeasureTheory.lp.coe_fn_inf

theorem coe_fn_abs (f : lp E p μ) : ⇑|f| =ᵐ[μ] fun x => |f x| :=
  AeEqFun.coe_fn_abs _
#align measure_theory.Lp.coe_fn_abs MeasureTheory.lp.coe_fn_abs

noncomputable instance [Fact (1 ≤ p)] : NormedLatticeAddCommGroup (lp E p μ) :=
  { lp.lattice, lp.normedAddCommGroup with add_le_add_left := fun f g => add_le_add_left,
    solid := fun f g hfg => by
      rw [← coe_fn_le] at hfg
      simp_rw [Lp.norm_def, Ennreal.to_real_le_to_real (Lp.snorm_ne_top f) (Lp.snorm_ne_top g)]
      refine' snorm_mono_ae _
      filter_upwards [hfg, Lp.coe_fn_abs f, Lp.coe_fn_abs g] with x hx hxf hxg
      rw [hxf, hxg] at hx
      exact solid hx }

end Order

end LpCat

end MeasureTheory

