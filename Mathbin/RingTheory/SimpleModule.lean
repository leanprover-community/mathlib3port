/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module ring_theory.simple_module
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Isomorphisms
import Mathbin.Order.JordanHolder

/-!
# Simple Modules

## Main Definitions
  * `is_simple_module` indicates that a module has no proper submodules
  (the only submodules are `⊥` and `⊤`).
  * `is_semisimple_module` indicates that every submodule has a complement, or equivalently,
    the module is a direct sum of simple modules.
  * A `division_ring` structure on the endomorphism ring of a simple module.

## Main Results
  * Schur's Lemma: `bijective_or_eq_zero` shows that a linear map between simple modules
  is either bijective or 0, leading to a `division_ring` structure on the endomorphism ring.

## TODO
  * Artin-Wedderburn Theory
  * Unify with the work on Schur's Lemma in a category theory context

-/


variable (R : Type _) [Ring R] (M : Type _) [AddCommGroup M] [Module R M]

/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
abbrev IsSimpleModule :=
  IsSimpleOrder (Submodule R M)
#align is_simple_module IsSimpleModule

/-- A module is semisimple when every submodule has a complement, or equivalently, the module
  is a direct sum of simple modules. -/
abbrev IsSemisimpleModule :=
  ComplementedLattice (Submodule R M)
#align is_semisimple_module IsSemisimpleModule

-- Making this an instance causes the linter to complain of "dangerous instances"
theorem IsSimpleModule.nontrivial [IsSimpleModule R M] : Nontrivial M :=
  ⟨⟨0, by 
      have h : (⊥ : Submodule R M) ≠ ⊤ := bot_ne_top
      contrapose! h
      ext
      simp [Submodule.mem_bot, Submodule.mem_top, h x]⟩⟩
#align is_simple_module.nontrivial IsSimpleModule.nontrivial

variable {R} {M} {m : Submodule R M} {N : Type _} [AddCommGroup N] [Module R N]

theorem IsSimpleModule.congr (l : M ≃ₗ[R] N) [IsSimpleModule R N] : IsSimpleModule R M :=
  (Submodule.orderIsoMapComap l).IsSimpleOrder
#align is_simple_module.congr IsSimpleModule.congr

theorem is_simple_module_iff_is_atom : IsSimpleModule R m ↔ IsAtom m := by
  rw [← Set.is_simple_order_Iic_iff_is_atom]
  apply OrderIso.is_simple_order_iff
  exact Submodule.MapSubtype.relIso m
#align is_simple_module_iff_is_atom is_simple_module_iff_is_atom

theorem is_simple_module_iff_is_coatom : IsSimpleModule R (M ⧸ m) ↔ IsCoatom m := by
  rw [← Set.is_simple_order_Ici_iff_is_coatom]
  apply OrderIso.is_simple_order_iff
  exact Submodule.ComapMkq.relIso m
#align is_simple_module_iff_is_coatom is_simple_module_iff_is_coatom

theorem covby_iff_quot_is_simple {A B : Submodule R M} (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleModule R (B ⧸ Submodule.comap B.Subtype A) := by
  set f : Submodule R B ≃o Set.Iic B := Submodule.MapSubtype.relIso B with hf
  rw [covby_iff_coatom_Iic hAB, is_simple_module_iff_is_coatom, ← OrderIso.is_coatom_iff f, hf]
  simp [-OrderIso.is_coatom_iff, Submodule.MapSubtype.relIso, Submodule.map_comap_subtype,
    inf_eq_right.2 hAB]
#align covby_iff_quot_is_simple covby_iff_quot_is_simple

namespace IsSimpleModule

variable [hm : IsSimpleModule R m]

@[simp]
theorem is_atom : IsAtom m :=
  is_simple_module_iff_is_atom.1 hm
#align is_simple_module.is_atom IsSimpleModule.is_atom

end IsSimpleModule

theorem is_semisimple_of_Sup_simples_eq_top
    (h : supₛ { m : Submodule R M | IsSimpleModule R m } = ⊤) : IsSemisimpleModule R M :=
  complemented_lattice_of_Sup_atoms_eq_top (by simp_rw [← h, is_simple_module_iff_is_atom])
#align is_semisimple_of_Sup_simples_eq_top is_semisimple_of_Sup_simples_eq_top

namespace IsSemisimpleModule

variable [IsSemisimpleModule R M]

theorem Sup_simples_eq_top : supₛ { m : Submodule R M | IsSimpleModule R m } = ⊤ := by
  simp_rw [is_simple_module_iff_is_atom]
  exact Sup_atoms_eq_top
#align is_semisimple_module.Sup_simples_eq_top IsSemisimpleModule.Sup_simples_eq_top

instance is_semisimple_submodule {m : Submodule R M} : IsSemisimpleModule R m :=
  haveI f : Submodule R m ≃o Set.Iic m := Submodule.MapSubtype.relIso m
  f.complemented_lattice_iff.2 IsModularLattice.complemented_lattice_Iic
#align is_semisimple_module.is_semisimple_submodule IsSemisimpleModule.is_semisimple_submodule

end IsSemisimpleModule

theorem is_semisimple_iff_top_eq_Sup_simples :
    supₛ { m : Submodule R M | IsSimpleModule R m } = ⊤ ↔ IsSemisimpleModule R M :=
  ⟨is_semisimple_of_Sup_simples_eq_top, by 
    intro
    exact IsSemisimpleModule.Sup_simples_eq_top⟩
#align is_semisimple_iff_top_eq_Sup_simples is_semisimple_iff_top_eq_Sup_simples

namespace LinearMap

theorem injective_or_eq_zero [IsSimpleModule R M] (f : M →ₗ[R] N) : Function.Injective f ∨ f = 0 :=
  by 
  rw [← ker_eq_bot, ← ker_eq_top]
  apply eq_bot_or_eq_top
#align linear_map.injective_or_eq_zero LinearMap.injective_or_eq_zero

theorem injective_of_ne_zero [IsSimpleModule R M] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Injective f :=
  f.injective_or_eq_zero.resolve_right h
#align linear_map.injective_of_ne_zero LinearMap.injective_of_ne_zero

theorem surjective_or_eq_zero [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Surjective f ∨ f = 0 := by
  rw [← range_eq_top, ← range_eq_bot, or_comm']
  apply eq_bot_or_eq_top
#align linear_map.surjective_or_eq_zero LinearMap.surjective_or_eq_zero

theorem surjective_of_ne_zero [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Surjective f :=
  f.surjective_or_eq_zero.resolve_right h
#align linear_map.surjective_of_ne_zero LinearMap.surjective_of_ne_zero

/-- **Schur's Lemma** for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Bijective f ∨ f = 0 := by 
  by_cases h : f = 0
  · right
    exact h
  exact Or.intro_left _ ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩
#align linear_map.bijective_or_eq_zero LinearMap.bijective_or_eq_zero

theorem bijective_of_ne_zero [IsSimpleModule R M] [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Bijective f :=
  f.bijective_or_eq_zero.resolve_right h
#align linear_map.bijective_of_ne_zero LinearMap.bijective_of_ne_zero

theorem is_coatom_ker_of_surjective [IsSimpleModule R N] {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : IsCoatom f.ker := by
  rw [← is_simple_module_iff_is_coatom]
  exact IsSimpleModule.congr (f.quot_ker_equiv_of_surjective hf)
#align linear_map.is_coatom_ker_of_surjective LinearMap.is_coatom_ker_of_surjective

/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable instance Module.EndCat.divisionRing [DecidableEq (Module.EndCat R M)]
    [IsSimpleModule R M] : DivisionRing (Module.EndCat R M) :=
  { (Module.EndCat.ring : Ring (Module.EndCat R M)) with
    inv := fun f =>
      if h : f = 0 then 0
      else
        LinearMap.inverse f (Equiv.ofBijective _ (bijective_of_ne_zero h)).invFun
          (Equiv.ofBijective _ (bijective_of_ne_zero h)).left_inv
          (Equiv.ofBijective _ (bijective_of_ne_zero h)).right_inv
    exists_pair_ne :=
      ⟨0, 1, by 
        haveI := IsSimpleModule.nontrivial R M
        have h := exists_pair_ne M
        contrapose! h
        intro x y
        simp_rw [ext_iff, one_apply, zero_apply] at h
        rw [← h x, h y]⟩
    mul_inv_cancel := by 
      intro a a0
      change a * dite _ _ _ = 1
      ext
      rw [dif_neg a0, mul_eq_comp, one_apply, comp_apply]
      exact (Equiv.ofBijective _ (bijective_of_ne_zero a0)).right_inv x
    inv_zero := dif_pos rfl }
#align module.End.division_ring Module.EndCat.divisionRing

end LinearMap

instance jordanHolderModule :
    JordanHolderLattice (Submodule R
        M) where 
  IsMaximal := (· ⋖ ·)
  lt_of_is_maximal x y := Covby.lt
  sup_eq_of_is_maximal x y z hxz hyz := Wcovby.sup_eq hxz.Wcovby hyz.Wcovby
  is_maximal_inf_left_of_is_maximal_sup A B := inf_covby_of_covby_sup_of_covby_sup_left
  Iso X Y := Nonempty <| (X.2 ⧸ X.1.comap X.2.Subtype) ≃ₗ[R] Y.2 ⧸ Y.1.comap Y.2.Subtype
  iso_symm := fun A B ⟨f⟩ => ⟨f.symm⟩
  iso_trans := fun A B C ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  second_iso A B h :=
    ⟨by 
      rw [sup_comm, inf_comm]
      exact (LinearMap.quotientInfEquivSupQuotient B A).symm⟩
#align jordan_holder_module jordanHolderModule

