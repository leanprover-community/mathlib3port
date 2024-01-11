/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import LinearAlgebra.Isomorphisms
import Order.JordanHolder

#align_import ring_theory.simple_module from "leanprover-community/mathlib"@"19cb3751e5e9b3d97adb51023949c50c13b5fdfd"

/-!
# Simple Modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print IsSimpleModule /-
/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
abbrev IsSimpleModule :=
  IsSimpleOrder (Submodule R M)
#align is_simple_module IsSimpleModule
-/

#print IsSemisimpleModule /-
/-- A module is semisimple when every submodule has a complement, or equivalently, the module
  is a direct sum of simple modules. -/
abbrev IsSemisimpleModule :=
  ComplementedLattice (Submodule R M)
#align is_semisimple_module IsSemisimpleModule
-/

#print IsSimpleModule.nontrivial /-
-- Making this an instance causes the linter to complain of "dangerous instances"
theorem IsSimpleModule.nontrivial [IsSimpleModule R M] : Nontrivial M :=
  ⟨⟨0, by
      have h : (⊥ : Submodule R M) ≠ ⊤ := bot_ne_top
      contrapose! h
      ext
      simp [Submodule.mem_bot, Submodule.mem_top, h x]⟩⟩
#align is_simple_module.nontrivial IsSimpleModule.nontrivial
-/

variable {R} {M} {m : Submodule R M} {N : Type _} [AddCommGroup N] [Module R N]

#print IsSimpleModule.congr /-
theorem IsSimpleModule.congr (l : M ≃ₗ[R] N) [IsSimpleModule R N] : IsSimpleModule R M :=
  (Submodule.orderIsoMapComap l).IsSimpleOrder
#align is_simple_module.congr IsSimpleModule.congr
-/

#print isSimpleModule_iff_isAtom /-
theorem isSimpleModule_iff_isAtom : IsSimpleModule R m ↔ IsAtom m :=
  by
  rw [← Set.isSimpleOrder_Iic_iff_isAtom]
  apply OrderIso.isSimpleOrder_iff
  exact Submodule.MapSubtype.relIso m
#align is_simple_module_iff_is_atom isSimpleModule_iff_isAtom
-/

#print isSimpleModule_iff_isCoatom /-
theorem isSimpleModule_iff_isCoatom : IsSimpleModule R (M ⧸ m) ↔ IsCoatom m :=
  by
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom]
  apply OrderIso.isSimpleOrder_iff
  exact Submodule.comapMkQRelIso m
#align is_simple_module_iff_is_coatom isSimpleModule_iff_isCoatom
-/

#print covBy_iff_quot_is_simple /-
theorem covBy_iff_quot_is_simple {A B : Submodule R M} (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleModule R (B ⧸ Submodule.comap B.Subtype A) :=
  by
  set f : Submodule R B ≃o Set.Iic B := Submodule.MapSubtype.relIso B with hf
  rw [covBy_iff_coatom_Iic hAB, isSimpleModule_iff_isCoatom, ← OrderIso.isCoatom_iff f, hf]
  simp [-OrderIso.isCoatom_iff, Submodule.MapSubtype.relIso, Submodule.map_comap_subtype,
    inf_eq_right.2 hAB]
#align covby_iff_quot_is_simple covBy_iff_quot_is_simple
-/

namespace IsSimpleModule

variable [hm : IsSimpleModule R m]

#print IsSimpleModule.isAtom /-
@[simp]
theorem isAtom : IsAtom m :=
  isSimpleModule_iff_isAtom.1 hm
#align is_simple_module.is_atom IsSimpleModule.isAtom
-/

end IsSimpleModule

#print is_semisimple_of_sSup_simples_eq_top /-
theorem is_semisimple_of_sSup_simples_eq_top
    (h : sSup {m : Submodule R M | IsSimpleModule R m} = ⊤) : IsSemisimpleModule R M :=
  complementedLattice_of_sSup_atoms_eq_top (by simp_rw [← h, isSimpleModule_iff_isAtom])
#align is_semisimple_of_Sup_simples_eq_top is_semisimple_of_sSup_simples_eq_top
-/

namespace IsSemisimpleModule

variable [IsSemisimpleModule R M]

#print IsSemisimpleModule.sSup_simples_eq_top /-
theorem sSup_simples_eq_top : sSup {m : Submodule R M | IsSimpleModule R m} = ⊤ :=
  by
  simp_rw [isSimpleModule_iff_isAtom]
  exact sSup_atoms_eq_top
#align is_semisimple_module.Sup_simples_eq_top IsSemisimpleModule.sSup_simples_eq_top
-/

#print IsSemisimpleModule.is_semisimple_submodule /-
instance is_semisimple_submodule {m : Submodule R M} : IsSemisimpleModule R m :=
  haveI f : Submodule R m ≃o Set.Iic m := Submodule.MapSubtype.relIso m
  f.complemented_lattice_iff.2 IsModularLattice.complementedLattice_Iic
#align is_semisimple_module.is_semisimple_submodule IsSemisimpleModule.is_semisimple_submodule
-/

end IsSemisimpleModule

#print is_semisimple_iff_top_eq_sSup_simples /-
theorem is_semisimple_iff_top_eq_sSup_simples :
    sSup {m : Submodule R M | IsSimpleModule R m} = ⊤ ↔ IsSemisimpleModule R M :=
  ⟨is_semisimple_of_sSup_simples_eq_top, by intro; exact IsSemisimpleModule.sSup_simples_eq_top⟩
#align is_semisimple_iff_top_eq_Sup_simples is_semisimple_iff_top_eq_sSup_simples
-/

namespace LinearMap

#print LinearMap.injective_or_eq_zero /-
theorem injective_or_eq_zero [IsSimpleModule R M] (f : M →ₗ[R] N) : Function.Injective f ∨ f = 0 :=
  by
  rw [← ker_eq_bot, ← ker_eq_top]
  apply eq_bot_or_eq_top
#align linear_map.injective_or_eq_zero LinearMap.injective_or_eq_zero
-/

#print LinearMap.injective_of_ne_zero /-
theorem injective_of_ne_zero [IsSimpleModule R M] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Injective f :=
  f.injective_or_eq_zero.resolve_right h
#align linear_map.injective_of_ne_zero LinearMap.injective_of_ne_zero
-/

#print LinearMap.surjective_or_eq_zero /-
theorem surjective_or_eq_zero [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Surjective f ∨ f = 0 :=
  by
  rw [← range_eq_top, ← range_eq_bot, or_comm']
  apply eq_bot_or_eq_top
#align linear_map.surjective_or_eq_zero LinearMap.surjective_or_eq_zero
-/

#print LinearMap.surjective_of_ne_zero /-
theorem surjective_of_ne_zero [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Surjective f :=
  f.surjective_or_eq_zero.resolve_right h
#align linear_map.surjective_of_ne_zero LinearMap.surjective_of_ne_zero
-/

#print LinearMap.bijective_or_eq_zero /-
/-- **Schur's Lemma** for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Bijective f ∨ f = 0 := by
  by_cases h : f = 0
  · right
    exact h
  exact Or.intro_left _ ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩
#align linear_map.bijective_or_eq_zero LinearMap.bijective_or_eq_zero
-/

#print LinearMap.bijective_of_ne_zero /-
theorem bijective_of_ne_zero [IsSimpleModule R M] [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Bijective f :=
  f.bijective_or_eq_zero.resolve_right h
#align linear_map.bijective_of_ne_zero LinearMap.bijective_of_ne_zero
-/

#print LinearMap.isCoatom_ker_of_surjective /-
theorem isCoatom_ker_of_surjective [IsSimpleModule R N] {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : IsCoatom f.ker :=
  by
  rw [← isSimpleModule_iff_isCoatom]
  exact IsSimpleModule.congr (f.quot_ker_equiv_of_surjective hf)
#align linear_map.is_coatom_ker_of_surjective LinearMap.isCoatom_ker_of_surjective
-/

#print Module.End.divisionRing /-
/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable instance Module.End.divisionRing [DecidableEq (Module.End R M)] [IsSimpleModule R M] :
    DivisionRing (Module.End R M) :=
  {
    (Module.End.ring :
      Ring
        (Module.End R
          M)) with
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
#align module.End.division_ring Module.End.divisionRing
-/

end LinearMap

#print JordanHolderModule.instJordanHolderLattice /-
instance JordanHolderModule.instJordanHolderLattice : JordanHolderLattice (Submodule R M)
    where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal x y := CovBy.lt
  sup_eq_of_isMaximal x y z hxz hyz := WCovBy.sup_eq hxz.WCovBy hyz.WCovBy
  isMaximal_inf_left_of_isMaximal_sup A B := inf_covBy_of_covBy_sup_of_covBy_sup_left
  Iso X Y := Nonempty <| (X.2 ⧸ X.1.comap X.2.Subtype) ≃ₗ[R] Y.2 ⧸ Y.1.comap Y.2.Subtype
  iso_symm := fun A B ⟨f⟩ => ⟨f.symm⟩
  iso_trans := fun A B C ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  second_iso A B h :=
    ⟨by rw [sup_comm, inf_comm]; exact (LinearMap.quotientInfEquivSupQuotient B A).symm⟩
#align jordan_holder_module JordanHolderModule.instJordanHolderLattice
-/

