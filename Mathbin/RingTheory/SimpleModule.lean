import Mathbin.LinearAlgebra.Basic 
import Mathbin.Order.Atoms

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


variable (R : Type _) [Ringₓ R] (M : Type _) [AddCommGroupₓ M] [Module R M]

/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
abbrev IsSimpleModule :=
  IsSimpleLattice (Submodule R M)

/-- A module is semisimple when every submodule has a complement, or equivalently, the module
  is a direct sum of simple modules. -/
abbrev IsSemisimpleModule :=
  IsComplemented (Submodule R M)

-- error in RingTheory.SimpleModule: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_simple_module.nontrivial [is_simple_module R M] : nontrivial M :=
⟨⟨0, begin
    have [ident h] [":", expr «expr ≠ »((«expr⊥»() : submodule R M), «expr⊤»())] [":=", expr bot_ne_top],
    contrapose ["!"] [ident h],
    ext [] [] [],
    simp [] [] [] ["[", expr submodule.mem_bot, ",", expr submodule.mem_top, ",", expr h x, "]"] [] []
  end⟩⟩

variable {R} {M} {m : Submodule R M} {N : Type _} [AddCommGroupₓ N] [Module R N]

theorem is_simple_module_iff_is_atom : IsSimpleModule R m ↔ IsAtom m :=
  by 
    rw [←Set.is_simple_lattice_Iic_iff_is_atom]
    apply OrderIso.is_simple_lattice_iff 
    exact Submodule.MapSubtype.relIso m

namespace IsSimpleModule

variable [hm : IsSimpleModule R m]

@[simp]
theorem IsAtom : IsAtom m :=
  is_simple_module_iff_is_atom.1 hm

end IsSimpleModule

theorem is_semisimple_of_Sup_simples_eq_top (h : Sup { m:Submodule R M | IsSimpleModule R m } = ⊤) :
  IsSemisimpleModule R M :=
  is_complemented_of_Sup_atoms_eq_top
    (by 
      simpRw [←h, is_simple_module_iff_is_atom])

namespace IsSemisimpleModule

variable [IsSemisimpleModule R M]

theorem Sup_simples_eq_top : Sup { m:Submodule R M | IsSimpleModule R m } = ⊤ :=
  by 
    simpRw [is_simple_module_iff_is_atom]
    exact Sup_atoms_eq_top

-- error in RingTheory.SimpleModule: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance is_semisimple_submodule {m : submodule R M} : is_semisimple_module R m :=
begin
  have [ident f] [":", expr «expr ≃o »(submodule R m, set.Iic m)] [":=", expr submodule.map_subtype.rel_iso m],
  exact [expr f.is_complemented_iff.2 is_modular_lattice.is_complemented_Iic]
end

end IsSemisimpleModule

theorem is_semisimple_iff_top_eq_Sup_simples :
  Sup { m:Submodule R M | IsSimpleModule R m } = ⊤ ↔ IsSemisimpleModule R M :=
  ⟨is_semisimple_of_Sup_simples_eq_top,
    by 
      intro 
      exact IsSemisimpleModule.Sup_simples_eq_top⟩

namespace LinearMap

theorem injective_or_eq_zero [IsSimpleModule R M] (f : M →ₗ[R] N) : Function.Injective f ∨ f = 0 :=
  by 
    rw [←ker_eq_bot, ←ker_eq_top]
    apply eq_bot_or_eq_top

theorem injective_of_ne_zero [IsSimpleModule R M] {f : M →ₗ[R] N} (h : f ≠ 0) : Function.Injective f :=
  f.injective_or_eq_zero.resolve_right h

theorem surjective_or_eq_zero [IsSimpleModule R N] (f : M →ₗ[R] N) : Function.Surjective f ∨ f = 0 :=
  by 
    rw [←range_eq_top, ←range_eq_bot, or_comm]
    apply eq_bot_or_eq_top

theorem surjective_of_ne_zero [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) : Function.Surjective f :=
  f.surjective_or_eq_zero.resolve_right h

/-- **Schur's Lemma** for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) : Function.Bijective f ∨ f = 0 :=
  by 
    byCases' h : f = 0
    ·
      right 
      exact h 
    exact Or.intro_left _ ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩

theorem bijective_of_ne_zero [IsSimpleModule R M] [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
  Function.Bijective f :=
  f.bijective_or_eq_zero.resolve_right h

-- error in RingTheory.SimpleModule: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable
instance _root_.module.End.division_ring
[decidable_eq (module.End R M)]
[is_simple_module R M] : division_ring (module.End R M) :=
{ inv := λ
  f, if h : «expr = »(f, 0) then 0 else linear_map.inverse f (equiv.of_bijective _ (bijective_of_ne_zero h)).inv_fun (equiv.of_bijective _ (bijective_of_ne_zero h)).left_inv (equiv.of_bijective _ (bijective_of_ne_zero h)).right_inv,
  exists_pair_ne := ⟨0, 1, begin
     haveI [] [] [":=", expr is_simple_module.nontrivial R M],
     have [ident h] [] [":=", expr exists_pair_ne M],
     contrapose ["!"] [ident h],
     intros [ident x, ident y],
     simp_rw ["[", expr ext_iff, ",", expr one_apply, ",", expr zero_apply, "]"] ["at", ident h],
     rw ["[", "<-", expr h x, ",", expr h y, "]"] []
   end⟩,
  mul_inv_cancel := begin
    intros [ident a, ident a0],
    change [expr «expr = »(«expr * »(a, dite _ _ _), 1)] [] [],
    ext [] [] [],
    rw ["[", expr dif_neg a0, ",", expr mul_eq_comp, ",", expr one_apply, ",", expr comp_apply, "]"] [],
    exact [expr (equiv.of_bijective _ (bijective_of_ne_zero a0)).right_inv x]
  end,
  inv_zero := dif_pos rfl,
  ..(module.End.ring : ring (module.End R M)) }

end LinearMap

