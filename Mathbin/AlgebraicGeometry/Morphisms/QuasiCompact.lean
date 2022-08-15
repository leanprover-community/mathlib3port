/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.AffineScheme
import Mathbin.Topology.Spectral.Hom

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasi_compact_iff_forall_affine`).

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `quasi-compact` if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
class QuasiCompact (f : X ⟶ Y) : Prop where
  is_compact_preimage : ∀ U : Set Y.Carrier, IsOpen U → IsCompact U → IsCompact (f.1.base ⁻¹' U)

theorem quasi_compact_iff_spectral : QuasiCompact f ↔ IsSpectralMap f.1.base :=
  ⟨fun ⟨h⟩ =>
    ⟨by
      continuity, h⟩,
    fun h => ⟨h.2⟩⟩

instance (priority := 900) quasi_compact_of_is_iso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : QuasiCompact f := by
  constructor
  intro U hU hU'
  convert hU'.image (inv f.1.base).continuous_to_fun using 1
  rw [Set.image_eq_preimage_of_inverse]
  delta' Function.LeftInverse
  exacts[is_iso.inv_hom_id_apply f.1.base, is_iso.hom_inv_id_apply f.1.base]

instance quasi_compact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (f ≫ g) := by
  constructor
  intro U hU hU'
  rw [Scheme.comp_val_base, coe_comp, Set.preimage_comp]
  apply quasi_compact.is_compact_preimage
  · exact
      Continuous.is_open_preimage
        (by
          continuity)
        _ hU
    
  apply quasi_compact.is_compact_preimage <;> assumption

theorem is_compact_open_iff_eq_finset_affine_union {X : Scheme} (U : Set X.Carrier) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set X.AffineOpens, s.Finite ∧ U = ⋃ (i : X.AffineOpens) (h : i ∈ s), i := by
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis (coe : X.affine_opens → opens X.carrier)
  · rw [Subtype.range_coe]
    exact is_basis_affine_open X
    
  · intro i
    exact i.2.IsCompact
    

theorem is_compact_open_iff_eq_basic_open_union {X : Scheme} [IsAffine X] (U : Set X.Carrier) :
    IsCompact U ∧ IsOpen U ↔
      ∃ s : Set (X.Presheaf.obj (op ⊤)), s.Finite ∧ U = ⋃ (i : X.Presheaf.obj (op ⊤)) (h : i ∈ s), X.basicOpen i :=
  by
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis
  · exact is_basis_basic_open X
    
  · intro i
    exact ((top_is_affine_open _).basic_open_is_affine _).IsCompact
    

theorem quasi_compact_iff_forall_affine :
    QuasiCompact f ↔ ∀ U : Opens Y.Carrier, IsAffineOpen U → IsCompact (f.1.base ⁻¹' (U : Set Y.Carrier)) := by
  rw [quasi_compact_iff]
  refine' ⟨fun H U hU => H U U.Prop hU.IsCompact, _⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := (is_compact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩
  simp only [← Set.preimage_Union, ← Subtype.val_eq_coe]
  exact hS.compact_bUnion fun i _ => H i i.Prop

@[elabAsElim]
theorem compact_open_induction_on {P : Opens X.Carrier → Prop} (S : Opens X.Carrier) (hS : IsCompact S.1) (h₁ : P ⊥)
    (h₂ : ∀ (S : Opens X.Carrier) (hS : IsCompact S.1) (U : X.AffineOpens), P S → P (S⊔U)) : P S := by
  classical
  obtain ⟨s, hs, hs'⟩ := (is_compact_open_iff_eq_finset_affine_union S.1).mp ⟨hS, S.2⟩
  replace hs' : S = supr fun i : s => (i : opens X.carrier) := by
    ext1
    simpa using hs'
  subst hs'
  apply hs.induction_on
  · convert h₁
    rw [supr_eq_bot]
    rintro ⟨_, h⟩
    exact h.elim
    
  · intro x s h₃ hs h₄
    have : IsCompact (⨆ i : s, (i : opens X.carrier)).1 := by
      refine' ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1
      exact
        ⟨s, hs, by
          simp ⟩
    convert h₂ _ this x h₄
    simp only [← coe_coe]
    rw [supr_subtype, sup_comm]
    conv_rhs => rw [supr_subtype]
    exact supr_insert
    

end AlgebraicGeometry

