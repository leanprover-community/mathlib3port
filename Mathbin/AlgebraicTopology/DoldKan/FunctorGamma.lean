/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.DoldKan.SplitSimplicialObject

/-!

# Construction of the inverse functor of the Dold-Kan equivalence

@TODO @joelriou: construct the functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
which shall be the inverse functor of the Dold-Kan equivalence in the case of abelian categories,
and more generally pseudoabelian categories. Extend this functor `Γ₀` as a functor
`Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)` on the idempotent
completion, show that this functor shall be an equivalence of categories when `C` is any additive
category.

Currently, this file contains the definition of `Γ₀.obj.obj₂ K Δ` for
`K : chain_complex C ℕ` and `Δ : simplex_categoryᵒᵖ`. By definition, `Γ₀.obj.obj₂ K Δ`
is a certain coproduct indexed by the set `splitting.index_set Δ` whose elements
consists of epimorphisms `e : Δ.unop ⟶ Δ'.unop` (with `Δ' : simplex_categoryᵒᵖ`).
Some morphisms between the summands of these coproducts are also studied.
When the simplicial operations are defined using the epi-mono factorisations in
`simplex_category`, the simplicial object `Γ₀.obj K` we get will be a split simplicial object.

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits SimplexCategory SimplicialObject

open Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] (K K' : ChainComplex C ℕ) (f : K ⟶ K')
  {Δ'' Δ' Δ : SimplexCategory} (i' : Δ'' ⟶ Δ') [Mono i'] (i : Δ' ⟶ Δ) [Mono i]

/-- `is_δ₀ i` is a simple condition used to check whether a monomorphism `i` in
`simplex_category` identifies to the coface map `δ 0`. -/
@[nolint unused_arguments]
def Isδ₀ {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] : Prop :=
  Δ.len = Δ'.len + 1 ∧ i.toOrderHom 0 ≠ 0
#align algebraic_topology.dold_kan.is_δ₀ AlgebraicTopology.DoldKan.Isδ₀

namespace Isδ₀

theorem iff {j : ℕ} {i : Fin (j + 2)} : Isδ₀ (SimplexCategory.δ i) ↔ i = 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra
    exact h₂ (Fin.succ_above_ne_zero_zero h)
  · rintro rfl
    exact ⟨rfl, Fin.succ_ne_zero _⟩
#align algebraic_topology.dold_kan.is_δ₀.iff AlgebraicTopology.DoldKan.Isδ₀.iff

theorem eq_δ₀ {n : ℕ} {i : [n] ⟶ [n + 1]} [Mono i] (hi : Isδ₀ i) : i = SimplexCategory.δ 0 := by
  obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono i
  rw [Iff] at hi
  rw [hi]
#align algebraic_topology.dold_kan.is_δ₀.eq_δ₀ AlgebraicTopology.DoldKan.Isδ₀.eq_δ₀

end Isδ₀

namespace Γ₀

namespace Obj

/-- In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : splitting.index_set Δ`,
the summand `summand K Δ A` is `K.X A.1.len`. -/
def summand (Δ : SimplexCategoryᵒᵖ) (A : Splitting.IndexSet Δ) : C :=
  K.x A.1.unop.len
#align algebraic_topology.dold_kan.Γ₀.obj.summand AlgebraicTopology.DoldKan.Γ₀.Obj.summand

/-- The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : splitting.index_set Δ` -/
def obj₂ (K : ChainComplex C ℕ) (Δ : SimplexCategoryᵒᵖ) [HasFiniteCoproducts C] : C :=
  ∐ fun A : Splitting.IndexSet Δ => summand K Δ A
#align algebraic_topology.dold_kan.Γ₀.obj.obj₂ AlgebraicTopology.DoldKan.Γ₀.Obj.obj₂

namespace Termwise

/-- A monomorphism `i : Δ' ⟶ Δ` induces a morphism `K.X Δ.len ⟶ K.X Δ'.len` which
is the identity if `Δ = Δ'`, the differential on the complex `K` if `i = δ 0`, and
zero otherwise. -/
def mapMono (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    K.x Δ.len ⟶ K.x Δ'.len := by 
  by_cases Δ = Δ'
  · exact eq_to_hom (by congr )
  · by_cases is_δ₀ i
    · exact K.d Δ.len Δ'.len
    · exact 0
#align
  algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono

variable (Δ)

theorem map_mono_id : mapMono K (𝟙 Δ) = 𝟙 _ := by
  unfold map_mono
  simp only [eq_self_iff_true, eq_to_hom_refl, dite_eq_ite, if_true]
#align
  algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_id AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.map_mono_id

variable {Δ}

theorem map_mono_δ₀' (hi : Isδ₀ i) : mapMono K i = K.d Δ.len Δ'.len := by
  unfold map_mono
  classical 
    rw [dif_neg, dif_pos hi]
    rintro rfl
    simpa only [self_eq_add_right, Nat.one_ne_zero] using hi.1
#align
  algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_δ₀' AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.map_mono_δ₀'

@[simp]
theorem map_mono_δ₀ {n : ℕ} : mapMono K (δ (0 : Fin (n + 2))) = K.d (n + 1) n :=
  map_mono_δ₀' K _ (by rw [is_δ₀.iff])
#align
  algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_δ₀ AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.map_mono_δ₀

theorem map_mono_eq_zero (h₁ : Δ ≠ Δ') (h₂ : ¬Isδ₀ i) : mapMono K i = 0 := by
  unfold map_mono
  rw [Ne.def] at h₁
  split_ifs
  rfl
#align
  algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_eq_zero AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.map_mono_eq_zero

variable {K K'}

@[simp, reassoc]
theorem map_mono_naturality : mapMono K i ≫ f.f Δ'.len = f.f Δ.len ≫ mapMono K' i := by
  unfold map_mono
  split_ifs
  · subst h
    simp only [id_comp, eq_to_hom_refl, comp_id]
  · rw [HomologicalComplex.Hom.comm]
  · rw [zero_comp, comp_zero]
#align
  algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_naturality AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.map_mono_naturality

variable (K)

@[simp, reassoc]
theorem map_mono_comp : mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i) :=
  by
  -- case where i : Δ' ⟶ Δ is the identity
  by_cases h₁ : Δ = Δ'
  · subst h₁
    simp only [SimplexCategory.eq_id_of_mono i, comp_id, id_comp, map_mono_id K, eq_to_hom_refl]
  -- case where i' : Δ'' ⟶ Δ' is the identity
  by_cases h₂ : Δ' = Δ''
  · subst h₂
    simp only [SimplexCategory.eq_id_of_mono i', comp_id, id_comp, map_mono_id K, eq_to_hom_refl]
  -- then the RHS is always zero
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i h₁)
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i' h₂)
  have eq : Δ.len = Δ''.len + (k + k' + 2) := by linarith
  rw [map_mono_eq_zero K (i' ≫ i) _ _]; rotate_left
  · by_contra
    simpa only [self_eq_add_right, h] using Eq
  · by_contra
    simp only [h.1, add_right_inj] at eq
    linarith
  -- in all cases, the LHS is also zero, either by definition, or because d ≫ d = 0
  by_cases h₃ : is_δ₀ i
  · by_cases h₄ : is_δ₀ i'
    · rw [map_mono_δ₀' K i h₃, map_mono_δ₀' K i' h₄, HomologicalComplex.d_comp_d]
    · simp only [map_mono_eq_zero K i' h₂ h₄, comp_zero]
  · simp only [map_mono_eq_zero K i h₁ h₃, zero_comp]
#align
  algebraic_topology.dold_kan.Γ₀.obj.termwise.map_mono_comp AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.map_mono_comp

end Termwise

end Obj

end Γ₀

end DoldKan

end AlgebraicTopology

