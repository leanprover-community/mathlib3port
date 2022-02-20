/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/
import Mathbin.FieldTheory.Galois
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Algebra.Algebra.Subalgebra

/-!
# Krull topology

We define the Krull topology on `L ≃ₐ[K] L` for an arbitrary field extension `L/K`. In order to do
this, we first define a `group_filter_basis` on `L ≃ₐ[K] L`, whose sets are `E.fixing_subgroup` for
all intermediate fields `E` with `E/K` finite dimensional.

## Main Definitions

- `finite_exts K L`. Given a field extension `L/K`, this is the set of intermediate fields that are
  finite-dimensional over `K`.

- `fixed_by_finite K L`. Given a field extension `L/K`, `fixed_by_finite K L` is the set of
  subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite

- `gal_basis K L`. Given a field extension `L/K`, this is the filter basis on `L ≃ₐ[K] L` whose
  sets are `Gal(L/E)` for intermediate fields `E` with `E/K` finite.

- `gal_group_basis K L`. This is the same as `gal_basis K L`, but with the added structure
  that it is a group filter basis on `L ≃ₐ[K] L`, rather than just a filter basis.

- `krull_topology K L`. Given a field extension `L/K`, this is the topology on `L ≃ₐ[K] L`, induced
  by the group filter basis `gal_group_basis K L`.

## Notations

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `L ≃ₐ[K] L` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `L ≃ₐ[E] L` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `L ≃ₐ[K] L`, while the latter is a group in its own right.

## Implementation Notes

- `krull_topology K L` is defined as an instance for type class inference.
-/


open_locale Classical

/-- Mapping intermediate fields along algebra equivalences preserves the partial order -/
theorem IntermediateField.map_mono {K L M : Type _} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    {E1 E2 : IntermediateField K L} (e : L ≃ₐ[K] M) (h12 : E1 ≤ E2) : E1.map e.toAlgHom ≤ E2.map e.toAlgHom :=
  Set.image_subset e h12

/-- Mapping intermediate fields along the identity does not change them -/
theorem IntermediateField.map_id {K L : Type _} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L) :
    E.map (AlgHom.id K L) = E :=
  SetLike.coe_injective <| Set.image_id _

/-- Mapping a finite dimensional intermediate field along an algebra equivalence gives
a finite-dimensional intermediate field. -/
instance im_finite_dimensional {K L : Type _} [Field K] [Field L] [Algebra K L] {E : IntermediateField K L}
    (σ : L ≃ₐ[K] L) [FiniteDimensional K E] : FiniteDimensional K (E.map σ.toAlgHom) :=
  LinearEquiv.finite_dimensional (IntermediateField.intermediateFieldMap σ E).toLinearEquiv

/-- Given a field extension `L/K`, `finite_exts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def FiniteExts (K : Type _) [Field K] (L : Type _) [Field L] [Algebra K L] : Set (IntermediateField K L) :=
  { E | FiniteDimensional K E }

/-- Given a field extension `L/K`, `fixed_by_finite K L` is the set of
subsets `Gal(L/E)` of `L ≃ₐ[K] L`, where `E/K` is finite -/
def FixedByFinite (K L : Type _) [Field K] [Field L] [Algebra K L] : Set (Subgroup (L ≃ₐ[K] L)) :=
  IntermediateField.fixingSubgroup '' FiniteExts K L

/-- For an field extension `L/K`, the intermediate field `K` is finite-dimensional over `K` -/
theorem IntermediateField.finite_dimensional_bot (K L : Type _) [Field K] [Field L] [Algebra K L] :
    FiniteDimensional K (⊥ : IntermediateField K L) :=
  finite_dimensional_of_dim_eq_one IntermediateField.dim_bot

/-- This lemma says that `Gal(L/K) = L ≃ₐ[K] L` -/
theorem IntermediateField.fixingSubgroup.bot {K L : Type _} [Field K] [Field L] [Algebra K L] :
    IntermediateField.fixingSubgroup (⊥ : IntermediateField K L) = ⊤ := by
  ext f
  refine' ⟨fun _ => Subgroup.mem_top _, fun _ => _⟩
  rintro ⟨x, hx : x ∈ (⊥ : IntermediateField K L)⟩
  rw [IntermediateField.mem_bot] at hx
  rcases hx with ⟨y, rfl⟩
  exact f.commutes y

/-- If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixed_by_finite K L` -/
theorem top_fixed_by_finite {K L : Type _} [Field K] [Field L] [Algebra K L] : ⊤ ∈ FixedByFinite K L :=
  ⟨⊥, IntermediateField.finite_dimensional_bot K L, IntermediateField.fixingSubgroup.bot⟩

/-- If `E1` and `E2` are finite-dimensional intermediate fields, then so is their compositum.
This rephrases a result already in mathlib so that it is compatible with our type classes -/
theorem finite_dimensional_sup {K L : Type _} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)
    (h1 : FiniteDimensional K E1) (h2 : FiniteDimensional K E2) : FiniteDimensional K (↥(E1⊔E2)) :=
  IntermediateField.finite_dimensional_sup E1 E2

/-- An element of `L ≃ₐ[K] L` is in `Gal(L/E)` if and only if it fixes every element of `E`-/
theorem mem_fixing_subgroup_iff {K L : Type _} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    (σ : L ≃ₐ[K] L) : σ ∈ E.fixingSubgroup ↔ ∀ x : L, x ∈ E → σ x = x :=
  ⟨fun hσ x hx => hσ ⟨x, hx⟩, fun h ⟨x, hx⟩ => h x hx⟩

/-- The map `E ↦ Gal(L/E)` is inclusion-reversing -/
theorem IntermediateField.fixingSubgroup.antimono {K L : Type _} [Field K] [Field L] [Algebra K L]
    {E1 E2 : IntermediateField K L} (h12 : E1 ≤ E2) : E2.fixingSubgroup ≤ E1.fixingSubgroup := by
  rintro σ hσ ⟨x, hx⟩
  exact hσ ⟨x, h12 hx⟩

/-- Given a field extension `L/K`, `gal_basis K L` is the filter basis on `L ≃ₐ[K] L` whose sets
are `Gal(L/E)` for intermediate fields `E` with `E/K` finite dimensional -/
def galBasis (K L : Type _) [Field K] [Field L] [Algebra K L] : FilterBasis (L ≃ₐ[K] L) where
  Sets := Subgroup.Carrier '' FixedByFinite K L
  Nonempty := ⟨⊤, ⊤, top_fixed_by_finite, rfl⟩
  inter_sets := by
    rintro X Y ⟨H1, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨H2, ⟨E2, h_E2, rfl⟩, rfl⟩
    use (IntermediateField.fixingSubgroup (E1⊔E2)).Carrier
    refine' ⟨⟨_, ⟨_, finite_dimensional_sup E1 E2 h_E1 h_E2, rfl⟩, rfl⟩, _⟩
    rw [Set.subset_inter_iff]
    exact
      ⟨IntermediateField.fixingSubgroup.antimono le_sup_left, IntermediateField.fixingSubgroup.antimono le_sup_right⟩

/-- A subset of `L ≃ₐ[K] L` is a member of `gal_basis K L` if and only if it is the underlying set
of `Gal(L/E)` for some finite subextension `E/K`-/
theorem mem_gal_basis_iff (K L : Type _) [Field K] [Field L] [Algebra K L] (U : Set (L ≃ₐ[K] L)) :
    U ∈ galBasis K L ↔ U ∈ Subgroup.Carrier '' FixedByFinite K L :=
  Iff.rfl

/-- For a field extension `L/K`, `gal_group_basis K L` is the group filter basis on `L ≃ₐ[K] L`
whose sets are `Gal(L/E)` for finite subextensions `E/K` -/
def galGroupBasis (K L : Type _) [Field K] [Field L] [Algebra K L] : GroupFilterBasis (L ≃ₐ[K] L) where
  toFilterBasis := galBasis K L
  one' := fun U ⟨H, hH, h2⟩ => h2 ▸ H.one_mem
  mul' := fun U hU =>
    ⟨U, hU, by
      rcases hU with ⟨H, hH, rfl⟩
      rintro x ⟨a, b, haH, hbH, rfl⟩
      exact H.mul_mem haH hbH⟩
  inv' := fun U hU =>
    ⟨U, hU, by
      rcases hU with ⟨H, hH, rfl⟩
      exact H.inv_mem'⟩
  conj' := by
    rintro σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩
    let F : IntermediateField K L := E.map σ.symm.to_alg_hom
    refine' ⟨F.fixing_subgroup.carrier, ⟨⟨F.fixing_subgroup, ⟨F, _, rfl⟩, rfl⟩, fun g hg => _⟩⟩
    · apply im_finite_dimensional σ.symm
      exact hE
      
    change σ * g * σ⁻¹ ∈ E.fixing_subgroup
    rw [mem_fixing_subgroup_iff]
    intro x hx
    change σ (g (σ⁻¹ x)) = x
    have h_in_F : σ⁻¹ x ∈ F :=
      ⟨x, hx, by
        dsimp
        rw [← AlgEquiv.inv_fun_eq_symm]
        rfl⟩
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x := by
      rw [Subgroup.mem_carrier, mem_fixing_subgroup_iff F g] at hg
      exact hg (σ⁻¹ x) h_in_F
    rw [h_g_fix]
    change σ (σ⁻¹ x) = x
    exact AlgEquiv.apply_symm_apply σ x

/-- For a field extension `L/K`, `krull_topology K L` is the topological space structure on
`L ≃ₐ[K] L` induced by the group filter basis `gal_group_basis K L` -/
instance krullTopology (K L : Type _) [Field K] [Field L] [Algebra K L] : TopologicalSpace (L ≃ₐ[K] L) :=
  GroupFilterBasis.topology (galGroupBasis K L)

/-- For a field extension `L/K`, the Krull topology on `L ≃ₐ[K] L` makes it a topological group. -/
instance (K L : Type _) [Field K] [Field L] [Algebra K L] : TopologicalGroup (L ≃ₐ[K] L) :=
  GroupFilterBasis.is_topological_group (galGroupBasis K L)

