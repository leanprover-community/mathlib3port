/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathbin.Topology.Bases
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

- `opens α` is the type of open subsets of a topological space `α`.
- `open_nhds_of x` is the type of open subsets of a topological space `α` containing `x : α`.
-/


open Filter Set

variable {α : Type _} {β : Type _} {γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

variable (α)

/-- The type of open subsets of a topological space. -/
def Opens :=
  { s : Set α // IsOpen s }

variable {α}

namespace Opens

instance : Coe (Opens α) (Set α) where
  coe := Subtype.val

theorem val_eq_coe (U : Opens α) : U.1 = ↑U :=
  rfl

/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
theorem coe_mk {α : Type _} [TopologicalSpace α] {U : Set α} {hU : IsOpen U} : ↑(⟨U, hU⟩ : Opens α) = U :=
  rfl

instance : HasSubset (Opens α) where
  Subset := fun U V => (U : Set α) ⊆ V

instance : HasMem α (Opens α) where
  Mem := fun a U => a ∈ (U : Set α)

@[simp]
theorem subset_coe {U V : Opens α} : ((U : Set α) ⊆ (V : Set α)) = (U ⊆ V) :=
  rfl

@[simp]
theorem mem_coe {x : α} {U : Opens α} : (x ∈ (U : Set α)) = (x ∈ U) :=
  rfl

@[ext]
theorem ext {U V : Opens α} (h : (U : Set α) = V) : U = V :=
  Subtype.ext_iff.mpr h

@[ext]
theorem ext_iff {U V : Opens α} : (U : Set α) = V ↔ U = V :=
  ⟨Opens.ext, congr_argₓ coe⟩

instance : PartialOrderₓ (Opens α) :=
  Subtype.partialOrder _

/-- The interior of a set, as an element of `opens`. -/
def interior (s : Set α) : Opens α :=
  ⟨Interior s, is_open_interior⟩

theorem gc : GaloisConnection (coe : Opens α → Set α) interior := fun U s =>
  ⟨fun h => interior_maximal h U.property, fun h => le_transₓ h interior_subset⟩

open OrderDual (ofDual toDual)

/-- The galois insertion between sets and opens, but ordered by reverse inclusion. -/
def gi : GaloisInsertion (to_dual ∘ @interior α _ ∘ of_dual) (to_dual ∘ Subtype.val ∘ of_dual) where
  choice := fun s hs => ⟨s, interior_eq_iff_open.mp <| le_antisymmₓ interior_subset hs⟩
  gc := gc.dual
  le_l_u := fun _ => interior_subset
  choice_eq := fun s hs => le_antisymmₓ interior_subset hs

@[simp]
theorem gi_choice_val {s : OrderDual (Set α)} {hs} : (gi.choice s hs).val = s :=
  rfl

instance : CompleteLattice (Opens α) :=
  CompleteLattice.copy (@OrderDual.completeLattice _ (GaloisInsertion.liftCompleteLattice (@gi α _)))
    (-- le
    fun U V => U ⊆ V)
    rfl-- top
    ⟨Set.Univ, is_open_univ⟩
    (Subtype.ext_iff_val.mpr interior_univ.symm)-- bot
    ⟨∅, is_open_empty⟩
    rfl
    (-- sup
    fun U V => ⟨↑U ∪ ↑V, IsOpen.union U.2 V.2⟩)
    rfl
    (-- inf
    fun U V => ⟨↑U ∩ ↑V, IsOpen.inter U.2 V.2⟩)
    (by
      funext
      apply subtype.ext_iff_val.mpr
      exact (IsOpen.inter U.2 V.2).interior_eq.symm)-- Sup
    _
    rfl-- Inf
    _
    rfl

theorem le_def {U V : Opens α} : U ≤ V ↔ (U : Set α) ≤ (V : Set α) := by
  rfl

@[simp]
theorem mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} :
    (⟨U, hU⟩⊓⟨V, hV⟩ : Opens α) = ⟨U⊓V, IsOpen.inter hU hV⟩ :=
  rfl

@[simp, norm_cast]
theorem coe_inf {U V : Opens α} : ((U⊓V : Opens α) : Set α) = (U : Set α)⊓(V : Set α) :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : Opens α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_top : ((⊤ : Opens α) : Set α) = Set.Univ :=
  rfl

instance : HasInter (Opens α) :=
  ⟨fun U V => U⊓V⟩

instance : HasUnion (Opens α) :=
  ⟨fun U V => U⊔V⟩

instance : HasEmptyc (Opens α) :=
  ⟨⊥⟩

instance : Inhabited (Opens α) :=
  ⟨∅⟩

@[simp]
theorem inter_eq (U V : Opens α) : U ∩ V = U⊓V :=
  rfl

@[simp]
theorem union_eq (U V : Opens α) : U ∪ V = U⊔V :=
  rfl

@[simp]
theorem empty_eq : (∅ : Opens α) = ⊥ :=
  rfl

@[simp]
theorem Sup_s {Us : Set (Opens α)} : ↑(sup Us) = ⋃₀((coe : _ → Set α) '' Us) := by
  rw [(@gc α _).l_Sup, Set.sUnion_image]
  rfl

theorem supr_def {ι} (s : ι → Opens α) : (⨆ i, s i) = ⟨⋃ i, s i, is_open_Union fun i => (s i).2⟩ := by
  ext
  simp only [supr, opens.Sup_s, sUnion_image, bUnion_range]
  rfl

@[simp]
theorem supr_mk {ι} (s : ι → Set α) (h : ∀ i, IsOpen (s i)) :
    (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, is_open_Union h⟩ := by
  rw [supr_def]
  simp

@[simp]
theorem supr_s {ι} (s : ι → Opens α) : ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i := by
  simp [supr_def]

@[simp]
theorem mem_supr {ι} {x : α} {s : ι → Opens α} : x ∈ supr s ↔ ∃ i, x ∈ s i := by
  rw [← mem_coe]
  simp

@[simp]
theorem mem_Sup {Us : Set (Opens α)} {x : α} : x ∈ sup Us ↔ ∃ u ∈ Us, x ∈ u := by
  simp_rw [Sup_eq_supr, mem_supr]

theorem open_embedding_of_le {U V : Opens α} (i : U ≤ V) : OpenEmbedding (Set.inclusion i) :=
  { inj := Set.inclusion_injective i, induced := (@induced_compose _ _ _ _ (Set.inclusion i) coe).symm,
    open_range := by
      rw [Set.range_inclusion i]
      exact U.property.preimage continuous_subtype_val }

theorem not_nonempty_iff_eq_bot (U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥ := by
  rw [← subtype.coe_injective.eq_iff, opens.coe_bot, ← Set.not_nonempty_iff_eq_empty]

theorem ne_bot_iff_nonempty (U : Opens α) : U ≠ ⊥ ↔ Set.Nonempty (U : Set α) := by
  rw [Ne.def, ← opens.not_nonempty_iff_eq_bot, not_not]

/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
def IsBasis (B : Set (Opens α)) : Prop :=
  IsTopologicalBasis ((coe : _ → Set α) '' B)

theorem is_basis_iff_nbhd {B : Set (Opens α)} : IsBasis B ↔ ∀ {U : Opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ⊆ U := by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine' ⟨V, H₁, _⟩
    cases V
    dsimp  at H₂
    subst H₂
    exact hsV
    
  · refine' is_topological_basis_of_open_of_nhds _ _
    · rintro sU ⟨U, ⟨H₁, H₂⟩⟩
      subst H₂
      exact U.property
      
    · intro x sU hx hsU
      rcases@h (⟨sU, hsU⟩ : opens α) x hx with ⟨V, hV, H⟩
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩
      
    

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (Us «expr ⊆ » B)
theorem is_basis_iff_cover {B : Set (Opens α)} : IsBasis B ↔ ∀ U : Opens α, ∃ (Us : _)(_ : Us ⊆ B), U = sup Us := by
  constructor
  · intro hB U
    refine' ⟨{ V : opens α | V ∈ B ∧ V ⊆ U }, fun U hU => hU.left, _⟩
    apply ext
    rw [Sup_s, hB.open_eq_sUnion' U.prop]
    simp_rw [sUnion_image, sUnion_eq_bUnion, Union, supr_and, supr_image]
    rfl
    
  · intro h
    rw [is_basis_iff_nbhd]
    intro U x hx
    rcases h U with ⟨Us, hUs, rfl⟩
    rcases mem_Sup.1 hx with ⟨U, Us, xU⟩
    exact ⟨U, hUs Us, xU, le_Sup Us⟩
    

/-- The preimage of an open set, as an open set. -/
def comap (f : C(α, β)) : Opens β →o Opens α where
  toFun := fun V => ⟨f ⁻¹' V, V.2.Preimage f.Continuous⟩
  monotone' := fun V₁ V₂ hle => monotone_preimage hle

@[simp]
theorem comap_id : comap (ContinuousMap.id α) = OrderHom.id := by
  ext
  rfl

theorem comap_mono (f : C(α, β)) {V W : Opens β} (hVW : V ⊆ W) : comap f V ⊆ comap f W :=
  (comap f).Monotone hVW

@[simp]
theorem coe_comap (f : C(α, β)) (U : Opens β) : ↑(comap f U) = f ⁻¹' U :=
  rfl

@[simp]
theorem comap_val (f : C(α, β)) (U : Opens β) : (comap f U).1 = f ⁻¹' U :=
  rfl

protected theorem comap_comp (g : C(β, γ)) (f : C(α, β)) : comap (g.comp f) = (comap f).comp (comap g) :=
  rfl

protected theorem comap_comap (g : C(β, γ)) (f : C(α, β)) (U : Opens γ) : comap f (comap g U) = comap (g.comp f) U :=
  rfl

/-- A homeomorphism induces an equivalence on open sets, by taking comaps. -/
@[simp]
protected def equiv (f : α ≃ₜ β) : Opens α ≃ Opens β where
  toFun := Opens.comap f.symm.toContinuousMap
  invFun := Opens.comap f.toContinuousMap
  left_inv := by
    intro U
    ext1
    exact f.to_equiv.preimage_symm_preimage _
  right_inv := by
    intro U
    ext1
    exact f.to_equiv.symm_preimage_preimage _

/-- A homeomorphism induces an order isomorphism on open sets, by taking comaps. -/
@[simp]
protected def orderIso (f : α ≃ₜ β) : Opens α ≃o Opens β where
  toEquiv := Opens.equiv f
  map_rel_iff' := fun U V => f.symm.Surjective.preimage_subset_preimage_iff

end Opens

/-- The open neighborhoods of a point. See also `opens` or `nhds`. -/
def OpenNhdsOf (x : α) : Type _ :=
  { s : Set α // IsOpen s ∧ x ∈ s }

instance OpenNhdsOf.inhabited {α : Type _} [TopologicalSpace α] (x : α) : Inhabited (OpenNhdsOf x) :=
  ⟨⟨Set.Univ, is_open_univ, Set.mem_univ _⟩⟩

end TopologicalSpace

