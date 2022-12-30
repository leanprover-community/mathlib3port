/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module topology.sets.opens
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.CompleteLattice
import Mathbin.Topology.Bases
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Order.CompactlyGenerated

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

- `opens α` is the type of open subsets of a topological space `α`.
- `open_nhds_of x` is the type of open subsets of a topological space `α` containing `x : α`.
-/


open Filter Function Order Set

variable {ι α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

variable (α)

/-- The type of open subsets of a topological space. -/
def Opens :=
  { s : Set α // IsOpen s }
#align topological_space.opens TopologicalSpace.Opens

variable {α}

namespace Opens

instance : Coe (Opens α) (Set α) where coe := Subtype.val

theorem val_eq_coe (U : Opens α) : U.1 = ↑U :=
  rfl
#align topological_space.opens.val_eq_coe TopologicalSpace.Opens.val_eq_coe

/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
theorem coe_mk {α : Type _} [TopologicalSpace α] {U : Set α} {hU : IsOpen U} :
    ↑(⟨U, hU⟩ : Opens α) = U :=
  rfl
#align topological_space.opens.coe_mk TopologicalSpace.Opens.coe_mk

instance : HasSubset (Opens α) where Subset U V := (U : Set α) ⊆ V

instance : Membership α (Opens α) where Mem a U := a ∈ (U : Set α)

@[simp]
theorem subset_coe {U V : Opens α} : ((U : Set α) ⊆ (V : Set α)) = (U ⊆ V) :=
  rfl
#align topological_space.opens.subset_coe TopologicalSpace.Opens.subset_coe

@[simp]
theorem mem_coe {x : α} {U : Opens α} : (x ∈ (U : Set α)) = (x ∈ U) :=
  rfl
#align topological_space.opens.mem_coe TopologicalSpace.Opens.mem_coe

@[simp]
theorem mem_mk {x : α} {U : Set α} {h : IsOpen U} :
    @Membership.Mem _ _ Opens.hasMem x ⟨U, h⟩ ↔ x ∈ U :=
  Iff.rfl
#align topological_space.opens.mem_mk TopologicalSpace.Opens.mem_mk

@[ext]
theorem ext {U V : Opens α} (h : (U : Set α) = V) : U = V :=
  Subtype.ext h
#align topological_space.opens.ext TopologicalSpace.Opens.ext

@[ext]
theorem ext_iff {U V : Opens α} : (U : Set α) = V ↔ U = V :=
  Subtype.ext_iff.symm
#align topological_space.opens.ext_iff TopologicalSpace.Opens.ext_iff

instance : PartialOrder (Opens α) :=
  Subtype.partialOrder _

/-- The interior of a set, as an element of `opens`. -/
def interior (s : Set α) : Opens α :=
  ⟨interior s, is_open_interior⟩
#align topological_space.opens.interior TopologicalSpace.Opens.interior

theorem gc : GaloisConnection (coe : Opens α → Set α) interior := fun U s =>
  ⟨fun h => interior_maximal h U.property, fun h => le_trans h interior_subset⟩
#align topological_space.opens.gc TopologicalSpace.Opens.gc

open OrderDual (ofDual toDual)

/-- The galois coinsertion between sets and opens. -/
def gi : GaloisCoinsertion Subtype.val (@interior α _)
    where
  choice s hs := ⟨s, interior_eq_iff_is_open.mp <| le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq s hs := le_antisymm hs interior_subset
#align topological_space.opens.gi TopologicalSpace.Opens.gi

instance : CompleteLattice (Opens α) :=
  CompleteLattice.copy (GaloisCoinsertion.liftCompleteLattice gi)
    (-- le
    fun U V => U ⊆ V)
    rfl-- top
    ⟨univ, is_open_univ⟩
    (ext interior_univ.symm)-- bot
    ⟨∅, is_open_empty⟩
    rfl
    (-- sup
    fun U V => ⟨↑U ∪ ↑V, U.2.union V.2⟩)
    rfl
    (-- inf
    fun U V => ⟨↑U ∩ ↑V, U.2.inter V.2⟩)
    (funext fun U => funext fun V => ext (U.2.inter V.2).interior_eq.symm)
    (-- Sup
    fun S => ⟨⋃ s ∈ S, ↑s, is_open_bUnion fun s _ => s.2⟩)
    (funext fun S => ext supₛ_image.symm)-- Inf
    _
    rfl

theorem le_def {U V : Opens α} : U ≤ V ↔ (U : Set α) ≤ (V : Set α) :=
  Iff.rfl
#align topological_space.opens.le_def TopologicalSpace.Opens.le_def

@[simp]
theorem mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} :
    (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : Opens α) = ⟨U ⊓ V, IsOpen.inter hU hV⟩ :=
  rfl
#align topological_space.opens.mk_inf_mk TopologicalSpace.Opens.mk_inf_mk

@[simp, norm_cast]
theorem coe_inf (s t : Opens α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.opens.coe_inf TopologicalSpace.Opens.coe_inf

@[simp, norm_cast]
theorem coe_sup (s t : Opens α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.opens.coe_sup TopologicalSpace.Opens.coe_sup

@[simp, norm_cast]
theorem coe_bot : ((⊥ : Opens α) : Set α) = ∅ :=
  rfl
#align topological_space.opens.coe_bot TopologicalSpace.Opens.coe_bot

@[simp, norm_cast]
theorem coe_top : ((⊤ : Opens α) : Set α) = Set.univ :=
  rfl
#align topological_space.opens.coe_top TopologicalSpace.Opens.coe_top

@[simp, norm_cast]
theorem coe_Sup {S : Set (Opens α)} : (↑(supₛ S) : Set α) = ⋃ i ∈ S, ↑i :=
  rfl
#align topological_space.opens.coe_Sup TopologicalSpace.Opens.coe_Sup

@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Opens α) (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup (coe ∘ f) :=
  map_finset_sup (⟨⟨coe, coe_sup⟩, coe_bot⟩ : SupBotHom (Opens α) (Set α)) _ _
#align topological_space.opens.coe_finset_sup TopologicalSpace.Opens.coe_finset_sup

@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Opens α) (s : Finset ι) : (↑(s.inf f) : Set α) = s.inf (coe ∘ f) :=
  map_finset_inf (⟨⟨coe, coe_inf⟩, coe_top⟩ : InfTopHom (Opens α) (Set α)) _ _
#align topological_space.opens.coe_finset_inf TopologicalSpace.Opens.coe_finset_inf

instance : Inter (Opens α) :=
  ⟨fun U V => U ⊓ V⟩

instance : Union (Opens α) :=
  ⟨fun U V => U ⊔ V⟩

instance : EmptyCollection (Opens α) :=
  ⟨⊥⟩

instance : Inhabited (Opens α) :=
  ⟨∅⟩

@[simp]
theorem inter_eq (U V : Opens α) : U ∩ V = U ⊓ V :=
  rfl
#align topological_space.opens.inter_eq TopologicalSpace.Opens.inter_eq

@[simp]
theorem union_eq (U V : Opens α) : U ∪ V = U ⊔ V :=
  rfl
#align topological_space.opens.union_eq TopologicalSpace.Opens.union_eq

@[simp]
theorem empty_eq : (∅ : Opens α) = ⊥ :=
  rfl
#align topological_space.opens.empty_eq TopologicalSpace.Opens.empty_eq

theorem supr_def {ι} (s : ι → Opens α) : (⨆ i, s i) = ⟨⋃ i, s i, is_open_Union fun i => (s i).2⟩ :=
  by
  ext
  simp only [supᵢ, coe_Sup, bUnion_range]
  rfl
#align topological_space.opens.supr_def TopologicalSpace.Opens.supr_def

@[simp]
theorem supr_mk {ι} (s : ι → Set α) (h : ∀ i, IsOpen (s i)) :
    (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, is_open_Union h⟩ :=
  by
  rw [supr_def]
  simp
#align topological_space.opens.supr_mk TopologicalSpace.Opens.supr_mk

@[simp, norm_cast]
theorem coe_supr {ι} (s : ι → Opens α) : ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i := by
  simp [supr_def]
#align topological_space.opens.coe_supr TopologicalSpace.Opens.coe_supr

@[simp]
theorem mem_supr {ι} {x : α} {s : ι → Opens α} : x ∈ supᵢ s ↔ ∃ i, x ∈ s i :=
  by
  rw [← mem_coe]
  simp
#align topological_space.opens.mem_supr TopologicalSpace.Opens.mem_supr

@[simp]
theorem mem_Sup {Us : Set (Opens α)} {x : α} : x ∈ supₛ Us ↔ ∃ u ∈ Us, x ∈ u := by
  simp_rw [supₛ_eq_supᵢ, mem_supr]
#align topological_space.opens.mem_Sup TopologicalSpace.Opens.mem_Sup

instance : Frame (Opens α) :=
  { Opens.completeLattice with
    sup := supₛ
    inf_Sup_le_supr_inf := fun a s =>
      (ext <| by simp only [coe_inf, coe_supr, coe_Sup, Set.inter_unionᵢ₂]).le }

theorem open_embedding_of_le {U V : Opens α} (i : U ≤ V) : OpenEmbedding (Set.inclusion i) :=
  { inj := Set.inclusion_injective i
    induced := (@induced_compose _ _ _ _ (Set.inclusion i) coe).symm
    open_range := by
      rw [Set.range_inclusion i]
      exact U.property.preimage continuous_subtype_val }
#align topological_space.opens.open_embedding_of_le TopologicalSpace.Opens.open_embedding_of_le

theorem not_nonempty_iff_eq_bot (U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥ := by
  rw [← subtype.coe_injective.eq_iff, opens.coe_bot, ← Set.not_nonempty_iff_eq_empty]
#align
  topological_space.opens.not_nonempty_iff_eq_bot TopologicalSpace.Opens.not_nonempty_iff_eq_bot

theorem ne_bot_iff_nonempty (U : Opens α) : U ≠ ⊥ ↔ Set.Nonempty (U : Set α) := by
  rw [Ne.def, ← opens.not_nonempty_iff_eq_bot, not_not]
#align topological_space.opens.ne_bot_iff_nonempty TopologicalSpace.Opens.ne_bot_iff_nonempty

/-- An open set in the indiscrete topology is either empty or the whole space. -/
theorem eq_bot_or_top {α} [t : TopologicalSpace α] (h : t = ⊤) (U : Opens α) : U = ⊥ ∨ U = ⊤ :=
  by
  simp_rw [← ext_iff]
  subst h
  exact (is_open_top_iff U.1).1 U.2
#align topological_space.opens.eq_bot_or_top TopologicalSpace.Opens.eq_bot_or_top

/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
def IsBasis (B : Set (Opens α)) : Prop :=
  IsTopologicalBasis ((coe : _ → Set α) '' B)
#align topological_space.opens.is_basis TopologicalSpace.Opens.IsBasis

theorem is_basis_iff_nbhd {B : Set (Opens α)} :
    IsBasis B ↔ ∀ {U : Opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ⊆ U :=
  by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine' ⟨V, H₁, _⟩
    cases V
    dsimp at H₂
    subst H₂
    exact hsV
  · refine' is_topological_basis_of_open_of_nhds _ _
    · rintro sU ⟨U, ⟨H₁, rfl⟩⟩
      exact U.property
    · intro x sU hx hsU
      rcases@h (⟨sU, hsU⟩ : opens α) x hx with ⟨V, hV, H⟩
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩
#align topological_space.opens.is_basis_iff_nbhd TopologicalSpace.Opens.is_basis_iff_nbhd

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (Us «expr ⊆ » B) -/
theorem is_basis_iff_cover {B : Set (Opens α)} :
    IsBasis B ↔ ∀ U : Opens α, ∃ (Us : _)(_ : Us ⊆ B), U = supₛ Us :=
  by
  constructor
  · intro hB U
    refine' ⟨{ V : opens α | V ∈ B ∧ V ⊆ U }, fun U hU => hU.left, _⟩
    apply ext
    rw [coe_Sup, hB.open_eq_sUnion' U.prop]
    simp_rw [sUnion_eq_bUnion, Union, supᵢ_and, supᵢ_image]
    rfl
  · intro h
    rw [is_basis_iff_nbhd]
    intro U x hx
    rcases h U with ⟨Us, hUs, rfl⟩
    rcases mem_Sup.1 hx with ⟨U, Us, xU⟩
    exact ⟨U, hUs Us, xU, le_supₛ Us⟩
#align topological_space.opens.is_basis_iff_cover TopologicalSpace.Opens.is_basis_iff_cover

/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
theorem is_compact_open_iff_eq_finite_Union_of_is_basis {ι : Type _} (b : ι → Opens α)
    (hb : Opens.IsBasis (Set.range b)) (hb' : ∀ i, IsCompact (b i : Set α)) (U : Set α) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i :=
  by
  apply is_compact_open_iff_eq_finite_Union_of_is_topological_basis fun i : ι => (b i).1
  · convert hb
    ext
    simp
  · exact hb'
#align
  topological_space.opens.is_compact_open_iff_eq_finite_Union_of_is_basis TopologicalSpace.Opens.is_compact_open_iff_eq_finite_Union_of_is_basis

@[simp]
theorem is_compact_element_iff (s : Opens α) :
    CompleteLattice.IsCompactElement s ↔ IsCompact (s : Set α) :=
  by
  rw [is_compact_iff_finite_subcover, CompleteLattice.is_compact_element_iff]
  refine' ⟨_, fun H ι U hU => _⟩
  · introv H hU hU'
    obtain ⟨t, ht⟩ := H ι (fun i => ⟨U i, hU i⟩) (by simpa)
    refine' ⟨t, Set.Subset.trans ht _⟩
    rw [coe_finset_sup, Finset.sup_eq_supr]
    rfl
  · obtain ⟨t, ht⟩ :=
      H (fun i => U i) (fun i => (U i).Prop) (by simpa using show (s : Set α) ⊆ ↑(supᵢ U) from hU)
    refine' ⟨t, Set.Subset.trans ht _⟩
    simp only [Set.unionᵢ_subset_iff]
    show ∀ i ∈ t, U i ≤ t.sup U
    exact fun i => Finset.le_sup
#align topological_space.opens.is_compact_element_iff TopologicalSpace.Opens.is_compact_element_iff

/-- The preimage of an open set, as an open set. -/
def comap (f : C(α, β)) : FrameHom (Opens β) (Opens α)
    where
  toFun s := ⟨f ⁻¹' s, s.2.Preimage f.Continuous⟩
  map_Sup' s :=
    ext <| by
      simp only [coe_Sup, preimage_Union, coe_mk, mem_image, Union_exists, bUnion_and',
        Union_Union_eq_right]
  map_inf' a b := rfl
  map_top' := rfl
#align topological_space.opens.comap TopologicalSpace.Opens.comap

@[simp]
theorem comap_id : comap (ContinuousMap.id α) = FrameHom.id _ :=
  FrameHom.ext fun a => ext rfl
#align topological_space.opens.comap_id TopologicalSpace.Opens.comap_id

theorem comap_mono (f : C(α, β)) {s t : Opens β} (h : s ≤ t) : comap f s ≤ comap f t :=
  OrderHomClass.mono (comap f) h
#align topological_space.opens.comap_mono TopologicalSpace.Opens.comap_mono

@[simp]
theorem coe_comap (f : C(α, β)) (U : Opens β) : ↑(comap f U) = f ⁻¹' U :=
  rfl
#align topological_space.opens.coe_comap TopologicalSpace.Opens.coe_comap

@[simp]
theorem comap_val (f : C(α, β)) (U : Opens β) : (comap f U).1 = f ⁻¹' U :=
  rfl
#align topological_space.opens.comap_val TopologicalSpace.Opens.comap_val

protected theorem comap_comp (g : C(β, γ)) (f : C(α, β)) :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl
#align topological_space.opens.comap_comp TopologicalSpace.Opens.comap_comp

protected theorem comap_comap (g : C(β, γ)) (f : C(α, β)) (U : Opens γ) :
    comap f (comap g U) = comap (g.comp f) U :=
  rfl
#align topological_space.opens.comap_comap TopologicalSpace.Opens.comap_comap

theorem comap_injective [T0Space β] : Injective (comap : C(α, β) → FrameHom (Opens β) (Opens α)) :=
  fun f g h =>
  ContinuousMap.ext fun a =>
    Inseparable.eq <|
      inseparable_iff_forall_open.2 fun s hs =>
        have : comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩ := FunLike.congr_fun h ⟨_, hs⟩
        show a ∈ f ⁻¹' s ↔ a ∈ g ⁻¹' s from Set.ext_iff.1 (ext_iff.2 this) a
#align topological_space.opens.comap_injective TopologicalSpace.Opens.comap_injective

/-- A homeomorphism induces an equivalence on open sets, by taking comaps. -/
@[simp]
protected def equiv (f : α ≃ₜ β) : Opens α ≃ Opens β
    where
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
#align topological_space.opens.equiv TopologicalSpace.Opens.equiv

/-- A homeomorphism induces an order isomorphism on open sets, by taking comaps. -/
@[simp]
protected def orderIso (f : α ≃ₜ β) : Opens α ≃o Opens β
    where
  toEquiv := Opens.equiv f
  map_rel_iff' U V := f.symm.Surjective.preimage_subset_preimage_iff
#align topological_space.opens.order_iso TopologicalSpace.Opens.orderIso

end Opens

/-- The open neighborhoods of a point. See also `opens` or `nhds`. -/
def OpenNhdsOf (x : α) : Type _ :=
  { s : Set α // IsOpen s ∧ x ∈ s }
#align topological_space.open_nhds_of TopologicalSpace.OpenNhdsOf

instance OpenNhdsOf.inhabited {α : Type _} [TopologicalSpace α] (x : α) :
    Inhabited (OpenNhdsOf x) :=
  ⟨⟨Set.univ, is_open_univ, Set.mem_univ _⟩⟩
#align topological_space.open_nhds_of.inhabited TopologicalSpace.OpenNhdsOf.inhabited

instance [Finite α] : Finite (Opens α) :=
  Subtype.finite

end TopologicalSpace

