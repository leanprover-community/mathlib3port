import Mathbin.Topology.Bases 
import Mathbin.Topology.Homeomorph

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

- `opens α` is the type of open subsets of a topological space `α`.
- `open_nhds_of x` is the type of open subsets of a topological space `α` containing `x : α`.
-
-/


open Filter Set

variable{α : Type _}{β : Type _}{γ : Type _}[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ]

namespace TopologicalSpace

variable(α)

/-- The type of open subsets of a topological space. -/
def opens :=
  { s : Set α // IsOpen s }

variable{α}

namespace Opens

instance  : Coe (opens α) (Set α) :=
  { coe := Subtype.val }

theorem val_eq_coe (U : opens α) : U.1 = «expr↑ » U :=
  rfl

/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
theorem coe_mk {α : Type _} [TopologicalSpace α] {U : Set α} {hU : IsOpen U} : «expr↑ » (⟨U, hU⟩ : opens α) = U :=
  rfl

instance  : HasSubset (opens α) :=
  { Subset := fun U V => (U : Set α) ⊆ V }

instance  : HasMem α (opens α) :=
  { Mem := fun a U => a ∈ (U : Set α) }

@[simp]
theorem subset_coe {U V : opens α} : ((U : Set α) ⊆ (V : Set α)) = (U ⊆ V) :=
  rfl

@[simp]
theorem mem_coe {x : α} {U : opens α} : (x ∈ (U : Set α)) = (x ∈ U) :=
  rfl

@[ext]
theorem ext {U V : opens α} (h : (U : Set α) = V) : U = V :=
  Subtype.ext_iff.mpr h

@[ext]
theorem ext_iff {U V : opens α} : (U : Set α) = V ↔ U = V :=
  ⟨opens.ext, congr_argₓ coeₓ⟩

instance  : PartialOrderₓ (opens α) :=
  Subtype.partialOrder _

/-- The interior of a set, as an element of `opens`. -/
def Interior (s : Set α) : opens α :=
  ⟨Interior s, is_open_interior⟩

theorem gc : GaloisConnection (coeₓ : opens α → Set α) Interior :=
  fun U s => ⟨fun h => interior_maximal h U.property, fun h => le_transₓ h interior_subset⟩

open order_dual(ofDual toDual)

/-- The galois insertion between sets and opens, but ordered by reverse inclusion. -/
def gi : GaloisInsertion (to_dual ∘ @Interior α _ ∘ of_dual) (to_dual ∘ Subtype.val ∘ of_dual) :=
  { choice := fun s hs => ⟨s, interior_eq_iff_open.mp$ le_antisymmₓ interior_subset hs⟩, gc := gc.dual,
    le_l_u := fun _ => interior_subset, choice_eq := fun s hs => le_antisymmₓ interior_subset hs }

@[simp]
theorem gi_choice_val {s : OrderDual (Set α)} {hs} : (gi.choice s hs).val = s :=
  rfl

instance  : CompleteLattice (opens α) :=
  CompleteLattice.copy (@OrderDual.completeLattice _ (GaloisInsertion.liftCompleteLattice (@gi α _))) (fun U V => U ⊆ V)
    rfl ⟨Set.Univ, is_open_univ⟩ (Subtype.ext_iff_val.mpr interior_univ.symm) ⟨∅, is_open_empty⟩ rfl
    (fun U V => ⟨«expr↑ » U ∪ «expr↑ » V, IsOpen.union U.2 V.2⟩) rfl
    (fun U V => ⟨«expr↑ » U ∩ «expr↑ » V, IsOpen.inter U.2 V.2⟩)
    (by 
      funext 
      apply subtype.ext_iff_val.mpr 
      exact (IsOpen.inter U.2 V.2).interior_eq.symm)
    _ rfl _ rfl

theorem le_def {U V : opens α} : U ≤ V ↔ (U : Set α) ≤ (V : Set α) :=
  by 
    rfl

@[simp]
theorem mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} :
  (⟨U, hU⟩⊓⟨V, hV⟩ : opens α) = ⟨U⊓V, IsOpen.inter hU hV⟩ :=
  rfl

@[simp, normCast]
theorem coe_inf {U V : opens α} : ((U⊓V : opens α) : Set α) = (U : Set α)⊓(V : Set α) :=
  rfl

instance  : HasInter (opens α) :=
  ⟨fun U V => U⊓V⟩

instance  : HasUnion (opens α) :=
  ⟨fun U V => U⊔V⟩

instance  : HasEmptyc (opens α) :=
  ⟨⊥⟩

instance  : Inhabited (opens α) :=
  ⟨∅⟩

@[simp]
theorem inter_eq (U V : opens α) : U ∩ V = U⊓V :=
  rfl

@[simp]
theorem union_eq (U V : opens α) : U ∪ V = U⊔V :=
  rfl

@[simp]
theorem empty_eq : (∅ : opens α) = ⊥ :=
  rfl

@[simp]
theorem Sup_s {Us : Set (opens α)} : «expr↑ » (Sup Us) = ⋃₀((coeₓ : _ → Set α) '' Us) :=
  by 
    rw [(@gc α _).l_Sup, Set.sUnion_image]
    rfl

theorem supr_def {ι} (s : ι → opens α) : (⨆i, s i) = ⟨⋃i, s i, is_open_Union$ fun i => (s i).2⟩ :=
  by 
    ext 
    simp only [supr, opens.Sup_s, sUnion_image, bUnion_range]
    rfl

@[simp]
theorem supr_mk {ι} (s : ι → Set α) (h : ∀ i, IsOpen (s i)) : (⨆i, ⟨s i, h i⟩ : opens α) = ⟨⋃i, s i, is_open_Union h⟩ :=
  by 
    rw [supr_def]
    simp 

@[simp]
theorem supr_s {ι} (s : ι → opens α) : ((⨆i, s i : opens α) : Set α) = ⋃i, s i :=
  by 
    simp [supr_def]

@[simp]
theorem mem_supr {ι} {x : α} {s : ι → opens α} : x ∈ supr s ↔ ∃ i, x ∈ s i :=
  by 
    rw [←mem_coe]
    simp 

@[simp]
theorem mem_Sup {Us : Set (opens α)} {x : α} : x ∈ Sup Us ↔ ∃ (u : _)(_ : u ∈ Us), x ∈ u :=
  by 
    simpRw [Sup_eq_supr, mem_supr]

theorem open_embedding_of_le {U V : opens α} (i : U ≤ V) : OpenEmbedding (Set.inclusion i) :=
  { inj := Set.inclusion_injective i, induced := (@induced_compose _ _ _ _ (Set.inclusion i) coeₓ).symm,
    open_range :=
      by 
        rw [Set.range_inclusion i]
        exact U.property.preimage continuous_subtype_val }

/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
def is_basis (B : Set (opens α)) : Prop :=
  is_topological_basis ((coeₓ : _ → Set α) '' B)

theorem is_basis_iff_nbhd {B : Set (opens α)} :
  is_basis B ↔ ∀ {U : opens α} {x}, x ∈ U → ∃ (U' : _)(_ : U' ∈ B), x ∈ U' ∧ U' ⊆ U :=
  by 
    split  <;> intro h
    ·
      rintro ⟨sU, hU⟩ x hx 
      rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
      refine' ⟨V, H₁, _⟩
      cases V 
      dsimp  at H₂ 
      subst H₂ 
      exact hsV
    ·
      refine' is_topological_basis_of_open_of_nhds _ _
      ·
        rintro sU ⟨U, ⟨H₁, H₂⟩⟩
        subst H₂ 
        exact U.property
      ·
        intro x sU hx hsU 
        rcases@h (⟨sU, hsU⟩ : opens α) x hx with ⟨V, hV, H⟩
        exact ⟨V, ⟨V, hV, rfl⟩, H⟩

theorem is_basis_iff_cover {B : Set (opens α)} : is_basis B ↔ ∀ U : opens α, ∃ (Us : _)(_ : Us ⊆ B), U = Sup Us :=
  by 
    split 
    ·
      intro hB U 
      refine' ⟨{ V:opens α | V ∈ B ∧ V ⊆ U }, fun U hU => hU.left, _⟩
      apply ext 
      rw [Sup_s, hB.open_eq_sUnion' U.prop]
      simpRw [sUnion_image, sUnion_eq_bUnion, Union, supr_and, supr_image]
      rfl
    ·
      intro h 
      rw [is_basis_iff_nbhd]
      intro U x hx 
      rcases h U with ⟨Us, hUs, rfl⟩
      rcases mem_Sup.1 hx with ⟨U, Us, xU⟩
      exact ⟨U, hUs Us, xU, le_Sup Us⟩

/-- The preimage of an open set, as an open set. -/
def comap {f : α → β} (hf : Continuous f) (V : opens β) : opens α :=
  ⟨f ⁻¹' V.1, V.2.Preimage hf⟩

@[simp]
theorem comap_id (U : opens α) : U.comap continuous_id = U :=
  by 
    ext 
    rfl

theorem comap_mono {f : α → β} (hf : Continuous f) {V W : opens β} (hVW : V ⊆ W) : V.comap hf ⊆ W.comap hf :=
  fun _ h => hVW h

@[simp]
theorem coe_comap {f : α → β} (hf : Continuous f) (U : opens β) : «expr↑ » (U.comap hf) = f ⁻¹' U :=
  rfl

@[simp]
theorem comap_val {f : α → β} (hf : Continuous f) (U : opens β) : (U.comap hf).1 = f ⁻¹' U :=
  rfl

protected theorem comap_comp {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) (U : opens γ) :
  U.comap (hg.comp hf) = (U.comap hg).comap hf :=
  by 
    ext1 
    simp only [coe_comap, preimage_preimage]

/-- A homeomorphism induces an equivalence on open sets, by taking comaps. -/
@[simp]
protected def Equiv (f : α ≃ₜ β) : opens α ≃ opens β :=
  { toFun := opens.comap f.symm.continuous, invFun := opens.comap f.continuous,
    left_inv :=
      by 
        intro U 
        ext1 
        simp only [coe_comap, ←preimage_comp, f.symm_comp_self, preimage_id],
    right_inv :=
      by 
        intro U 
        ext1 
        simp only [coe_comap, ←preimage_comp, f.self_comp_symm, preimage_id] }

end Opens

/-- The open neighborhoods of a point. See also `opens` or `nhds`. -/
def open_nhds_of (x : α) : Type _ :=
  { s : Set α // IsOpen s ∧ x ∈ s }

instance open_nhds_of.inhabited {α : Type _} [TopologicalSpace α] (x : α) : Inhabited (open_nhds_of x) :=
  ⟨⟨Set.Univ, is_open_univ, Set.mem_univ _⟩⟩

end TopologicalSpace

