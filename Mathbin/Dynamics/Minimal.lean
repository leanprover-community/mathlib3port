import Mathbin.Topology.Algebra.MulAction 
import Mathbin.GroupTheory.GroupAction.Basic

/-!
# Minimal action of a group

In this file we define an action of a monoid `M` on a topological space `α` to be *minimal* if the
`M`-orbit of every point `x : α` is dense. We also provide an additive version of this definition
and prove some basic facts about minimal actions.

## TODO

* Define a minimal set of an action.

## Tags

group action, minimal
-/


open_locale Pointwise

/-- An action of an additive monoid `M` on a topological space is called *minimal* if the `M`-orbit
of every point `x : α` is dense. -/
class AddAction.IsMinimal (M α : Type _) [AddMonoidₓ M] [TopologicalSpace α] [AddAction M α] : Prop where 
  dense_orbit : ∀ x : α, Dense (AddAction.Orbit M x)

/-- An action of a monoid `M` on a topological space is called *minimal* if the `M`-orbit of every
point `x : α` is dense. -/
@[toAdditive]
class MulAction.IsMinimal (M α : Type _) [Monoidₓ M] [TopologicalSpace α] [MulAction M α] : Prop where 
  dense_orbit : ∀ x : α, Dense (MulAction.Orbit M x)

open MulAction Set

variable (M G : Type _) {α : Type _} [Monoidₓ M] [Groupₓ G] [TopologicalSpace α] [MulAction M α] [MulAction G α]

@[toAdditive]
theorem MulAction.dense_orbit [is_minimal M α] (x : α) : Dense (orbit M x) :=
  MulAction.IsMinimal.dense_orbit x

@[toAdditive]
theorem dense_range_smul [is_minimal M α] (x : α) : DenseRange fun c : M => c • x :=
  MulAction.dense_orbit M x

@[toAdditive]
instance (priority := 100) MulAction.is_minimal_of_pretransitive [is_pretransitive M α] : is_minimal M α :=
  ⟨fun x => (surjective_smul M x).DenseRange⟩

@[toAdditive]
theorem IsOpen.exists_smul_mem [is_minimal M α] (x : α) {U : Set α} (hUo : IsOpen U) (hne : U.nonempty) :
  ∃ c : M, c • x ∈ U :=
  (dense_range_smul M x).exists_mem_open hUo hne

@[toAdditive]
theorem IsOpen.Union_preimage_smul [is_minimal M α] {U : Set α} (hUo : IsOpen U) (hne : U.nonempty) :
  (⋃c : M, (· • ·) c ⁻¹' U) = univ :=
  Union_eq_univ_iff.2$ fun x => hUo.exists_smul_mem M x hne

@[toAdditive]
theorem IsOpen.Union_smul [is_minimal G α] {U : Set α} (hUo : IsOpen U) (hne : U.nonempty) : (⋃g : G, g • U) = univ :=
  Union_eq_univ_iff.2$
    fun x =>
      let ⟨g, hg⟩ := hUo.exists_smul_mem G x hne
      ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[toAdditive]
theorem IsCompact.exists_finite_cover_smul [TopologicalSpace G] [is_minimal G α] [HasContinuousSmul G α] {K U : Set α}
  (hK : IsCompact K) (hUo : IsOpen U) (hne : U.nonempty) : ∃ I : Finset G, K ⊆ ⋃(g : _)(_ : g ∈ I), g • U :=
  (hK.elim_finite_subcover (fun g : G => g • U) fun g => hUo.smul _)$
    calc K ⊆ univ := subset_univ K 
      _ = ⋃g : G, g • U := (hUo.Union_smul G hne).symm
      

@[toAdditive]
theorem dense_of_nonempty_smul_invariant [is_minimal M α] {s : Set α} (hne : s.nonempty) (hsmul : ∀ c : M, c • s ⊆ s) :
  Dense s :=
  let ⟨x, hx⟩ := hne
  (MulAction.dense_orbit M x).mono (range_subset_iff.2$ fun c => hsmul c$ ⟨x, hx, rfl⟩)

@[toAdditive]
theorem eq_empty_or_univ_of_smul_invariant_closed [is_minimal M α] {s : Set α} (hs : IsClosed s)
  (hsmul : ∀ c : M, c • s ⊆ s) : s = ∅ ∨ s = univ :=
  s.eq_empty_or_nonempty.imp_right$ fun hne => hs.closure_eq ▸ (dense_of_nonempty_smul_invariant M hne hsmul).closure_eq

@[toAdditive]
theorem is_minimal_iff_closed_smul_invariant [TopologicalSpace M] [HasContinuousSmul M α] :
  is_minimal M α ↔ ∀ s : Set α, IsClosed s → (∀ c : M, c • s ⊆ s) → s = ∅ ∨ s = univ :=
  by 
    split 
    ·
      intros h s 
      exact eq_empty_or_univ_of_smul_invariant_closed M 
    refine' fun H => ⟨fun x => dense_iff_closure_eq.2$ (H _ _ _).resolve_left _⟩
    exacts[is_closed_closure, fun c => smul_closure_orbit_subset _ _, (orbit_nonempty _).closure.ne_empty]

