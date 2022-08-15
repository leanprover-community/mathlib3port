/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/
import Mathbin.LinearAlgebra.ProjectiveSpace.Basic

/-!
# Subspaces of Projective Space

In this file we define subspaces of a projective space, and show that the subspaces of a projective
space form a complete lattice under inclusion.

## Implementation Details

A subspace of a projective space ℙ K V is defined to be a structure consisting of a subset of
ℙ K V such that if two nonzero vectors in V determine points in ℙ K V which are in the subset, and
the sum of the two vectors is nonzero, then the point determined by the sum of the two vectors is
also in the subset.

## Results

- There is a Galois insertion between the subsets of points of a projective space
  and the subspaces of the projective space, which is given by taking the span of the set of points.
- The subspaces of a projective space form a complete lattice under inclusion.

# Future Work
- Show that there is a one-to-one order-preserving correspondence between subspaces of a
  projective space and the submodules of the underlying vector space.
-/


variable (K V : Type _) [Field K] [AddCommGroupₓ V] [Module K V]

namespace Projectivization

/-- A subspace of a projective space is a structure consisting of a set of points such that:
If two nonzero vectors determine points which are in the set, and the sum of the two vectors is
nonzero, then the point determined by the sum is also in the set. -/
@[ext]
structure Subspace where
  Carrier : Set (ℙ K V)
  mem_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) hvw ∈ carrier

namespace Subspace

variable {K V}

instance : SetLike (Subspace K V) (ℙ K V) where
  coe := Carrier
  coe_injective' := fun A B => by
    cases A
    cases B
    simp

@[simp]
theorem mem_carrier_iff (A : Subspace K V) (x : ℙ K V) : x ∈ A.Carrier ↔ x ∈ A :=
  Iff.refl _

theorem mem_add (T : Subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    Projectivization.mk K v hv ∈ T → Projectivization.mk K w hw ∈ T → Projectivization.mk K (v + w) hvw ∈ T :=
  T.mem_add' v w hv hw hvw

/-- The span of a set of points in a projective space is defined inductively to be the set of points
which contains the original set, and contains all points determined by the (nonzero) sum of two
nonzero vectors, each of which determine points in the span. -/
inductive SpanCarrier (S : Set (ℙ K V)) : Set (ℙ K V)
  | of (x : ℙ K V) (hx : x ∈ S) : span_carrier x
  | mem_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    span_carrier (Projectivization.mk K v hv) →
      span_carrier (Projectivization.mk K w hw) → span_carrier (Projectivization.mk K (v + w) hvw)

/-- The span of a set of points in projective space is a subspace. -/
def span (S : Set (ℙ K V)) : Subspace K V where
  Carrier := SpanCarrier S
  mem_add' := fun v w hv hw hvw => SpanCarrier.mem_add v w hv hw hvw

/-- The span of a set of points contains the set of points. -/
theorem subset_span (S : Set (ℙ K V)) : S ⊆ span S := fun x hx => SpanCarrier.of _ hx

/-- The span of a subspace is the subspace. -/
@[simp]
theorem span_coe (W : Subspace K V) : span ↑W = W := by
  ext
  refine' ⟨fun hx => _, fun hx => _⟩
  · induction' hx with a ha u w hu hw huw _ _ hum hwm
    · exact ha
      
    · exact mem_add W u w hu hw huw hum hwm
      
    
  · exact subset_span W hx
    

/-- The span of a set of points is a Galois insertion between sets of points of a projective space
and subspaces of the projective space. -/
def gi : GaloisInsertion (span : Set (ℙ K V) → Subspace K V) coe where
  choice := fun S hS => span S
  gc := fun A B =>
    ⟨fun h => le_transₓ (subset_span _) h, by
      intro h x hx
      induction hx
      · apply h
        assumption
        
      · apply B.mem_add
        assumption'
        ⟩
  le_l_u := fun S => subset_span _
  choice_eq := fun _ _ => rfl

/-- The infimum of two subspaces exists. -/
instance hasInf : HasInf (Subspace K V) :=
  ⟨fun A B => ⟨A⊓B, fun v w hv hw hvw h1 h2 => ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

/-- Infimums of arbitrary collections of subspaces exist. -/
instance hasInfₓ : HasInfₓ (Subspace K V) :=
  ⟨fun A =>
    ⟨inf (coe '' A), fun v w hv hw hvw h1 h2 t => by
      rintro ⟨s, hs, rfl⟩
      exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩)⟩⟩

/-- The subspaces of a projective space form a complete lattice. -/
instance : CompleteLattice (Subspace K V) :=
  { (inferInstance : HasInf _),
    completeLatticeOfInf (Subspace K V)
      (by
        refine' fun s => ⟨fun a ha x hx => hx _ ⟨a, ha, rfl⟩, fun a ha x hx E => _⟩
        rintro ⟨E, hE, rfl⟩
        exact ha hE hx) with
    inf_le_left := fun A B x hx => hx.1, inf_le_right := fun A B x hx => hx.2,
    le_inf := fun A B C h1 h2 x hx => ⟨h1 hx, h2 hx⟩ }

instance subspaceInhabited : Inhabited (Subspace K V) where default := ⊤

end Subspace

end Projectivization

