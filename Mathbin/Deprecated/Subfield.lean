/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import Deprecated.Subring

#align_import deprecated.subfield from "leanprover-community/mathlib"@"23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6"

/-!
# Unbundled subfields (deprecated)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled subfields. Instead of using this file, please use
`subfield`, defined in `field_theory.subfield`, for subfields of fields.

## Main definitions

`is_subfield (S : set F) : Prop` : the predicate that `S` is the underlying set of a subfield
of the field `F`. The bundled variant `subfield F` should be used in preference to this.

## Tags

is_subfield
-/


variable {F : Type _} [Field F] (S : Set F)

#print IsSubfield /-
/-- `is_subfield (S : set F)` is the predicate saying that a given subset of a field is
the set underlying a subfield. This structure is deprecated; use the bundled variant
`subfield F` to model subfields of a field. -/
structure IsSubfield extends IsSubring S : Prop where
  inv_mem : ∀ {x : F}, x ∈ S → x⁻¹ ∈ S
#align is_subfield IsSubfield
-/

#print IsSubfield.div_mem /-
theorem IsSubfield.div_mem {S : Set F} (hS : IsSubfield S) {x y : F} (hx : x ∈ S) (hy : y ∈ S) :
    x / y ∈ S := by rw [div_eq_mul_inv];
  exact hS.to_is_subring.to_is_submonoid.mul_mem hx (hS.inv_mem hy)
#align is_subfield.div_mem IsSubfield.div_mem
-/

#print IsSubfield.pow_mem /-
theorem IsSubfield.pow_mem {a : F} {n : ℤ} {s : Set F} (hs : IsSubfield s) (h : a ∈ s) :
    a ^ n ∈ s := by
  cases n
  · rw [zpow_ofNat]; exact hs.to_is_subring.to_is_submonoid.pow_mem h
  · rw [zpow_negSucc]; exact hs.inv_mem (hs.to_is_subring.to_is_submonoid.pow_mem h)
#align is_subfield.pow_mem IsSubfield.pow_mem
-/

#print Univ.isSubfield /-
theorem Univ.isSubfield : IsSubfield (@Set.univ F) :=
  { Univ.isSubmonoid, IsAddSubgroup.univ_addSubgroup with inv_mem := by intros <;> trivial }
#align univ.is_subfield Univ.isSubfield
-/

#print Preimage.isSubfield /-
theorem Preimage.isSubfield {K : Type _} [Field K] (f : F →+* K) {s : Set K} (hs : IsSubfield s) :
    IsSubfield (f ⁻¹' s) :=
  { f.isSubring_preimage hs.to_isSubring with
    inv_mem := fun a (ha : f a ∈ s) =>
      show f a⁻¹ ∈ s by
        rw [map_inv₀]
        exact hs.inv_mem ha }
#align preimage.is_subfield Preimage.isSubfield
-/

#print Image.isSubfield /-
theorem Image.isSubfield {K : Type _} [Field K] (f : F →+* K) {s : Set F} (hs : IsSubfield s) :
    IsSubfield (f '' s) :=
  { f.isSubring_image hs.to_isSubring with
    inv_mem := fun a ⟨x, xmem, ha⟩ => ⟨x⁻¹, hs.inv_mem xmem, ha ▸ map_inv₀ f _⟩ }
#align image.is_subfield Image.isSubfield
-/

#print Range.isSubfield /-
theorem Range.isSubfield {K : Type _} [Field K] (f : F →+* K) : IsSubfield (Set.range f) := by
  rw [← Set.image_univ]; apply Image.isSubfield _ Univ.isSubfield
#align range.is_subfield Range.isSubfield
-/

namespace Field

#print Field.closure /-
/-- `field.closure s` is the minimal subfield that includes `s`. -/
def closure : Set F :=
  {x | ∃ y ∈ Ring.closure S, ∃ z ∈ Ring.closure S, y / z = x}
#align field.closure Field.closure
-/

variable {S}

#print Field.ring_closure_subset /-
theorem ring_closure_subset : Ring.closure S ⊆ closure S := fun x hx =>
  ⟨x, hx, 1, Ring.closure.isSubring.to_isSubmonoid.one_mem, div_one x⟩
#align field.ring_closure_subset Field.ring_closure_subset
-/

#print Field.closure.isSubmonoid /-
theorem closure.isSubmonoid : IsSubmonoid (closure S) :=
  { hMul_mem := by
      rintro _ _ ⟨p, hp, q, hq, hq0, rfl⟩ ⟨r, hr, s, hs, hs0, rfl⟩ <;>
        exact
          ⟨p * r, IsSubmonoid.hMul_mem ring.closure.is_subring.to_is_submonoid hp hr, q * s,
            IsSubmonoid.hMul_mem ring.closure.is_subring.to_is_submonoid hq hs,
            (div_mul_div_comm _ _ _ _).symm⟩
    one_mem := ring_closure_subset <| IsSubmonoid.one_mem Ring.closure.isSubring.to_isSubmonoid }
#align field.closure.is_submonoid Field.closure.isSubmonoid
-/

#print Field.closure.isSubfield /-
theorem closure.isSubfield : IsSubfield (closure S) :=
  have h0 : (0 : F) ∈ closure S :=
    ring_closure_subset <| Ring.closure.isSubring.to_isAddSubgroup.to_isAddSubmonoid.zero_mem
  {
    closure.isSubmonoid with
    add_mem := by
      intro a b ha hb
      rcases id ha with ⟨p, hp, q, hq, rfl⟩
      rcases id hb with ⟨r, hr, s, hs, rfl⟩
      classical
    zero_mem := h0
    neg_mem := by
      rintro _ ⟨p, hp, q, hq, rfl⟩
      exact ⟨-p, ring.closure.is_subring.to_is_add_subgroup.neg_mem hp, q, hq, neg_div q p⟩
    inv_mem := by
      rintro _ ⟨p, hp, q, hq, rfl⟩
      exact ⟨q, hq, p, hp, (inv_div _ _).symm⟩ }
#align field.closure.is_subfield Field.closure.isSubfield
-/

#print Field.mem_closure /-
theorem mem_closure {a : F} (ha : a ∈ S) : a ∈ closure S :=
  ring_closure_subset <| Ring.mem_closure ha
#align field.mem_closure Field.mem_closure
-/

#print Field.subset_closure /-
theorem subset_closure : S ⊆ closure S := fun _ => mem_closure
#align field.subset_closure Field.subset_closure
-/

#print Field.closure_subset /-
theorem closure_subset {T : Set F} (hT : IsSubfield T) (H : S ⊆ T) : closure S ⊆ T := by
  rintro _ ⟨p, hp, q, hq, hq0, rfl⟩ <;>
    exact
      hT.div_mem (Ring.closure_subset hT.to_is_subring H hp)
        (Ring.closure_subset hT.to_is_subring H hq)
#align field.closure_subset Field.closure_subset
-/

#print Field.closure_subset_iff /-
theorem closure_subset_iff {s t : Set F} (ht : IsSubfield t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, closure_subset ht⟩
#align field.closure_subset_iff Field.closure_subset_iff
-/

#print Field.closure_mono /-
theorem closure_mono {s t : Set F} (H : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset closure.isSubfield <| Set.Subset.trans H subset_closure
#align field.closure_mono Field.closure_mono
-/

end Field

#print isSubfield_iUnion_of_directed /-
theorem isSubfield_iUnion_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set F}
    (hs : ∀ i, IsSubfield (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubfield (⋃ i, s i) :=
  { inv_mem := fun x hx =>
      let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      Set.mem_iUnion.2 ⟨i, (hs i).inv_mem hi⟩
    to_isSubring := isSubring_iUnion_of_directed (fun i => (hs i).to_isSubring) Directed }
#align is_subfield_Union_of_directed isSubfield_iUnion_of_directed
-/

#print IsSubfield.inter /-
theorem IsSubfield.inter {S₁ S₂ : Set F} (hS₁ : IsSubfield S₁) (hS₂ : IsSubfield S₂) :
    IsSubfield (S₁ ∩ S₂) :=
  { IsSubring.inter hS₁.to_isSubring hS₂.to_isSubring with
    inv_mem := fun x hx => ⟨hS₁.inv_mem hx.1, hS₂.inv_mem hx.2⟩ }
#align is_subfield.inter IsSubfield.inter
-/

#print IsSubfield.iInter /-
theorem IsSubfield.iInter {ι : Sort _} {S : ι → Set F} (h : ∀ y : ι, IsSubfield (S y)) :
    IsSubfield (Set.iInter S) :=
  { IsSubring.iInter fun y => (h y).to_isSubring with
    inv_mem := fun x hx => Set.mem_iInter.2 fun y => (h y).inv_mem <| Set.mem_iInter.1 hx y }
#align is_subfield.Inter IsSubfield.iInter
-/

