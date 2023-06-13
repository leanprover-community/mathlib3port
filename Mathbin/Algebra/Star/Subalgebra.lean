/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jireh Loreaux

! This file was ported from Lean 3 source module algebra.star.subalgebra
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.StarAlgHom
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.Star.Pointwise
import Mathbin.Algebra.Star.Module
import Mathbin.RingTheory.Adjoin.Basic

/-!
# Star subalgebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A *-subalgebra is a subalgebra of a *-algebra which is closed under *.

The centralizer of a *-closed set is a *-subalgebra.
-/


universe u v

#print StarSubalgebra /-
/-- A *-subalgebra is a subalgebra of a *-algebra which is closed under *. -/
structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A]
    [StarRing A] [Algebra R A] [StarModule R A] extends Subalgebra R A : Type v where
  star_mem' {a} : a ∈ carrier → star a ∈ carrier
#align star_subalgebra StarSubalgebra
-/

namespace StarSubalgebra

/-- Forgetting that a *-subalgebra is closed under *.
-/
add_decl_doc StarSubalgebra.toSubalgebra

variable {F R A B C : Type _} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

instance : SetLike (StarSubalgebra R A) A :=
  ⟨StarSubalgebra.carrier, fun p q h => by cases p <;> cases q <;> congr⟩

instance : StarMemClass (StarSubalgebra R A) A where star_mem s a := s.star_mem'

instance : SubsemiringClass (StarSubalgebra R A) A
    where
  add_mem := add_mem'
  mul_mem := mul_mem'
  one_mem := one_mem'
  zero_mem := zero_mem'

instance {R A} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A] [StarModule R A] :
    SubringClass (StarSubalgebra R A) A
    where neg_mem s a ha := show -a ∈ s.toSubalgebra from neg_mem ha

-- this uses the `has_star` instance `s` inherits from `star_mem_class (star_subalgebra R A) A`
instance (s : StarSubalgebra R A) : StarRing s
    where
  unit := star
  star_involutive r := Subtype.ext (star_star r)
  star_mul r₁ r₂ := Subtype.ext (star_mul r₁ r₂)
  star_add r₁ r₂ := Subtype.ext (star_add r₁ r₂)

instance (s : StarSubalgebra R A) : Algebra R s :=
  s.toSubalgebra.algebra'

instance (s : StarSubalgebra R A) : StarModule R s
    where star_smul r a := Subtype.ext (star_smul r a)

#print StarSubalgebra.mem_carrier /-
@[simp]
theorem mem_carrier {s : StarSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align star_subalgebra.mem_carrier StarSubalgebra.mem_carrier
-/

#print StarSubalgebra.ext /-
@[ext]
theorem ext {S T : StarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align star_subalgebra.ext StarSubalgebra.ext
-/

#print StarSubalgebra.mem_toSubalgebra /-
@[simp]
theorem mem_toSubalgebra {S : StarSubalgebra R A} {x} : x ∈ S.toSubalgebra ↔ x ∈ S :=
  Iff.rfl
#align star_subalgebra.mem_to_subalgebra StarSubalgebra.mem_toSubalgebra
-/

#print StarSubalgebra.coe_toSubalgebra /-
@[simp]
theorem coe_toSubalgebra (S : StarSubalgebra R A) : (S.toSubalgebra : Set A) = S :=
  rfl
#align star_subalgebra.coe_to_subalgebra StarSubalgebra.coe_toSubalgebra
-/

#print StarSubalgebra.toSubalgebra_injective /-
theorem toSubalgebra_injective :
    Function.Injective (toSubalgebra : StarSubalgebra R A → Subalgebra R A) := fun S T h =>
  ext fun x => by rw [← mem_to_subalgebra, ← mem_to_subalgebra, h]
#align star_subalgebra.to_subalgebra_injective StarSubalgebra.toSubalgebra_injective
-/

#print StarSubalgebra.toSubalgebra_inj /-
theorem toSubalgebra_inj {S U : StarSubalgebra R A} : S.toSubalgebra = U.toSubalgebra ↔ S = U :=
  toSubalgebra_injective.eq_iff
#align star_subalgebra.to_subalgebra_inj StarSubalgebra.toSubalgebra_inj
-/

#print StarSubalgebra.toSubalgebra_le_iff /-
theorem toSubalgebra_le_iff {S₁ S₂ : StarSubalgebra R A} :
    S₁.toSubalgebra ≤ S₂.toSubalgebra ↔ S₁ ≤ S₂ :=
  Iff.rfl
#align star_subalgebra.to_subalgebra_le_iff StarSubalgebra.toSubalgebra_le_iff
-/

#print StarSubalgebra.copy /-
/-- Copy of a star subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : StarSubalgebra R A
    where
  carrier := s
  add_mem' _ _ := hs.symm ▸ S.add_mem'
  mul_mem' _ _ := hs.symm ▸ S.mul_mem'
  algebraMap_mem' := hs.symm ▸ S.algebraMap_mem'
  star_mem' _ := hs.symm ▸ S.star_mem'
#align star_subalgebra.copy StarSubalgebra.copy
-/

#print StarSubalgebra.coe_copy /-
@[simp]
theorem coe_copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl
#align star_subalgebra.coe_copy StarSubalgebra.coe_copy
-/

#print StarSubalgebra.copy_eq /-
theorem copy_eq (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align star_subalgebra.copy_eq StarSubalgebra.copy_eq
-/

variable (S : StarSubalgebra R A)

#print StarSubalgebra.algebraMap_mem /-
theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  S.algebraMap_mem' r
#align star_subalgebra.algebra_map_mem StarSubalgebra.algebraMap_mem
-/

#print StarSubalgebra.rangeS_le /-
theorem rangeS_le : (algebraMap R A).srange ≤ S.toSubalgebra.toSubsemiring := fun x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r
#align star_subalgebra.srange_le StarSubalgebra.rangeS_le
-/

#print StarSubalgebra.range_subset /-
theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r
#align star_subalgebra.range_subset StarSubalgebra.range_subset
-/

#print StarSubalgebra.range_le /-
theorem range_le : Set.range (algebraMap R A) ≤ S :=
  S.range_subset
#align star_subalgebra.range_le StarSubalgebra.range_le
-/

#print StarSubalgebra.smul_mem /-
protected theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx
#align star_subalgebra.smul_mem StarSubalgebra.smul_mem
-/

#print StarSubalgebra.subtype /-
/-- Embedding of a subalgebra into the algebra. -/
def subtype : S →⋆ₐ[R] A := by refine_struct { toFun := (coe : S → A) } <;> intros <;> rfl
#align star_subalgebra.subtype StarSubalgebra.subtype
-/

#print StarSubalgebra.coe_subtype /-
@[simp]
theorem coe_subtype : (S.Subtype : S → A) = coe :=
  rfl
#align star_subalgebra.coe_subtype StarSubalgebra.coe_subtype
-/

#print StarSubalgebra.subtype_apply /-
theorem subtype_apply (x : S) : S.Subtype x = (x : A) :=
  rfl
#align star_subalgebra.subtype_apply StarSubalgebra.subtype_apply
-/

#print StarSubalgebra.toSubalgebra_subtype /-
@[simp]
theorem toSubalgebra_subtype : S.toSubalgebra.val = S.Subtype.toAlgHom :=
  rfl
#align star_subalgebra.to_subalgebra_subtype StarSubalgebra.toSubalgebra_subtype
-/

#print StarSubalgebra.inclusion /-
/-- The inclusion map between `star_subalgebra`s given by `subtype.map id` as a `star_alg_hom`. -/
@[simps]
def inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) : S₁ →⋆ₐ[R] S₂
    where
  toFun := Subtype.map id h
  map_one' := rfl
  map_mul' x y := rfl
  map_zero' := rfl
  map_add' x y := rfl
  commutes' z := rfl
  map_star' x := rfl
#align star_subalgebra.inclusion StarSubalgebra.inclusion
-/

#print StarSubalgebra.inclusion_injective /-
theorem inclusion_injective {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    Function.Injective <| inclusion h :=
  Set.inclusion_injective h
#align star_subalgebra.inclusion_injective StarSubalgebra.inclusion_injective
-/

#print StarSubalgebra.subtype_comp_inclusion /-
@[simp]
theorem subtype_comp_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    S₂.Subtype.comp (inclusion h) = S₁.Subtype :=
  rfl
#align star_subalgebra.subtype_comp_inclusion StarSubalgebra.subtype_comp_inclusion
-/

section Map

#print StarSubalgebra.map /-
/-- Transport a star subalgebra via a star algebra homomorphism. -/
def map (f : A →⋆ₐ[R] B) (S : StarSubalgebra R A) : StarSubalgebra R B :=
  { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }
#align star_subalgebra.map StarSubalgebra.map
-/

#print StarSubalgebra.map_mono /-
theorem map_mono {S₁ S₂ : StarSubalgebra R A} {f : A →⋆ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_subset f
#align star_subalgebra.map_mono StarSubalgebra.map_mono
-/

#print StarSubalgebra.map_injective /-
theorem map_injective {f : A →⋆ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun S₁ S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih
#align star_subalgebra.map_injective StarSubalgebra.map_injective
-/

#print StarSubalgebra.map_id /-
@[simp]
theorem map_id (S : StarSubalgebra R A) : S.map (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _
#align star_subalgebra.map_id StarSubalgebra.map_id
-/

#print StarSubalgebra.map_map /-
theorem map_map (S : StarSubalgebra R A) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align star_subalgebra.map_map StarSubalgebra.map_map
-/

#print StarSubalgebra.mem_map /-
theorem mem_map {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {y : B} :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map
#align star_subalgebra.mem_map StarSubalgebra.mem_map
-/

#print StarSubalgebra.map_toSubalgebra /-
theorem map_toSubalgebra {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} :
    (S.map f).toSubalgebra = S.toSubalgebra.map f.toAlgHom :=
  SetLike.coe_injective rfl
#align star_subalgebra.map_to_subalgebra StarSubalgebra.map_toSubalgebra
-/

#print StarSubalgebra.coe_map /-
@[simp]
theorem coe_map (S : StarSubalgebra R A) (f : A →⋆ₐ[R] B) : (S.map f : Set B) = f '' S :=
  rfl
#align star_subalgebra.coe_map StarSubalgebra.coe_map
-/

#print StarSubalgebra.comap /-
/-- Preimage of a star subalgebra under an star algebra homomorphism. -/
def comap (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) : StarSubalgebra R A :=
  { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := fun a ha => show f (star a) ∈ S from (map_star f a).symm ▸ star_mem ha }
#align star_subalgebra.comap StarSubalgebra.comap
-/

#print StarSubalgebra.map_le_iff_le_comap /-
theorem map_le_iff_le_comap {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {U : StarSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
#align star_subalgebra.map_le_iff_le_comap StarSubalgebra.map_le_iff_le_comap
-/

#print StarSubalgebra.gc_map_comap /-
theorem gc_map_comap (f : A →⋆ₐ[R] B) : GaloisConnection (map f) (comap f) := fun S U =>
  map_le_iff_le_comap
#align star_subalgebra.gc_map_comap StarSubalgebra.gc_map_comap
-/

#print StarSubalgebra.comap_mono /-
theorem comap_mono {S₁ S₂ : StarSubalgebra R B} {f : A →⋆ₐ[R] B} :
    S₁ ≤ S₂ → S₁.comap f ≤ S₂.comap f :=
  Set.preimage_mono
#align star_subalgebra.comap_mono StarSubalgebra.comap_mono
-/

#print StarSubalgebra.comap_injective /-
theorem comap_injective {f : A →⋆ₐ[R] B} (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun S₁ S₂ h =>
  ext fun b =>
    let ⟨x, hx⟩ := hf b
    let this := SetLike.ext_iff.1 h x
    hx ▸ this
#align star_subalgebra.comap_injective StarSubalgebra.comap_injective
-/

#print StarSubalgebra.comap_id /-
@[simp]
theorem comap_id (S : StarSubalgebra R A) : S.comap (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.preimage_id
#align star_subalgebra.comap_id StarSubalgebra.comap_id
-/

#print StarSubalgebra.comap_comap /-
theorem comap_comap (S : StarSubalgebra R C) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| Set.preimage_preimage
#align star_subalgebra.comap_comap StarSubalgebra.comap_comap
-/

#print StarSubalgebra.mem_comap /-
@[simp]
theorem mem_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align star_subalgebra.mem_comap StarSubalgebra.mem_comap
-/

#print StarSubalgebra.coe_comap /-
@[simp, norm_cast]
theorem coe_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) :
    (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl
#align star_subalgebra.coe_comap StarSubalgebra.coe_comap
-/

end Map

section Centralizer

variable (R) {A}

#print Set.star_mem_centralizer /-
theorem Set.star_mem_centralizer {a : A} {s : Set A} (h : ∀ a : A, a ∈ s → star a ∈ s)
    (ha : a ∈ Set.centralizer s) : star a ∈ Set.centralizer s := fun y hy => by
  simpa using congr_arg star (ha _ (h _ hy)).symm
#align set.star_mem_centralizer Set.star_mem_centralizer
-/

#print StarSubalgebra.centralizer /-
/-- The centralizer, or commutant, of a *-closed set as star subalgebra. -/
def centralizer (s : Set A) (w : ∀ a : A, a ∈ s → star a ∈ s) : StarSubalgebra R A :=
  { Subalgebra.centralizer R s with star_mem' := fun x => Set.star_mem_centralizer w }
#align star_subalgebra.centralizer StarSubalgebra.centralizer
-/

#print StarSubalgebra.coe_centralizer /-
@[simp]
theorem coe_centralizer (s : Set A) (w : ∀ a : A, a ∈ s → star a ∈ s) :
    (centralizer R s w : Set A) = s.centralizer :=
  rfl
#align star_subalgebra.coe_centralizer StarSubalgebra.coe_centralizer
-/

#print StarSubalgebra.mem_centralizer_iff /-
theorem mem_centralizer_iff {s : Set A} {w} {z : A} :
    z ∈ centralizer R s w ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
#align star_subalgebra.mem_centralizer_iff StarSubalgebra.mem_centralizer_iff
-/

#print StarSubalgebra.centralizer_le /-
theorem centralizer_le (s t : Set A) (ws : ∀ a : A, a ∈ s → star a ∈ s)
    (wt : ∀ a : A, a ∈ t → star a ∈ t) (h : s ⊆ t) : centralizer R t wt ≤ centralizer R s ws :=
  Set.centralizer_subset h
#align star_subalgebra.centralizer_le StarSubalgebra.centralizer_le
-/

end Centralizer

end StarSubalgebra

/-! ### The star closure of a subalgebra -/


namespace Subalgebra

open scoped Pointwise

variable {F R A B : Type _} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- The pointwise `star` of a subalgebra is a subalgebra. -/
instance : InvolutiveStar (Subalgebra R A)
    where
  unit S :=
    { carrier := star S.carrier
      mul_mem' := fun x y hx hy =>
        by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_mul x y).symm ▸ mul_mem hy hx
      one_mem' := Set.mem_star.mp ((star_one A).symm ▸ one_mem S : star (1 : A) ∈ S)
      add_mem' := fun x y hx hy =>
        by
        simp only [Set.mem_star, Subalgebra.mem_carrier] at *
        exact (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) ∈ S)
      algebraMap_mem' := fun r => by
        simpa only [Set.mem_star, Subalgebra.mem_carrier, ← algebraMap_star_comm] using
          S.algebra_map_mem (star r) }
  star_involutive S :=
    Subalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) ∈ S)⟩

#print Subalgebra.mem_star_iff /-
@[simp]
theorem mem_star_iff (S : Subalgebra R A) (x : A) : x ∈ star S ↔ star x ∈ S :=
  Iff.rfl
#align subalgebra.mem_star_iff Subalgebra.mem_star_iff
-/

#print Subalgebra.star_mem_star_iff /-
@[simp]
theorem star_mem_star_iff (S : Subalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S := by
  simpa only [star_star] using mem_star_iff S (star x)
#align subalgebra.star_mem_star_iff Subalgebra.star_mem_star_iff
-/

#print Subalgebra.coe_star /-
@[simp]
theorem coe_star (S : Subalgebra R A) : ((star S : Subalgebra R A) : Set A) = star S :=
  rfl
#align subalgebra.coe_star Subalgebra.coe_star
-/

#print Subalgebra.star_mono /-
theorem star_mono : Monotone (star : Subalgebra R A → Subalgebra R A) := fun _ _ h _ hx => h hx
#align subalgebra.star_mono Subalgebra.star_mono
-/

variable (R)

#print Subalgebra.star_adjoin_comm /-
/-- The star operation on `subalgebra` commutes with `algebra.adjoin`. -/
theorem star_adjoin_comm (s : Set A) : star (Algebra.adjoin R s) = Algebra.adjoin R (star s) :=
  have this : ∀ t : Set A, Algebra.adjoin R (star t) ≤ star (Algebra.adjoin R t) := fun t =>
    Algebra.adjoin_le fun x hx => Algebra.subset_adjoin hx
  le_antisymm (by simpa only [star_star] using Subalgebra.star_mono (this (star s))) (this s)
#align subalgebra.star_adjoin_comm Subalgebra.star_adjoin_comm
-/

variable {R}

#print Subalgebra.starClosure /-
/-- The `star_subalgebra` obtained from `S : subalgebra R A` by taking the smallest subalgebra
containing both `S` and `star S`. -/
@[simps]
def starClosure (S : Subalgebra R A) : StarSubalgebra R A :=
  { S ⊔ star S with
    star_mem' := fun a ha =>
      by
      simp only [Subalgebra.mem_carrier, ← (@Algebra.gi R A _ _ _).l_sup_u _ _] at *
      rw [← mem_star_iff _ a, star_adjoin_comm]
      convert ha
      simp [Set.union_comm] }
#align subalgebra.star_closure Subalgebra.starClosure
-/

#print Subalgebra.starClosure_le /-
theorem starClosure_le {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂.toSubalgebra) :
    S₁.starClosure ≤ S₂ :=
  StarSubalgebra.toSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)
#align subalgebra.star_closure_le Subalgebra.starClosure_le
-/

#print Subalgebra.starClosure_le_iff /-
theorem starClosure_le_iff {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩
#align subalgebra.star_closure_le_iff Subalgebra.starClosure_le_iff
-/

end Subalgebra

/-! ### The star subalgebra generated by a set -/


namespace StarSubalgebra

variable {F R A B : Type _} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

variable (R)

#print StarSubalgebra.adjoin /-
/-- The minimal star subalgebra that contains `s`. -/
@[simps]
def adjoin (s : Set A) : StarSubalgebra R A :=
  { Algebra.adjoin R (s ∪ star s) with
    star_mem' := fun x hx => by
      rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, Subalgebra.star_adjoin_comm,
        Set.union_star, star_star, Set.union_comm] }
#align star_subalgebra.adjoin StarSubalgebra.adjoin
-/

#print StarSubalgebra.adjoin_eq_starClosure_adjoin /-
theorem adjoin_eq_starClosure_adjoin (s : Set A) : adjoin R s = (Algebra.adjoin R s).starClosure :=
  toSubalgebra_injective <|
    show Algebra.adjoin R (s ∪ star s) = Algebra.adjoin R s ⊔ star (Algebra.adjoin R s) from
      (Subalgebra.star_adjoin_comm R s).symm ▸ Algebra.adjoin_union s (star s)
#align star_subalgebra.adjoin_eq_star_closure_adjoin StarSubalgebra.adjoin_eq_starClosure_adjoin
-/

#print StarSubalgebra.adjoin_toSubalgebra /-
theorem adjoin_toSubalgebra (s : Set A) :
    (adjoin R s).toSubalgebra = Algebra.adjoin R (s ∪ star s) :=
  rfl
#align star_subalgebra.adjoin_to_subalgebra StarSubalgebra.adjoin_toSubalgebra
-/

#print StarSubalgebra.subset_adjoin /-
theorem subset_adjoin (s : Set A) : s ⊆ adjoin R s :=
  (Set.subset_union_left s (star s)).trans Algebra.subset_adjoin
#align star_subalgebra.subset_adjoin StarSubalgebra.subset_adjoin
-/

#print StarSubalgebra.star_subset_adjoin /-
theorem star_subset_adjoin (s : Set A) : star s ⊆ adjoin R s :=
  (Set.subset_union_right s (star s)).trans Algebra.subset_adjoin
#align star_subalgebra.star_subset_adjoin StarSubalgebra.star_subset_adjoin
-/

#print StarSubalgebra.self_mem_adjoin_singleton /-
theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  Algebra.subset_adjoin <| Set.mem_union_left _ (Set.mem_singleton x)
#align star_subalgebra.self_mem_adjoin_singleton StarSubalgebra.self_mem_adjoin_singleton
-/

#print StarSubalgebra.star_self_mem_adjoin_singleton /-
theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : Set A) :=
  star_mem <| self_mem_adjoin_singleton R x
#align star_subalgebra.star_self_mem_adjoin_singleton StarSubalgebra.star_self_mem_adjoin_singleton
-/

variable {R}

#print StarSubalgebra.gc /-
protected theorem gc : GaloisConnection (adjoin R : Set A → StarSubalgebra R A) coe :=
  by
  intro s S
  rw [← to_subalgebra_le_iff, adjoin_to_subalgebra, Algebra.adjoin_le_iff, coe_to_subalgebra]
  exact
    ⟨fun h => (Set.subset_union_left s _).trans h, fun h =>
      Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩
#align star_subalgebra.gc StarSubalgebra.gc
-/

#print StarSubalgebra.gi /-
/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → StarSubalgebra R A) coe
    where
  choice s hs := (adjoin R s).copy s <| le_antisymm (StarSubalgebra.gc.le_u_l s) hs
  gc := StarSubalgebra.gc
  le_l_u S := (StarSubalgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := StarSubalgebra.copy_eq _ _ _
#align star_subalgebra.gi StarSubalgebra.gi
-/

#print StarSubalgebra.adjoin_le /-
theorem adjoin_le {S : StarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  StarSubalgebra.gc.l_le hs
#align star_subalgebra.adjoin_le StarSubalgebra.adjoin_le
-/

#print StarSubalgebra.adjoin_le_iff /-
theorem adjoin_le_iff {S : StarSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  StarSubalgebra.gc _ _
#align star_subalgebra.adjoin_le_iff StarSubalgebra.adjoin_le_iff
-/

#print Subalgebra.starClosure_eq_adjoin /-
theorem Subalgebra.starClosure_eq_adjoin (S : Subalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (Subalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S ≤ S ⊔ star S))
#align subalgebra.star_closure_eq_adjoin Subalgebra.starClosure_eq_adjoin
-/

#print StarSubalgebra.adjoin_induction /-
/-- If some predicate holds for all `x ∈ (s : set A)` and this predicate is closed under the
`algebra_map`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
theorem adjoin_induction {s : Set A} {p : A → Prop} {a : A} (h : a ∈ adjoin R s)
    (Hs : ∀ x : A, x ∈ s → p x) (Halg : ∀ r : R, p (algebraMap R A r))
    (Hadd : ∀ x y : A, p x → p y → p (x + y)) (Hmul : ∀ x y : A, p x → p y → p (x * y))
    (Hstar : ∀ x : A, p x → p (star x)) : p a :=
  Algebra.adjoin_induction h
    (fun x hx => hx.elim (fun hx => Hs x hx) fun hx => star_star x ▸ Hstar _ (Hs _ hx)) Halg Hadd
    Hmul
#align star_subalgebra.adjoin_induction StarSubalgebra.adjoin_induction
-/

#print StarSubalgebra.adjoin_induction₂ /-
theorem adjoin_induction₂ {s : Set A} {p : A → A → Prop} {a b : A} (ha : a ∈ adjoin R s)
    (hb : b ∈ adjoin R s) (Hs : ∀ x : A, x ∈ s → ∀ y : A, y ∈ s → p x y)
    (Halg : ∀ r₁ r₂ : R, p (algebraMap R A r₁) (algebraMap R A r₂))
    (Halg_left : ∀ (r : R) (x : A), x ∈ s → p (algebraMap R A r) x)
    (Halg_right : ∀ (r : R) (x : A), x ∈ s → p x (algebraMap R A r))
    (Hadd_left : ∀ x₁ x₂ y : A, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂ : A, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y : A, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂ : A, p x y₁ → p x y₂ → p x (y₁ * y₂))
    (Hstar : ∀ x y : A, p x y → p (star x) (star y)) (Hstar_left : ∀ x y : A, p x y → p (star x) y)
    (Hstar_right : ∀ x y : A, p x y → p x (star y)) : p a b :=
  by
  refine'
    Algebra.adjoin_induction₂ ha hb (fun x hx y hy => _) Halg (fun r x hx => _) (fun r x hx => _)
      Hadd_left Hadd_right Hmul_left Hmul_right
  · cases hx <;> cases hy
    exacts [Hs x hx y hy, star_star y ▸ Hstar_right _ _ (Hs _ hx _ hy),
      star_star x ▸ Hstar_left _ _ (Hs _ hx _ hy),
      star_star x ▸ star_star y ▸ Hstar _ _ (Hs _ hx _ hy)]
  · cases hx; exacts [Halg_left _ _ hx, star_star x ▸ Hstar_right _ _ (Halg_left r _ hx)]
  · cases hx; exacts [Halg_right _ _ hx, star_star x ▸ Hstar_left _ _ (Halg_right r _ hx)]
#align star_subalgebra.adjoin_induction₂ StarSubalgebra.adjoin_induction₂
-/

#print StarSubalgebra.adjoin_induction' /-
/-- The difference with `star_subalgebra.adjoin_induction` is that this acts on the subtype. -/
theorem adjoin_induction' {s : Set A} {p : adjoin R s → Prop} (a : adjoin R s)
    (Hs : ∀ (x) (h : x ∈ s), p ⟨x, subset_adjoin R s h⟩) (Halg : ∀ r, p (algebraMap R _ r))
    (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y))
    (Hstar : ∀ x, p x → p (star x)) : p a :=
  Subtype.recOn a fun b hb =>
    by
    refine' Exists.elim _ fun (hb : b ∈ adjoin R s) (hc : p ⟨b, hb⟩) => hc
    apply adjoin_induction hb
    exacts [fun x hx => ⟨subset_adjoin R s hx, Hs x hx⟩, fun r =>
      ⟨StarSubalgebra.algebraMap_mem _ r, Halg r⟩, fun x y hx hy =>
      Exists.elim hx fun hx' hx => Exists.elim hy fun hy' hy => ⟨add_mem hx' hy', Hadd _ _ hx hy⟩,
      fun x y hx hy =>
      Exists.elim hx fun hx' hx => Exists.elim hy fun hy' hy => ⟨mul_mem hx' hy', Hmul _ _ hx hy⟩,
      fun x hx => Exists.elim hx fun hx' hx => ⟨star_mem hx', Hstar _ hx⟩]
#align star_subalgebra.adjoin_induction' StarSubalgebra.adjoin_induction'
-/

variable (R)

#print StarSubalgebra.adjoinCommSemiringOfComm /-
/-- If all elements of `s : set A` commute pairwise and also commute pairwise with elements of
`star s`, then `star_subalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[reducible]
def adjoinCommSemiringOfComm {s : Set A} (hcomm : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * b = b * a)
    (hcomm_star : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * star b = star b * a) :
    CommSemiring (adjoin R s) :=
  { (adjoin R s).toSubalgebra.toSemiring with
    mul_comm := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      ext
      simp only [SetLike.coe_mk, MulMemClass.mk_mul_mk]
      rw [← mem_to_subalgebra, adjoin_to_subalgebra] at hx hy 
      letI : CommSemiring (Algebra.adjoin R (s ∪ star s)) :=
        Algebra.adjoinCommSemiringOfComm R
          (by
            intro a ha b hb
            cases ha <;> cases hb
            exacts [hcomm _ ha _ hb, star_star b ▸ hcomm_star _ ha _ hb,
              star_star a ▸ (hcomm_star _ hb _ ha).symm, by
              simpa only [star_mul, star_star] using congr_arg star (hcomm _ hb _ ha)])
      exact congr_arg coe (mul_comm (⟨x, hx⟩ : Algebra.adjoin R (s ∪ star s)) ⟨y, hy⟩) }
#align star_subalgebra.adjoin_comm_semiring_of_comm StarSubalgebra.adjoinCommSemiringOfComm
-/

#print StarSubalgebra.adjoinCommRingOfComm /-
/-- If all elements of `s : set A` commute pairwise and also commute pairwise with elements of
`star s`, then `star_subalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[reducible]
def adjoinCommRingOfComm (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A] [Algebra R A]
    [StarRing A] [StarModule R A] {s : Set A}
    (hcomm : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * b = b * a)
    (hcomm_star : ∀ a : A, a ∈ s → ∀ b : A, b ∈ s → a * star b = star b * a) :
    CommRing (adjoin R s) :=
  { StarSubalgebra.adjoinCommSemiringOfComm R hcomm hcomm_star,
    (adjoin R s).toSubalgebra.toRing with }
#align star_subalgebra.adjoin_comm_ring_of_comm StarSubalgebra.adjoinCommRingOfComm
-/

#print StarSubalgebra.adjoinCommSemiringOfIsStarNormal /-
/-- The star subalgebra `star_subalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
instance adjoinCommSemiringOfIsStarNormal (x : A) [IsStarNormal x] :
    CommSemiring (adjoin R ({x} : Set A)) :=
  adjoinCommSemiringOfComm R (fun a ha b hb => by rw [Set.mem_singleton_iff] at ha hb ; rw [ha, hb])
    fun a ha b hb => by rw [Set.mem_singleton_iff] at ha hb ;
    simpa only [ha, hb] using (star_comm_self' x).symm
#align star_subalgebra.adjoin_comm_semiring_of_is_star_normal StarSubalgebra.adjoinCommSemiringOfIsStarNormal
-/

#print StarSubalgebra.adjoinCommRingOfIsStarNormal /-
/-- The star subalgebra `star_subalgebra.adjoin R {x}` generated by a single `x : A` is commutative
if `x` is normal. -/
instance adjoinCommRingOfIsStarNormal (R : Type u) {A : Type v} [CommRing R] [StarRing R] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] (x : A) [IsStarNormal x] :
    CommRing (adjoin R ({x} : Set A)) :=
  { (adjoin R ({x} : Set A)).toSubalgebra.toRing with mul_comm := mul_comm }
#align star_subalgebra.adjoin_comm_ring_of_is_star_normal StarSubalgebra.adjoinCommRingOfIsStarNormal
-/

/-! ### Complete lattice structure -/


variable {F R A B}

instance : CompleteLattice (StarSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice StarSubalgebra.gi

instance : Inhabited (StarSubalgebra R A) :=
  ⟨⊤⟩

#print StarSubalgebra.coe_top /-
@[simp]
theorem coe_top : (↑(⊤ : StarSubalgebra R A) : Set A) = Set.univ :=
  rfl
#align star_subalgebra.coe_top StarSubalgebra.coe_top
-/

#print StarSubalgebra.mem_top /-
@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : StarSubalgebra R A) :=
  Set.mem_univ x
#align star_subalgebra.mem_top StarSubalgebra.mem_top
-/

#print StarSubalgebra.top_toSubalgebra /-
@[simp]
theorem top_toSubalgebra : (⊤ : StarSubalgebra R A).toSubalgebra = ⊤ :=
  rfl
#align star_subalgebra.top_to_subalgebra StarSubalgebra.top_toSubalgebra
-/

#print StarSubalgebra.toSubalgebra_eq_top /-
@[simp]
theorem toSubalgebra_eq_top {S : StarSubalgebra R A} : S.toSubalgebra = ⊤ ↔ S = ⊤ :=
  StarSubalgebra.toSubalgebra_injective.eq_iff' top_toSubalgebra
#align star_subalgebra.to_subalgebra_eq_top StarSubalgebra.toSubalgebra_eq_top
-/

#print StarSubalgebra.mem_sup_left /-
theorem mem_sup_left {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  show S ≤ S ⊔ T from le_sup_left
#align star_subalgebra.mem_sup_left StarSubalgebra.mem_sup_left
-/

#print StarSubalgebra.mem_sup_right /-
theorem mem_sup_right {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
  show T ≤ S ⊔ T from le_sup_right
#align star_subalgebra.mem_sup_right StarSubalgebra.mem_sup_right
-/

#print StarSubalgebra.mul_mem_sup /-
theorem mul_mem_sup {S T : StarSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align star_subalgebra.mul_mem_sup StarSubalgebra.mul_mem_sup
-/

#print StarSubalgebra.map_sup /-
theorem map_sup (f : A →⋆ₐ[R] B) (S T : StarSubalgebra R A) : map f (S ⊔ T) = map f S ⊔ map f T :=
  (StarSubalgebra.gc_map_comap f).l_sup
#align star_subalgebra.map_sup StarSubalgebra.map_sup
-/

#print StarSubalgebra.coe_inf /-
@[simp, norm_cast]
theorem coe_inf (S T : StarSubalgebra R A) : (↑(S ⊓ T) : Set A) = S ∩ T :=
  rfl
#align star_subalgebra.coe_inf StarSubalgebra.coe_inf
-/

#print StarSubalgebra.mem_inf /-
@[simp]
theorem mem_inf {S T : StarSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl
#align star_subalgebra.mem_inf StarSubalgebra.mem_inf
-/

#print StarSubalgebra.inf_toSubalgebra /-
@[simp]
theorem inf_toSubalgebra (S T : StarSubalgebra R A) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra :=
  rfl
#align star_subalgebra.inf_to_subalgebra StarSubalgebra.inf_toSubalgebra
-/

#print StarSubalgebra.coe_sInf /-
@[simp, norm_cast]
theorem coe_sInf (S : Set (StarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image
#align star_subalgebra.coe_Inf StarSubalgebra.coe_sInf
-/

#print StarSubalgebra.mem_sInf /-
theorem mem_sInf {S : Set (StarSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_Inf, Set.mem_iInter₂]
#align star_subalgebra.mem_Inf StarSubalgebra.mem_sInf
-/

#print StarSubalgebra.sInf_toSubalgebra /-
@[simp]
theorem sInf_toSubalgebra (S : Set (StarSubalgebra R A)) :
    (sInf S).toSubalgebra = sInf (StarSubalgebra.toSubalgebra '' S) :=
  SetLike.coe_injective <| by simp
#align star_subalgebra.Inf_to_subalgebra StarSubalgebra.sInf_toSubalgebra
-/

#print StarSubalgebra.coe_iInf /-
@[simp, norm_cast]
theorem coe_iInf {ι : Sort _} {S : ι → StarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]
#align star_subalgebra.coe_infi StarSubalgebra.coe_iInf
-/

#print StarSubalgebra.mem_iInf /-
theorem mem_iInf {ι : Sort _} {S : ι → StarSubalgebra R A} {x : A} :
    (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_Inf, Set.forall_range_iff]
#align star_subalgebra.mem_infi StarSubalgebra.mem_iInf
-/

#print StarSubalgebra.iInf_toSubalgebra /-
@[simp]
theorem iInf_toSubalgebra {ι : Sort _} (S : ι → StarSubalgebra R A) :
    (⨅ i, S i).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by simp
#align star_subalgebra.infi_to_subalgebra StarSubalgebra.iInf_toSubalgebra
-/

#print StarSubalgebra.bot_toSubalgebra /-
theorem bot_toSubalgebra : (⊥ : StarSubalgebra R A).toSubalgebra = ⊥ := by
  change Algebra.adjoin R (∅ ∪ star ∅) = Algebra.adjoin R ∅; simp
#align star_subalgebra.bot_to_subalgebra StarSubalgebra.bot_toSubalgebra
-/

#print StarSubalgebra.mem_bot /-
theorem mem_bot {x : A} : x ∈ (⊥ : StarSubalgebra R A) ↔ x ∈ Set.range (algebraMap R A) := by
  rw [← mem_to_subalgebra, bot_to_subalgebra, Algebra.mem_bot]
#align star_subalgebra.mem_bot StarSubalgebra.mem_bot
-/

#print StarSubalgebra.coe_bot /-
@[simp]
theorem coe_bot : ((⊥ : StarSubalgebra R A) : Set A) = Set.range (algebraMap R A) := by
  simp [Set.ext_iff, mem_bot]
#align star_subalgebra.coe_bot StarSubalgebra.coe_bot
-/

#print StarSubalgebra.eq_top_iff /-
theorem eq_top_iff {S : StarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h] <;> exact mem_top, fun h => by
    ext x <;> exact ⟨fun _ => mem_top, fun _ => h x⟩⟩
#align star_subalgebra.eq_top_iff StarSubalgebra.eq_top_iff
-/

end StarSubalgebra

namespace StarAlgHom

open StarSubalgebra

variable {F R A B : Type _} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [hF : StarAlgHomClass F R A B] (f g : F)

#print StarAlgHom.equalizer /-
/-- The equalizer of two star `R`-algebra homomorphisms. -/
def equalizer : StarSubalgebra R A
    where
  carrier := {a | f a = g a}
  mul_mem' a b (ha : f a = g a) (hb : f b = g b) := by
    rw [Set.mem_setOf_eq, map_mul f, map_mul g, ha, hb]
  add_mem' a b (ha : f a = g a) (hb : f b = g b) := by
    rw [Set.mem_setOf_eq, map_add f, map_add g, ha, hb]
  algebraMap_mem' r := by simp only [Set.mem_setOf_eq, AlgHomClass.commutes]
  star_mem' a (ha : f a = g a) := by rw [Set.mem_setOf_eq, map_star f, map_star g, ha]
#align star_alg_hom.equalizer StarAlgHom.equalizer
-/

#print StarAlgHom.mem_equalizer /-
@[simp]
theorem mem_equalizer (x : A) : x ∈ StarAlgHom.equalizer f g ↔ f x = g x :=
  Iff.rfl
#align star_alg_hom.mem_equalizer StarAlgHom.mem_equalizer
-/

#print StarAlgHom.adjoin_le_equalizer /-
theorem adjoin_le_equalizer {s : Set A} (h : s.EqOn f g) : adjoin R s ≤ StarAlgHom.equalizer f g :=
  adjoin_le h
#align star_alg_hom.adjoin_le_equalizer StarAlgHom.adjoin_le_equalizer
-/

#print StarAlgHom.ext_of_adjoin_eq_top /-
theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃f g : F⦄ (hs : s.EqOn f g) : f = g :=
  FunLike.ext f g fun x => StarAlgHom.adjoin_le_equalizer f g hs <| h.symm ▸ trivial
#align star_alg_hom.ext_of_adjoin_eq_top StarAlgHom.ext_of_adjoin_eq_top
-/

#print StarAlgHom.map_adjoin /-
theorem map_adjoin [StarModule R B] (f : A →⋆ₐ[R] B) (s : Set A) :
    map f (adjoin R s) = adjoin R (f '' s) :=
  GaloisConnection.l_comm_of_u_comm Set.image_preimage (gc_map_comap f) StarSubalgebra.gc
    StarSubalgebra.gc fun _ => rfl
#align star_alg_hom.map_adjoin StarAlgHom.map_adjoin
-/

#print StarAlgHom.ext_adjoin /-
theorem ext_adjoin {s : Set A} [StarAlgHomClass F R (adjoin R s) B] {f g : F}
    (h : ∀ x : adjoin R s, (x : A) ∈ s → f x = g x) : f = g :=
  by
  refine'
    FunLike.ext f g fun a =>
      adjoin_induction' a (fun x hx => _) (fun r => _) (fun x y hx hy => _) (fun x y hx hy => _)
        fun x hx => _
  · exact h ⟨x, subset_adjoin R s hx⟩ hx
  · simp only [AlgHomClass.commutes]
  · rw [map_add, map_add, hx, hy]
  · rw [map_mul, map_mul, hx, hy]
  · rw [map_star, map_star, hx]
#align star_alg_hom.ext_adjoin StarAlgHom.ext_adjoin
-/

#print StarAlgHom.ext_adjoin_singleton /-
theorem ext_adjoin_singleton {a : A} [StarAlgHomClass F R (adjoin R ({a} : Set A)) B] {f g : F}
    (h : f ⟨a, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_singleton R a⟩) : f = g :=
  ext_adjoin fun x hx =>
    (show x = ⟨a, self_mem_adjoin_singleton R a⟩ from
          Subtype.ext <| Set.mem_singleton_iff.mp hx).symm ▸
      h
#align star_alg_hom.ext_adjoin_singleton StarAlgHom.ext_adjoin_singleton
-/

end StarAlgHom

