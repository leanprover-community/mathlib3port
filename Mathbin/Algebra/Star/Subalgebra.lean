/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Star.StarAlgHom
import Mathbin.Algebra.Algebra.Subalgebra.Basic

/-!
# Star subalgebras

A *-subalgebra is a subalgebra of a *-algebra which is closed under *.

The centralizer of a *-closed set is a *-subalgebra.
-/


universe u v

/-- A *-subalgebra is a subalgebra of a *-algebra which is closed under *. -/
structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A] extends Subalgebra R A : Type v where
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

namespace StarSubalgebra

/-- Forgetting that a *-subalgebra is closed under *.
-/
add_decl_doc StarSubalgebra.toSubalgebra

variable {R A B C : Type _} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

instance : SetLike (StarSubalgebra R A) A :=
  ⟨StarSubalgebra.Carrier, fun p q h => by cases p <;> cases q <;> congr⟩

instance : HasTop (StarSubalgebra R A) :=
  ⟨{ (⊤ : Subalgebra R A) with star_mem' := by tidy }⟩

instance : Inhabited (StarSubalgebra R A) :=
  ⟨⊤⟩

instance : StarMemClass (StarSubalgebra R A) A where star_mem s a := s.star_mem'

instance : SubsemiringClass (StarSubalgebra R A) A where
  add_mem := add_mem'
  mul_mem := mul_mem'
  one_mem := one_mem'
  zero_mem := zero_mem'

instance {R A} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A] [StarModule R A] :
    SubringClass (StarSubalgebra R A) A where neg_mem s a ha := show -a ∈ s.toSubalgebra from neg_mem ha

-- this uses the `has_star` instance `s` inherits from `star_mem_class (star_subalgebra R A) A`
instance (s : StarSubalgebra R A) : StarRing s where
  star := star
  star_involutive r := Subtype.ext (star_star r)
  star_mul r₁ r₂ := Subtype.ext (star_mul r₁ r₂)
  star_add r₁ r₂ := Subtype.ext (star_add r₁ r₂)

instance (s : StarSubalgebra R A) : Algebra R s :=
  s.toSubalgebra.algebra'

instance (s : StarSubalgebra R A) : StarModule R s where star_smul r a := Subtype.ext (star_smul r a)

@[simp]
theorem mem_carrier {s : StarSubalgebra R A} {x : A} : x ∈ s.Carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : StarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_to_subalgebra {S : StarSubalgebra R A} {x} : x ∈ S.toSubalgebra ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_to_subalgebra (S : StarSubalgebra R A) : (S.toSubalgebra : Set A) = S :=
  rfl

theorem to_subalgebra_injective : Function.Injective (toSubalgebra : StarSubalgebra R A → Subalgebra R A) :=
  fun S T h => ext fun x => by rw [← mem_to_subalgebra, ← mem_to_subalgebra, h]

theorem to_subalgebra_inj {S U : StarSubalgebra R A} : S.toSubalgebra = U.toSubalgebra ↔ S = U :=
  to_subalgebra_injective.eq_iff

/-- Copy of a star subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : StarSubalgebra R A where
  Carrier := s
  add_mem' _ _ := hs.symm ▸ S.add_mem'
  mul_mem' _ _ := hs.symm ▸ S.mul_mem'
  algebra_map_mem' := hs.symm ▸ S.algebra_map_mem'
  star_mem' _ := hs.symm ▸ S.star_mem'

@[simp]
theorem coe_copy (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : StarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : StarSubalgebra R A)

theorem algebra_map_mem (r : R) : algebraMap R A r ∈ S :=
  S.algebra_map_mem' r

theorem srange_le : (algebraMap R A).srange ≤ S.toSubalgebra.toSubsemiring := fun x ⟨r, hr⟩ => hr ▸ S.algebra_map_mem r

theorem range_subset : Set.Range (algebraMap R A) ⊆ S := fun x ⟨r, hr⟩ => hr ▸ S.algebra_map_mem r

theorem range_le : Set.Range (algebraMap R A) ≤ S :=
  S.range_subset

protected theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  (Algebra.smul_def r x).symm ▸ mul_mem (S.algebra_map_mem r) hx

/-- Embedding of a subalgebra into the algebra. -/
def subtype : S →⋆ₐ[R] A := by refine_struct { toFun := (coe : S → A) } <;> intros <;> rfl

@[simp]
theorem coe_subtype : (S.Subtype : S → A) = coe :=
  rfl

theorem subtype_apply (x : S) : S.Subtype x = (x : A) :=
  rfl

@[simp]
theorem to_subalgebra_subtype : S.toSubalgebra.val = S.Subtype.toAlgHom :=
  rfl

section Map

/-- Transport a star subalgebra via a star algebra homomorphism. -/
def map (f : A →⋆ₐ[R] B) (S : StarSubalgebra R A) : StarSubalgebra R B :=
  { S.toSubalgebra.map f.toAlgHom with
    star_mem' := by
      rintro _ ⟨a, ha, rfl⟩
      exact map_star f a ▸ Set.mem_image_of_mem _ (S.star_mem' ha) }

theorem map_mono {S₁ S₂ : StarSubalgebra R A} {f : A →⋆ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_subset f

theorem map_injective {f : A →⋆ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) := fun S₁ S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
theorem map_id (S : StarSubalgebra R A) : S.map (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (S : StarSubalgebra R A) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem mem_map {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {y : B} : y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map

theorem map_to_subalgebra {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} :
    (S.map f).toSubalgebra = S.toSubalgebra.map f.toAlgHom :=
  SetLike.coe_injective rfl

@[simp]
theorem coe_map (S : StarSubalgebra R A) (f : A →⋆ₐ[R] B) : (S.map f : Set B) = f '' S :=
  rfl

/-- Preimage of a star subalgebra under an star algebra homomorphism. -/
def comap (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) : StarSubalgebra R A :=
  { S.toSubalgebra.comap f.toAlgHom with
    star_mem' := fun a ha => show f (star a) ∈ S from (map_star f a).symm ▸ star_mem ha }

theorem map_le_iff_le_comap {S : StarSubalgebra R A} {f : A →⋆ₐ[R] B} {U : StarSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff

theorem gc_map_comap (f : A →⋆ₐ[R] B) : GaloisConnection (map f) (comap f) := fun S U => map_le_iff_le_comap

theorem comap_mono {S₁ S₂ : StarSubalgebra R B} {f : A →⋆ₐ[R] B} : S₁ ≤ S₂ → S₁.comap f ≤ S₂.comap f :=
  Set.preimage_mono

theorem comap_injective {f : A →⋆ₐ[R] B} (hf : Function.Surjective f) : Function.Injective (comap f) := fun S₁ S₂ h =>
  ext fun b =>
    let ⟨x, hx⟩ := hf b
    let this := SetLike.ext_iff.1 h x
    hx ▸ this

@[simp]
theorem comap_id (S : StarSubalgebra R A) : S.comap (StarAlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.preimage_id

theorem comap_comap (S : StarSubalgebra R C) (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| Set.preimage_preimage

@[simp]
theorem mem_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) : (S.comap f : Set A) = f ⁻¹' (S : Set B) :=
  rfl

end Map

section Centralizer

variable (R) {A}

/-- The centralizer, or commutant, of a *-closed set as star subalgebra. -/
def centralizer (s : Set A) (w : ∀ a : A, a ∈ s → star a ∈ s) : StarSubalgebra R A :=
  { Subalgebra.centralizer R s with star_mem' := fun x xm y hy => by simpa using congr_arg star (xm _ (w _ hy)).symm }

@[simp]
theorem coe_centralizer (s : Set A) (w : ∀ a : A, a ∈ s → star a ∈ s) : (centralizer R s w : Set A) = s.Centralizer :=
  rfl

theorem mem_centralizer_iff {s : Set A} {w} {z : A} : z ∈ centralizer R s w ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl

theorem centralizer_le (s t : Set A) (ws : ∀ a : A, a ∈ s → star a ∈ s) (wt : ∀ a : A, a ∈ t → star a ∈ t) (h : s ⊆ t) :
    centralizer R t wt ≤ centralizer R s ws :=
  Set.centralizer_subset h

end Centralizer

end StarSubalgebra

