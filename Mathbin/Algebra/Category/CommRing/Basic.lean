import Mathbin.Algebra.Category.Group.Basic
import Mathbin.CategoryTheory.ConcreteCategory.ReflectsIsomorphisms
import Mathbin.Data.Equiv.Ring

/-!
# Category instances for semiring, ring, comm_semiring, and comm_ring.

We introduce the bundled categories:
* `SemiRing`
* `Ring`
* `CommSemiRing`
* `CommRing`
along with the relevant forgetful functors between them.
-/


universe u v

open CategoryTheory

/-- The category of semirings. -/
def SemiRing : Type (u + 1) :=
  Bundled Semiringₓ

namespace SemiRing

/-- `ring_hom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. We use the same trick in `category_theory.Mon.assoc_monoid_hom`. -/
abbrev assoc_ring_hom (M N : Type _) [Semiringₓ M] [Semiringₓ N] :=
  RingHom M N

instance bundled_hom : BundledHom AssocRingHom :=
  ⟨fun M N [Semiringₓ M] [Semiringₓ N] => @RingHom.toFun M N _ _, fun M [Semiringₓ M] => @RingHom.id M _,
    fun M N P [Semiringₓ M] [Semiringₓ N] [Semiringₓ P] => @RingHom.comp M N P _ _ _,
    fun M N [Semiringₓ M] [Semiringₓ N] => @RingHom.coe_inj M N _ _⟩

deriving instance LargeCategory, ConcreteCategory for SemiRing

instance : CoeSort SemiRing (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [Semiringₓ R] : SemiRing :=
  Bundled.of R

/-- Typecheck a `ring_hom` as a morphism in `SemiRing`. -/
def of_hom {R S : Type u} [Semiringₓ R] [Semiringₓ S] (f : R →+* S) : of R ⟶ of S :=
  f

instance : Inhabited SemiRing :=
  ⟨of PUnit⟩

instance (R : SemiRing) : Semiringₓ R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [Semiringₓ R] : (SemiRing.of R : Type u) = R :=
  rfl

instance has_forget_to_Mon : HasForget₂ SemiRing Mon :=
  BundledHom.mkHasForget₂ (fun R hR => @MonoidWithZeroₓ.toMonoid R (@Semiringₓ.toMonoidWithZero R hR))
    (fun R₁ R₂ => RingHom.toMonoidHom) fun _ _ _ => rfl

instance has_forget_to_AddCommMon : HasForget₂ SemiRing AddCommMon where
  forget₂ := { obj := fun R => AddCommMon.of R, map := fun R₁ R₂ f => RingHom.toAddMonoidHom f }

end SemiRing

/-- The category of rings. -/
def Ringₓₓ : Type (u + 1) :=
  Bundled Ringₓ

namespace Ringₓₓ

instance : BundledHom.ParentProjection @Ringₓ.toSemiring :=
  ⟨⟩

-- ././Mathport/Syntax/Translate/Basic.lean:859:9: unsupported derive handler λ Ring, has_coe_to_sort Ring (Type*)
deriving instance [anonymous], LargeCategory, ConcreteCategory for Ringₓₓ

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [Ringₓ R] : Ringₓₓ :=
  Bundled.of R

/-- Typecheck a `ring_hom` as a morphism in `Ring`. -/
def of_hom {R S : Type u} [Ringₓ R] [Ringₓ S] (f : R →+* S) : of R ⟶ of S :=
  f

instance : Inhabited Ringₓₓ :=
  ⟨of PUnit⟩

instance (R : Ringₓₓ) : Ringₓ R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [Ringₓ R] : (Ringₓₓ.of R : Type u) = R :=
  rfl

instance has_forget_to_SemiRing : HasForget₂ Ringₓₓ SemiRing :=
  BundledHom.forget₂ _ _

instance has_forget_to_AddCommGroup : HasForget₂ Ringₓₓ AddCommGroupₓₓ where
  forget₂ := { obj := fun R => AddCommGroupₓₓ.of R, map := fun R₁ R₂ f => RingHom.toAddMonoidHom f }

end Ringₓₓ

/-- The category of commutative semirings. -/
def CommSemiRing : Type (u + 1) :=
  Bundled CommSemiringₓ

namespace CommSemiRing

instance : BundledHom.ParentProjection @CommSemiringₓ.toSemiring :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommSemiRing

instance : CoeSort CommSemiRing (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [CommSemiringₓ R] : CommSemiRing :=
  Bundled.of R

/-- Typecheck a `ring_hom` as a morphism in `CommSemiRing`. -/
def of_hom {R S : Type u} [CommSemiringₓ R] [CommSemiringₓ S] (f : R →+* S) : of R ⟶ of S :=
  f

instance : Inhabited CommSemiRing :=
  ⟨of PUnit⟩

instance (R : CommSemiRing) : CommSemiringₓ R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommSemiringₓ R] : (CommSemiRing.of R : Type u) = R :=
  rfl

instance has_forget_to_SemiRing : HasForget₂ CommSemiRing SemiRing :=
  BundledHom.forget₂ _ _

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommMon : HasForget₂ CommSemiRing CommMon :=
  HasForget₂.mk' (fun R : CommSemiRing => CommMon.of R) (fun R => rfl) (fun R₁ R₂ f => f.toMonoidHom)
    (by
      tidy)

end CommSemiRing

/-- The category of commutative rings. -/
def CommRingₓₓ : Type (u + 1) :=
  Bundled CommRingₓ

namespace CommRingₓₓ

instance : BundledHom.ParentProjection @CommRingₓ.toRing :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommRingₓₓ

instance : CoeSort CommRingₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [CommRingₓ R] : CommRingₓₓ :=
  Bundled.of R

/-- Typecheck a `ring_hom` as a morphism in `CommRing`. -/
def of_hom {R S : Type u} [CommRingₓ R] [CommRingₓ S] (f : R →+* S) : of R ⟶ of S :=
  f

instance : Inhabited CommRingₓₓ :=
  ⟨of PUnit⟩

instance (R : CommRingₓₓ) : CommRingₓ R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [CommRingₓ R] : (CommRingₓₓ.of R : Type u) = R :=
  rfl

instance has_forget_to_Ring : HasForget₂ CommRingₓₓ Ringₓₓ :=
  BundledHom.forget₂ _ _

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance has_forget_to_CommSemiRing : HasForget₂ CommRingₓₓ CommSemiRing :=
  HasForget₂.mk' (fun R : CommRingₓₓ => CommSemiRing.of R) (fun R => rfl) (fun R₁ R₂ f => f)
    (by
      tidy)

instance : Full (forget₂ CommRingₓₓ CommSemiRing) where
  Preimage := fun X Y f => f

end CommRingₓₓ

example {R S : CommRingₓₓ} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 := by
  simp [h]

namespace RingEquiv

variable {X Y : Type u}

/-- Build an isomorphism in the category `Ring` from a `ring_equiv` between `ring`s. -/
@[simps]
def to_Ring_iso [Ringₓ X] [Ringₓ Y] (e : X ≃+* Y) : Ringₓₓ.of X ≅ Ringₓₓ.of Y where
  Hom := e.toRingHom
  inv := e.symm.toRingHom

/-- Build an isomorphism in the category `CommRing` from a `ring_equiv` between `comm_ring`s. -/
@[simps]
def to_CommRing_iso [CommRingₓ X] [CommRingₓ Y] (e : X ≃+* Y) : CommRingₓₓ.of X ≅ CommRingₓₓ.of Y where
  Hom := e.toRingHom
  inv := e.symm.toRingHom

end RingEquiv

namespace CategoryTheory.Iso

/-- Build a `ring_equiv` from an isomorphism in the category `Ring`. -/
def Ring_iso_to_ring_equiv {X Y : Ringₓₓ} (i : X ≅ Y) : X ≃+* Y where
  toFun := i.Hom
  invFun := i.inv
  left_inv := by
    tidy
  right_inv := by
    tidy
  map_add' := by
    tidy
  map_mul' := by
    tidy

/-- Build a `ring_equiv` from an isomorphism in the category `CommRing`. -/
def CommRing_iso_to_ring_equiv {X Y : CommRingₓₓ} (i : X ≅ Y) : X ≃+* Y where
  toFun := i.Hom
  invFun := i.inv
  left_inv := by
    tidy
  right_inv := by
    tidy
  map_add' := by
    tidy
  map_mul' := by
    tidy

@[simp]
theorem CommRing_iso_to_ring_equiv_to_ring_hom {X Y : CommRingₓₓ} (i : X ≅ Y) :
    i.commRingIsoToRingEquiv.toRingHom = i.Hom := by
  ext
  rfl

@[simp]
theorem CommRing_iso_to_ring_equiv_symm_to_ring_hom {X Y : CommRingₓₓ} (i : X ≅ Y) :
    i.commRingIsoToRingEquiv.symm.toRingHom = i.inv := by
  ext
  rfl

end CategoryTheory.Iso

/-- Ring equivalences between `ring`s are the same as (isomorphic to) isomorphisms in `Ring`. -/
def ringEquivIsoRingIso {X Y : Type u} [Ringₓ X] [Ringₓ Y] : X ≃+* Y ≅ Ringₓₓ.of X ≅ Ringₓₓ.of Y where
  Hom := fun e => e.toRingIso
  inv := fun i => i.ringIsoToRingEquiv

/-- Ring equivalences between `comm_ring`s are the same as (isomorphic to) isomorphisms
in `CommRing`. -/
def ringEquivIsoCommRingIso {X Y : Type u} [CommRingₓ X] [CommRingₓ Y] :
    X ≃+* Y ≅ CommRingₓₓ.of X ≅ CommRingₓₓ.of Y where
  Hom := fun e => e.toCommRingIso
  inv := fun i => i.commRingIsoToRingEquiv

instance Ringₓₓ.forget_reflects_isos : ReflectsIsomorphisms (forget Ringₓₓ.{u}) where
  reflects := fun X Y f _ => by
    skip
    let i := as_iso ((forget Ringₓₓ).map f)
    let e : X ≃+* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Ring_iso).1⟩

instance CommRingₓₓ.forget_reflects_isos : ReflectsIsomorphisms (forget CommRingₓₓ.{u}) where
  reflects := fun X Y f _ => by
    skip
    let i := as_iso ((forget CommRingₓₓ).map f)
    let e : X ≃+* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommRing_iso).1⟩

attribute [local instance] reflects_isomorphisms_forget₂

example : ReflectsIsomorphisms (forget₂ Ringₓₓ AddCommGroupₓₓ) := by
  infer_instance

