import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.CategoryTheory.Limits.Shapes.Zero

/-!
# The category of seminormed groups

We define `SemiNormedGroup`, the category of seminormed groups and normed group homs between them,
as well as `SemiNormedGroup₁`, the subcategory of norm non-increasing morphisms.
-/


noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroupₓ : Type (u + 1) :=
  bundled SemiNormedGroup

namespace SemiNormedGroupₓ

instance bundled_hom : bundled_hom @NormedGroupHom :=
  ⟨@NormedGroupHom.toFun, @NormedGroupHom.id, @NormedGroupHom.comp, @NormedGroupHom.coe_inj⟩

deriving instance large_category, concrete_category for SemiNormedGroupₓ

instance : CoeSort SemiNormedGroupₓ (Type u) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [SemiNormedGroup M] : SemiNormedGroupₓ :=
  bundled.of M

instance (M : SemiNormedGroupₓ) : SemiNormedGroup M :=
  M.str

@[simp]
theorem coe_of (V : Type u) [SemiNormedGroup V] : (SemiNormedGroupₓ.of V : Type u) = V :=
  rfl

@[simp]
theorem coe_id (V : SemiNormedGroupₓ) : ⇑𝟙 V = id :=
  rfl

@[simp]
theorem coe_comp {M N K : SemiNormedGroupₓ} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl

instance : HasZero SemiNormedGroupₓ :=
  ⟨of PUnit⟩

instance : Inhabited SemiNormedGroupₓ :=
  ⟨0⟩

instance : limits.has_zero_morphisms.{u, u + 1} SemiNormedGroupₓ :=
  {  }

@[simp]
theorem zero_apply {V W : SemiNormedGroupₓ} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

instance has_zero_object : limits.has_zero_object SemiNormedGroupₓ.{u} where
  zero := 0
  uniqueTo := fun X =>
    { default := 0,
      uniq := fun a => by
        ext ⟨⟩
        exact a.map_zero }
  uniqueFrom := fun X =>
    { default := 0,
      uniq := fun f => by
        ext }

theorem iso_isometry_of_norm_noninc {V W : SemiNormedGroupₓ} (i : V ≅ W) (h1 : i.hom.norm_noninc)
    (h2 : i.inv.norm_noninc) : Isometry i.hom := by
  apply NormedGroupHom.isometry_of_norm
  intro v
  apply le_antisymmₓ (h1 v)
  calc ∥v∥ = ∥i.inv (i.hom v)∥ := by
      rw [coe_hom_inv_id]_ ≤ ∥i.hom v∥ := h2 _

end SemiNormedGroupₓ

/-- `SemiNormedGroup₁` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroup₁ : Type (u + 1) :=
  bundled SemiNormedGroup

namespace SemiNormedGroup₁

instance : CoeSort SemiNormedGroup₁ (Type u) :=
  bundled.has_coe_to_sort

instance : large_category.{u} SemiNormedGroup₁ where
  hom := fun X Y => { f : NormedGroupHom X Y // f.norm_noninc }
  id := fun X => ⟨NormedGroupHom.id X, NormedGroupHom.NormNoninc.id⟩
  comp := fun X Y Z f g => ⟨(g : NormedGroupHom Y Z).comp (f : NormedGroupHom X Y), g.2.comp f.2⟩

@[ext]
theorem hom_ext {M N : SemiNormedGroup₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) : f = g :=
  Subtype.eq (NormedGroupHom.ext (congr_funₓ w))

instance : concrete_category.{u} SemiNormedGroup₁ where
  forget := { obj := fun X => X, map := fun X Y f => f }
  forget_faithful := {  }

/-- Construct a bundled `SemiNormedGroup₁` from the underlying type and typeclass. -/
def of (M : Type u) [SemiNormedGroup M] : SemiNormedGroup₁ :=
  bundled.of M

instance (M : SemiNormedGroup₁) : SemiNormedGroup M :=
  M.str

/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup₁`. -/
def mk_hom {M N : SemiNormedGroupₓ} (f : M ⟶ N) (i : f.norm_noninc) : SemiNormedGroup₁.of M ⟶ SemiNormedGroup₁.of N :=
  ⟨f, i⟩

@[simp]
theorem mk_hom_apply {M N : SemiNormedGroupₓ} (f : M ⟶ N) (i : f.norm_noninc) x : mk_hom f i x = f x :=
  rfl

/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup₁`. -/
@[simps]
def mk_iso {M N : SemiNormedGroupₓ} (f : M ≅ N) (i : f.hom.norm_noninc) (i' : f.inv.norm_noninc) :
    SemiNormedGroup₁.of M ≅ SemiNormedGroup₁.of N where
  hom := mk_hom f.hom i
  inv := mk_hom f.inv i'
  hom_inv_id' := by
    apply Subtype.eq
    exact f.hom_inv_id
  inv_hom_id' := by
    apply Subtype.eq
    exact f.inv_hom_id

instance : has_forget₂ SemiNormedGroup₁ SemiNormedGroupₓ where
  forget₂ := { obj := fun X => X, map := fun X Y f => f.1 }

@[simp]
theorem coe_of (V : Type u) [SemiNormedGroup V] : (SemiNormedGroup₁.of V : Type u) = V :=
  rfl

@[simp]
theorem coe_id (V : SemiNormedGroup₁) : ⇑𝟙 V = id :=
  rfl

@[simp]
theorem coe_comp {M N K : SemiNormedGroup₁} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl

@[simp]
theorem coe_comp' {M N K : SemiNormedGroup₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : NormedGroupHom M K) = (↑g : NormedGroupHom N K).comp (↑f) :=
  rfl

instance : HasZero SemiNormedGroup₁ :=
  ⟨of PUnit⟩

instance : Inhabited SemiNormedGroup₁ :=
  ⟨0⟩

instance : limits.has_zero_morphisms.{u, u + 1} SemiNormedGroup₁ where
  HasZero := fun X Y => { zero := ⟨0, NormedGroupHom.NormNoninc.zero⟩ }
  comp_zero' := fun X Y f Z => by
    ext
    rfl
  zero_comp' := fun X Y Z f => by
    ext
    simp [coe_fn_coe_base']

@[simp]
theorem zero_apply {V W : SemiNormedGroup₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

instance has_zero_object : limits.has_zero_object SemiNormedGroup₁.{u} where
  zero := 0
  uniqueTo := fun X =>
    { default := 0,
      uniq := fun a => by
        ext ⟨⟩
        exact a.1.map_zero }
  uniqueFrom := fun X =>
    { default := 0,
      uniq := fun f => by
        ext }

theorem iso_isometry {V W : SemiNormedGroup₁} (i : V ≅ W) : Isometry i.hom := by
  apply NormedGroupHom.isometry_of_norm
  intro v
  apply le_antisymmₓ (i.hom.2 v)
  calc ∥v∥ = ∥i.inv (i.hom v)∥ := by
      rw [coe_hom_inv_id]_ ≤ ∥i.hom v∥ := i.inv.2 _

end SemiNormedGroup₁

