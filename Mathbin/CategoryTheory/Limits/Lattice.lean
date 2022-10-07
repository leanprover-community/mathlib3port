/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import Mathbin.Order.CompleteLattice
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Limits in lattice categories are given by infimums and supremums.
-/


universe w u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Limits.CompleteLattice

section Semilattice

variable {α : Type u}

variable {J : Type w} [SmallCategory J] [FinCategory J]

/-- The limit cone over any functor from a finite diagram into a `semilattice_inf` with `order_top`.
-/
def finiteLimitCone [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : LimitCone F where
  Cone := { x := Finsetₓ.univ.inf F.obj, π := { app := fun j => homOfLe (Finsetₓ.inf_le (Fintypeₓ.complete _)) } }
  IsLimit := { lift := fun s => homOfLe (Finsetₓ.le_inf fun j _ => (s.π.app j).down.down) }

/-- The colimit cocone over any functor from a finite diagram into a `semilattice_sup` with `order_bot`.
-/
def finiteColimitCocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : ColimitCocone F where
  Cocone := { x := Finsetₓ.univ.sup F.obj, ι := { app := fun i => homOfLe (Finsetₓ.le_sup (Fintypeₓ.complete _)) } }
  IsColimit := { desc := fun s => homOfLe (Finsetₓ.sup_le fun j _ => (s.ι.app j).down.down) }

-- see Note [lower instance priority]
instance (priority := 100) has_finite_limits_of_semilattice_inf_order_top [SemilatticeInf α] [OrderTop α] :
    HasFiniteLimits α :=
  ⟨fun J 𝒥₁ 𝒥₂ => { HasLimit := fun F => has_limit.mk (finite_limit_cone F) }⟩

-- see Note [lower instance priority]
instance (priority := 100) has_finite_colimits_of_semilattice_sup_order_bot [SemilatticeSup α] [OrderBot α] :
    HasFiniteColimits α :=
  ⟨fun J 𝒥₁ 𝒥₂ => { HasColimit := fun F => has_colimit.mk (finite_colimit_cocone F) }⟩

/-- The limit of a functor from a finite diagram into a `semilattice_inf` with `order_top` is the
infimum of the objects in the image.
-/
theorem finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) :
    limit F = Finsetₓ.univ.inf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).IsLimit).to_eq

/-- The colimit of a functor from a finite diagram into a `semilattice_sup` with `order_bot`
is the supremum of the objects in the image.
-/
theorem finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
    colimit F = Finsetₓ.univ.sup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).IsColimit).to_eq

/-- A finite product in the category of a `semilattice_inf` with `order_top` is the same as the infimum.
-/
theorem finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} [Fintypeₓ ι] (f : ι → α) :
    (∏ f) = (Fintypeₓ.elems ι).inf f := by
  trans
  exact (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (finite_limit_cone (discrete.functor f)).IsLimit).to_eq
  change finset.univ.inf (f ∘ discrete_equiv.to_embedding) = (Fintypeₓ.elems ι).inf f
  simp only [← Finsetₓ.inf_map, Finsetₓ.univ_map_equiv_to_embedding]
  rfl

/-- A finite coproduct in the category of a `semilattice_sup` with `order_bot` is the same as the
supremum.
-/
theorem finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u} [Fintypeₓ ι] (f : ι → α) :
    (∐ f) = (Fintypeₓ.elems ι).sup f := by
  trans
  exact
    (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
        (finite_colimit_cocone (discrete.functor f)).IsColimit).to_eq
  change finset.univ.sup (f ∘ discrete_equiv.to_embedding) = (Fintypeₓ.elems ι).sup f
  simp only [← Finsetₓ.sup_map, Finsetₓ.univ_map_equiv_to_embedding]
  rfl

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeInf α] [OrderTop α] : HasBinaryProducts α := by
  have : ∀ x y : α, has_limit (pair x y) := by
    letI := has_finite_limits_of_has_finite_limits_of_size.{u} α
    infer_instance
  apply has_binary_products_of_has_limit_pair

/-- The binary product in the category of a `semilattice_inf` with `order_top` is the same as the
infimum.
-/
@[simp]
theorem prod_eq_inf [SemilatticeInf α] [OrderTop α] (x y : α) : Limits.prod x y = x ⊓ y :=
  calc
    Limits.prod x y = limit (pair x y) := rfl
    _ = Finsetₓ.univ.inf (pair x y).obj := by rw [finite_limit_eq_finset_univ_inf (pair.{u} x y)]
    _ = x ⊓ (y ⊓ ⊤) := rfl
    -- Note: finset.inf is realized as a fold, hence the definitional equality
        _ =
        x ⊓ y :=
      by rw [inf_top_eq]
    

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeSup α] [OrderBot α] : HasBinaryCoproducts α := by
  have : ∀ x y : α, has_colimit (pair x y) := by
    letI := has_finite_colimits_of_has_finite_colimits_of_size.{u} α
    infer_instance
  apply has_binary_coproducts_of_has_colimit_pair

/-- The binary coproduct in the category of a `semilattice_sup` with `order_bot` is the same as the
supremum.
-/
@[simp]
theorem coprod_eq_sup [SemilatticeSup α] [OrderBot α] (x y : α) : Limits.coprod x y = x ⊔ y :=
  calc
    Limits.coprod x y = colimit (pair x y) := rfl
    _ = Finsetₓ.univ.sup (pair x y).obj := by rw [finite_colimit_eq_finset_univ_sup (pair x y)]
    _ = x ⊔ (y ⊔ ⊥) := rfl
    -- Note: finset.sup is realized as a fold, hence the definitional equality
        _ =
        x ⊔ y :=
      by rw [sup_bot_eq]
    

/-- The pullback in the category of a `semilattice_inf` with `order_top` is the same as the infimum
over the objects.
-/
@[simp]
theorem pullback_eq_inf [SemilatticeInf α] [OrderTop α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z) : pullback f g = x ⊓ y :=
  calc
    pullback f g = limit (cospan f g) := rfl
    _ = Finsetₓ.univ.inf (cospan f g).obj := by rw [finite_limit_eq_finset_univ_inf]
    _ = z ⊓ (x ⊓ (y ⊓ ⊤)) := rfl
    _ = z ⊓ (x ⊓ y) := by rw [inf_top_eq]
    _ = x ⊓ y := inf_eq_right.mpr (inf_le_of_left_le f.le)
    

/-- The pushout in the category of a `semilattice_sup` with `order_bot` is the same as the supremum
over the objects.
-/
@[simp]
theorem pushout_eq_sup [SemilatticeSup α] [OrderBot α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y) : pushout f g = x ⊔ y :=
  calc
    pushout f g = colimit (span f g) := rfl
    _ = Finsetₓ.univ.sup (span f g).obj := by rw [finite_colimit_eq_finset_univ_sup]
    _ = z ⊔ (x ⊔ (y ⊔ ⊥)) := rfl
    _ = z ⊔ (x ⊔ y) := by rw [sup_bot_eq]
    _ = x ⊔ y := sup_eq_right.mpr (le_sup_of_le_left f.le)
    

end Semilattice

variable {α : Type u} [CompleteLattice α]

variable {J : Type u} [SmallCategory J]

/-- The limit cone over any functor into a complete lattice.
-/
def limitCone (F : J ⥤ α) : LimitCone F where
  Cone := { x := infi F.obj, π := { app := fun j => homOfLe (CompleteLattice.Inf_le _ _ (Set.mem_range_self _)) } }
  IsLimit :=
    { lift := fun s =>
        homOfLe
          (CompleteLattice.le_Inf _ _
            (by
              rintro _ ⟨j, rfl⟩
              exact (s.π.app j).le)) }

/-- The colimit cocone over any functor into a complete lattice.
-/
def colimitCocone (F : J ⥤ α) : ColimitCocone F where
  Cocone := { x := supr F.obj, ι := { app := fun j => homOfLe (CompleteLattice.le_Sup _ _ (Set.mem_range_self _)) } }
  IsColimit :=
    { desc := fun s =>
        homOfLe
          (CompleteLattice.Sup_le _ _
            (by
              rintro _ ⟨j, rfl⟩
              exact (s.ι.app j).le)) }

-- It would be nice to only use the `Inf` half of the complete lattice, but
-- this seems not to have been described separately.
-- see Note [lower instance priority]
instance (priority := 100) has_limits_of_complete_lattice :
    HasLimits α where HasLimitsOfShape := fun J 𝒥 => { HasLimit := fun F => has_limit.mk (limit_cone F) }

-- see Note [lower instance priority]
instance (priority := 100) has_colimits_of_complete_lattice :
    HasColimits α where HasColimitsOfShape := fun J 𝒥 => { HasColimit := fun F => has_colimit.mk (colimit_cocone F) }

/-- The limit of a functor into a complete lattice is the infimum of the objects in the image.
-/
theorem limit_eq_infi (F : J ⥤ α) : limit F = infi F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (limitCone F).IsLimit).to_eq

/-- The colimit of a functor into a complete lattice is the supremum of the objects in the image.
-/
theorem colimit_eq_supr (F : J ⥤ α) : colimit F = supr F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCocone F).IsColimit).to_eq

end CategoryTheory.Limits.CompleteLattice

