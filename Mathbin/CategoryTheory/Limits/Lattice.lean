import Mathbin.Order.CompleteLattice
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Limits in lattice categories are given by infimums and supremums.
-/


universe u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Limits.CompleteLattice

section Semilattice

variable {α : Type u}

variable {J : Type u} [small_category J] [fin_category J]

/-- 
The limit cone over any functor from a finite diagram into a `semilattice_inf` with `order_top`.
-/
def finite_limit_cone [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : limit_cone F :=
  { Cone := { x := Finset.univ.inf F.obj, π := { app := fun j => hom_of_le (Finset.inf_le (Fintype.complete _)) } },
    IsLimit := { lift := fun s => hom_of_le (Finset.le_inf fun j _ => (s.π.app j).down.down) } }

/-- 
The colimit cocone over any functor from a finite diagram into a `semilattice_sup` with `order_bot`.
-/
def finite_colimit_cocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : colimit_cocone F :=
  { Cocone := { x := Finset.univ.sup F.obj, ι := { app := fun i => hom_of_le (Finset.le_sup (Fintype.complete _)) } },
    IsColimit := { desc := fun s => hom_of_le (Finset.sup_le fun j _ => (s.ι.app j).down.down) } }

instance (priority := 100) has_finite_limits_of_semilattice_inf_order_top [SemilatticeInf α] [OrderTop α] :
    has_finite_limits α :=
  ⟨fun J 𝒥₁ 𝒥₂ => by
    exact { HasLimit := fun F => has_limit.mk (finite_limit_cone F) }⟩

instance (priority := 100) has_finite_colimits_of_semilattice_sup_order_bot [SemilatticeSup α] [OrderBot α] :
    has_finite_colimits α :=
  ⟨fun J 𝒥₁ 𝒥₂ => by
    exact { HasColimit := fun F => has_colimit.mk (finite_colimit_cocone F) }⟩

/-- 
The limit of a functor from a finite diagram into a `semilattice_inf` with `order_top` is the
infimum of the objects in the image.
-/
theorem finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : limit F = Finset.univ.inf F.obj :=
  (is_limit.cone_point_unique_up_to_iso (limit.is_limit F) (finite_limit_cone F).IsLimit).to_eq

/-- 
The colimit of a functor from a finite diagram into a `semilattice_sup` with `order_bot`
is the supremum of the objects in the image.
-/
theorem finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
    colimit F = Finset.univ.sup F.obj :=
  (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) (finite_colimit_cocone F).IsColimit).to_eq

/-- 
A finite product in the category of a `semilattice_inf` with `order_top` is the same as the infimum.
-/
theorem finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} [DecidableEq ι] [Fintype ι]
    (f : ι → α) : (∏ f) = (Fintype.elems ι).inf f :=
  (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (finite_limit_cone (discrete.functor f)).IsLimit).to_eq

/-- 
A finite coproduct in the category of a `semilattice_sup` with `order_bot` is the same as the
supremum.
-/
theorem finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u} [DecidableEq ι] [Fintype ι]
    (f : ι → α) : (∐ f) = (Fintype.elems ι).sup f :=
  (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
      (finite_colimit_cocone (discrete.functor f)).IsColimit).to_eq

/-- 
The binary product in the category of a `semilattice_inf` with `order_top` is the same as the
infimum.
-/
@[simp]
theorem prod_eq_inf [SemilatticeInf α] [OrderTop α] (x y : α) : limits.prod x y = x⊓y :=
  calc limits.prod x y = limit (pair x y) := rfl
    _ = Finset.univ.inf (pair x y).obj := by
    rw [finite_limit_eq_finset_univ_inf (pair x y)]
    _ = x⊓(y⊓⊤) := rfl
    _ = x⊓y := by
    rw [inf_top_eq]
    

/-- 
The binary coproduct in the category of a `semilattice_sup` with `order_bot` is the same as the
supremum.
-/
@[simp]
theorem coprod_eq_sup [SemilatticeSup α] [OrderBot α] (x y : α) : limits.coprod x y = x⊔y :=
  calc limits.coprod x y = colimit (pair x y) := rfl
    _ = Finset.univ.sup (pair x y).obj := by
    rw [finite_colimit_eq_finset_univ_sup (pair x y)]
    _ = x⊔(y⊔⊥) := rfl
    _ = x⊔y := by
    rw [sup_bot_eq]
    

/-- 
The pullback in the category of a `semilattice_inf` with `order_top` is the same as the infimum
over the objects.
-/
@[simp]
theorem pullback_eq_inf [SemilatticeInf α] [OrderTop α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z) : pullback f g = x⊓y :=
  calc pullback f g = limit (cospan f g) := rfl
    _ = Finset.univ.inf (cospan f g).obj := by
    rw [finite_limit_eq_finset_univ_inf]
    _ = z⊓(x⊓(y⊓⊤)) := rfl
    _ = z⊓(x⊓y) := by
    rw [inf_top_eq]
    _ = x⊓y := inf_eq_right.mpr (inf_le_of_left_le f.le)
    

/-- 
The pushout in the category of a `semilattice_sup` with `order_bot` is the same as the supremum
over the objects.
-/
@[simp]
theorem pushout_eq_sup [SemilatticeSup α] [OrderBot α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y) : pushout f g = x⊔y :=
  calc pushout f g = colimit (span f g) := rfl
    _ = Finset.univ.sup (span f g).obj := by
    rw [finite_colimit_eq_finset_univ_sup]
    _ = z⊔(x⊔(y⊔⊥)) := rfl
    _ = z⊔(x⊔y) := by
    rw [sup_bot_eq]
    _ = x⊔y := sup_eq_right.mpr (le_sup_of_le_left f.le)
    

end Semilattice

variable {α : Type u} [CompleteLattice α]

variable {J : Type u} [small_category J]

/-- 
The limit cone over any functor into a complete lattice.
-/
def limit_cone (F : J ⥤ α) : limit_cone F :=
  { Cone := { x := infi F.obj, π := { app := fun j => hom_of_le (CompleteLattice.Inf_le _ _ (Set.mem_range_self _)) } },
    IsLimit :=
      { lift := fun s =>
          hom_of_le
            (CompleteLattice.le_Inf _ _
              (by
                rintro _ ⟨j, rfl⟩
                exact (s.π.app j).le)) } }

/-- 
The colimit cocone over any functor into a complete lattice.
-/
def colimit_cocone (F : J ⥤ α) : colimit_cocone F :=
  { Cocone :=
      { x := supr F.obj, ι := { app := fun j => hom_of_le (CompleteLattice.le_Sup _ _ (Set.mem_range_self _)) } },
    IsColimit :=
      { desc := fun s =>
          hom_of_le
            (CompleteLattice.Sup_le _ _
              (by
                rintro _ ⟨j, rfl⟩
                exact (s.ι.app j).le)) } }

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  has_limits_of_complete_lattice
  : has_limits α
  where HasLimitsOfShape J 𝒥 := by exact { HasLimit := fun F => has_limit.mk ( limit_cone F ) }

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  has_colimits_of_complete_lattice
  : has_colimits α
  where HasColimitsOfShape J 𝒥 := by exact { HasColimit := fun F => has_colimit.mk ( colimit_cocone F ) }

/-- 
The limit of a functor into a complete lattice is the infimum of the objects in the image.
-/
theorem limit_eq_infi (F : J ⥤ α) : limit F = infi F.obj :=
  (is_limit.cone_point_unique_up_to_iso (limit.is_limit F) (limit_cone F).IsLimit).to_eq

/-- 
The colimit of a functor into a complete lattice is the supremum of the objects in the image.
-/
theorem colimit_eq_supr (F : J ⥤ α) : colimit F = supr F.obj :=
  (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) (colimit_cocone F).IsColimit).to_eq

end CategoryTheory.Limits.CompleteLattice

