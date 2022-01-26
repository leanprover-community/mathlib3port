import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.EpiMono

/-!

# Adjunctions involving evaluation

We show that evaluation of functors have adjoints, given the existence of (co)products.

-/


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [category.{v₁} C] (D : Type u₂) [category.{v₂} D]

noncomputable section

section

variable [∀ a b : C, has_coproducts_of_shape (a ⟶ b) D]

/-- The left adjoint of evaluation. -/
@[simps]
def evaluation_left_adjoint (c : C) : D ⥤ C ⥤ D where
  obj := fun d =>
    { obj := fun t => ∐ fun i : c ⟶ t => d, map := fun u v f => sigma.desc fun g => (sigma.ι fun _ => d) <| g ≫ f,
      map_id' := by
        intros
        ext
        simp only [cofan.mk_ι_app, colimit.ι_desc, category.comp_id]
        congr 1
        rw [category.comp_id],
      map_comp' := by
        intros
        ext
        simp only [cofan.mk_ι_app, colimit.ι_desc_assoc, colimit.ι_desc]
        congr 1
        rw [category.assoc] }
  map := fun d₁ d₂ f =>
    { app := fun e => sigma.desc fun h => f ≫ sigma.ι (fun _ => d₂) h,
      naturality' := by
        intros
        ext
        dsimp
        simp }
  map_id' := by
    intros
    ext
    dsimp
    simp
  map_comp' := by
    intros
    ext
    dsimp
    simp

/-- The adjunction showing that evaluation is a right adjoint. -/
@[simps unit_app counit_app_app]
def evaluation_adjunction_right (c : C) : evaluation_left_adjoint D c ⊣ (evaluation _ _).obj c :=
  adjunction.mk_of_hom_equiv
    { homEquiv := fun d F =>
        { toFun := fun f => sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c,
          invFun := fun f =>
            { app := fun e => sigma.desc fun h => f ≫ F.map h,
              naturality' := by
                intros
                ext
                dsimp
                simp },
          left_inv := by
            intro f
            ext x g
            dsimp
            simp only [colimit.ι_desc, limits.cofan.mk_ι_app, category.assoc, ← f.naturality,
              evaluation_left_adjoint_obj_map, colimit.ι_desc_assoc, cofan.mk_ι_app]
            congr 2
            rw [category.id_comp],
          right_inv := fun f => by
            dsimp
            simp },
      hom_equiv_naturality_left_symm' := by
        intros
        ext
        dsimp
        simp ,
      hom_equiv_naturality_right' := by
        intros
        dsimp
        simp }

instance evaluation_is_right_adjoint (c : C) : is_right_adjoint ((evaluation _ D).obj c) :=
  ⟨_, evaluation_adjunction_right _ _⟩

theorem nat_trans.mono_iff_app_mono {F G : C ⥤ D} (η : F ⟶ G) : mono η ↔ ∀ c, mono (η.app c) := by
  constructor
  · intro h c
    exact right_adjoint_preserves_mono (evaluation_adjunction_right D c) h
    
  · intros _
    apply nat_trans.mono_app_of_mono
    

end

section

variable [∀ a b : C, has_products_of_shape (a ⟶ b) D]

/-- The right adjoint of evaluation. -/
@[simps]
def evaluation_right_adjoint (c : C) : D ⥤ C ⥤ D where
  obj := fun d =>
    { obj := fun t => ∏ fun i : t ⟶ c => d, map := fun u v f => pi.lift fun g => pi.π _ <| f ≫ g,
      map_id' := by
        intros
        ext
        dsimp
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app]
        congr
        simp ,
      map_comp' := by
        intros
        ext
        dsimp
        simp only [limit.lift_π, fan.mk_π_app, category.assoc]
        congr 1
        simp }
  map := fun d₁ d₂ f =>
    { app := fun t => pi.lift fun g => pi.π _ g ≫ f,
      naturality' := by
        intros
        ext
        dsimp
        simp }
  map_id' := by
    intros
    ext
    dsimp
    simp
  map_comp' := by
    intros
    ext
    dsimp
    simp

/-- The adjunction showing that evaluation is a left adjoint. -/
@[simps unit_app_app counit_app]
def evaluation_adjunction_left (c : C) : (evaluation _ _).obj c ⊣ evaluation_right_adjoint D c :=
  adjunction.mk_of_hom_equiv
    { homEquiv := fun F d =>
        { toFun := fun f =>
            { app := fun t => pi.lift fun g => F.map g ≫ f,
              naturality' := by
                intros
                ext
                dsimp
                simp },
          invFun := fun f => f.app _ ≫ pi.π _ (𝟙 _),
          left_inv := fun f => by
            dsimp
            simp ,
          right_inv := by
            intro f
            ext x g
            dsimp
            simp only [limit.lift_π, evaluation_right_adjoint_obj_map, nat_trans.naturality_assoc, fan.mk_π_app]
            congr
            rw [category.comp_id] },
      hom_equiv_naturality_left_symm' := by
        intros
        dsimp
        simp ,
      hom_equiv_naturality_right' := by
        intros
        ext
        dsimp
        simp }

instance evaluation_is_left_adjoint (c : C) : is_left_adjoint ((evaluation _ D).obj c) :=
  ⟨_, evaluation_adjunction_left _ _⟩

theorem nat_trans.epi_iff_app_epi {F G : C ⥤ D} (η : F ⟶ G) : epi η ↔ ∀ c, epi (η.app c) := by
  constructor
  · intro h c
    exact left_adjoint_preserves_epi (evaluation_adjunction_left D c) h
    
  · intros
    apply nat_trans.epi_app_of_epi
    

end

end CategoryTheory

