import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.StructuredArrow

/-!

# Kan extensions

This file defines the right and left Kan extensions of a functor.
They exist under the assumption that the target category has enough limits
resp. colimits.

The main definitions are `Ran ι` and `Lan ι`, where `ι : S ⥤ L` is a functor.
Namely, `Ran ι` is the right Kan extension, while `Lan ι` is the left Kan extension,
both as functors `(S ⥤ D) ⥤ (L ⥤ D)`.

To access the right resp. left adjunction associated to these, use `Ran.adjunction`
resp. `Lan.adjunction`.

# Projects

A lot of boilerplate could be generalized by defining and working with pseudofunctors.

-/


noncomputable section

namespace CategoryTheory

open Limits

universe v u₁ u₂ u₃

variable {S : Type v} {L : Type u₂} {D : Type u₃}

variable [category.{v} S] [category.{v} L] [category.{v} D]

variable (ι : S ⥤ L)

namespace Ran

attribute [local simp] structured_arrow.proj

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
abbrev diagram (F : S ⥤ D) (x : L) : structured_arrow x ι ⥤ D :=
  structured_arrow.proj x ι ⋙ F

variable {ι}

/-- A cone over `Ran.diagram ι F x` used to define `Ran`. -/
@[simp]
def cone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : ι ⋙ G ⟶ F) : cone (diagram ι F x) where
  x := G.obj x
  π :=
    { app := fun i => G.map i.hom ≫ f.app i.right,
      naturality' := by
        rintro ⟨⟨il⟩, ir, i⟩ ⟨⟨jl⟩, jr, j⟩ ⟨⟨⟨fl⟩⟩, fr, ff⟩
        dsimp  at *
        simp only [category.id_comp, category.assoc] at *
        rw [ff]
        have := f.naturality
        tidy }

variable (ι)

/-- An auxiliary definition used to define `Ran`. -/
@[simps]
def loc (F : S ⥤ D) [∀ x, has_limit (diagram ι F x)] : L ⥤ D where
  obj := fun x => limit (diagram ι F x)
  map := fun x y f => limit.pre (diagram _ _ _) (structured_arrow.map f : structured_arrow _ ι ⥤ _)
  map_id' := by
    intro l
    ext j
    simp only [category.id_comp, limit.pre_π]
    congr 1
    simp
  map_comp' := by
    intro x y z f g
    ext j
    erw [limit.pre_pre, limit.pre_π, limit.pre_π]
    congr 1
    tidy

/-- An auxiliary definition used to define `Ran` and `Ran.adjunction`. -/
@[simps]
def Equivₓ (F : S ⥤ D) [∀ x, has_limit (diagram ι F x)] (G : L ⥤ D) :
    (G ⟶ loc ι F) ≃ (((whiskering_left _ _ _).obj ι).obj G ⟶ F) where
  toFun := fun f =>
    { app := fun x => f.app _ ≫ limit.π (diagram ι F (ι.obj x)) (structured_arrow.mk (𝟙 _)),
      naturality' := by
        intro x y ff
        dsimp only [whiskering_left]
        simp only [functor.comp_map, nat_trans.naturality_assoc, loc_map, category.assoc]
        congr 1
        erw [limit.pre_π]
        change _ = _ ≫ (diagram ι F (ι.obj x)).map (structured_arrow.hom_mk _ _)
        rw [limit.w]
        tidy }
  invFun := fun f =>
    { app := fun x => limit.lift (diagram ι F x) (cone _ f),
      naturality' := by
        intro x y ff
        ext j
        erw [limit.lift_pre, limit.lift_π, category.assoc, limit.lift_π (cone _ f) j]
        tidy }
  left_inv := by
    intro x
    ext k j
    dsimp only [cone]
    rw [limit.lift_π]
    simp only [nat_trans.naturality_assoc, loc_map]
    erw [limit.pre_π]
    congr
    cases j
    tidy
  right_inv := by
    tidy

end Ran

/-- The right Kan extension of a functor. -/
@[simps]
def Ran [∀ X, has_limits_of_shape (structured_arrow X ι) D] : (S ⥤ D) ⥤ L ⥤ D :=
  adjunction.right_adjoint_of_equiv (fun F G => (Ran.equiv ι G F).symm)
    (by
      tidy)

namespace Ran

variable (D)

/-- The adjunction associated to `Ran`. -/
def adjunction [∀ X, has_limits_of_shape (structured_arrow X ι) D] : (whiskering_left _ _ D).obj ι ⊣ Ran ι :=
  adjunction.adjunction_of_equiv_right _ _

theorem reflective [full ι] [faithful ι] [∀ X, has_limits_of_shape (structured_arrow X ι) D] :
    is_iso (adjunction D ι).counit := by
  apply nat_iso.is_iso_of_is_iso_app _
  intro F
  apply nat_iso.is_iso_of_is_iso_app _
  intro X
  dsimp [adjunction]
  simp only [category.id_comp]
  exact
    is_iso.of_iso
      ((limit.is_limit _).conePointUniqueUpToIso (limit_of_diagram_initial structured_arrow.mk_id_initial _))

end Ran

namespace Lan

attribute [local simp] costructured_arrow.proj

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
abbrev diagram (F : S ⥤ D) (x : L) : costructured_arrow ι x ⥤ D :=
  costructured_arrow.proj ι x ⋙ F

variable {ι}

/-- A cocone over `Lan.diagram ι F x` used to define `Lan`. -/
@[simp]
def cocone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : F ⟶ ι ⋙ G) : cocone (diagram ι F x) where
  x := G.obj x
  ι :=
    { app := fun i => f.app i.left ≫ G.map i.hom,
      naturality' := by
        rintro ⟨ir, ⟨il⟩, i⟩ ⟨jl, ⟨jr⟩, j⟩ ⟨fl, ⟨⟨fl⟩⟩, ff⟩
        dsimp  at *
        simp only [functor.comp_map, category.comp_id, nat_trans.naturality_assoc]
        rw [← G.map_comp, ff]
        tidy }

variable (ι)

/-- An auxiliary definition used to define `Lan`. -/
@[simps]
def loc (F : S ⥤ D) [I : ∀ x, has_colimit (diagram ι F x)] : L ⥤ D where
  obj := fun x => colimit (diagram ι F x)
  map := fun x y f => colimit.pre (diagram _ _ _) (costructured_arrow.map f : costructured_arrow ι _ ⥤ _)
  map_id' := by
    intro l
    ext j
    erw [colimit.ι_pre, category.comp_id]
    congr 1
    simp
  map_comp' := by
    intro x y z f g
    ext j
    let ff : costructured_arrow ι _ ⥤ _ := costructured_arrow.map f
    let gg : costructured_arrow ι _ ⥤ _ := costructured_arrow.map g
    let dd := diagram ι F z
    have : has_colimit (ff ⋙ gg ⋙ dd) := I _
    have : has_colimit ((ff ⋙ gg) ⋙ dd) := I _
    have : has_colimit (gg ⋙ dd) := I _
    change _ = colimit.ι ((ff ⋙ gg) ⋙ dd) j ≫ _ ≫ _
    erw [colimit.pre_pre dd gg ff, colimit.ι_pre, colimit.ι_pre]
    congr 1
    simp

/-- An auxiliary definition used to define `Lan` and `Lan.adjunction`. -/
@[simps]
def Equivₓ (F : S ⥤ D) [I : ∀ x, has_colimit (diagram ι F x)] (G : L ⥤ D) :
    (loc ι F ⟶ G) ≃ (F ⟶ ((whiskering_left _ _ _).obj ι).obj G) where
  toFun := fun f =>
    { app := fun x => by
        apply colimit.ι (diagram ι F (ι.obj x)) (costructured_arrow.mk (𝟙 _)) ≫ f.app _,
      naturality' := by
        intro x y ff
        dsimp only [whiskering_left]
        simp only [functor.comp_map, category.assoc]
        rw [← f.naturality (ι.map ff), ← category.assoc, ← category.assoc]
        let fff : costructured_arrow ι _ ⥤ _ := costructured_arrow.map (ι.map ff)
        have : has_colimit (fff ⋙ diagram ι F (ι.obj y)) := I _
        erw [colimit.ι_pre (diagram ι F (ι.obj y)) fff (costructured_arrow.mk (𝟙 _))]
        let xx : costructured_arrow ι (ι.obj y) := costructured_arrow.mk (ι.map ff)
        let yy : costructured_arrow ι (ι.obj y) := costructured_arrow.mk (𝟙 _)
        let fff : xx ⟶ yy :=
          costructured_arrow.hom_mk ff
            (by
              simp only [costructured_arrow.mk_hom_eq_self]
              erw [category.comp_id])
        erw [colimit.w (diagram ι F (ι.obj y)) fff]
        congr
        simp }
  invFun := fun f =>
    { app := fun x => colimit.desc (diagram ι F x) (cocone _ f),
      naturality' := by
        intro x y ff
        ext j
        erw [colimit.pre_desc, ← category.assoc, colimit.ι_desc, colimit.ι_desc]
        tidy }
  left_inv := by
    intro x
    ext k j
    rw [colimit.ι_desc]
    dsimp only [cocone]
    rw [category.assoc, ← x.naturality j.hom, ← category.assoc]
    congr 1
    change colimit.ι _ _ ≫ colimit.pre (diagram ι F k) (costructured_arrow.map _) = _
    rw [colimit.ι_pre]
    congr
    cases j
    tidy
  right_inv := by
    tidy

end Lan

/-- The left Kan extension of a functor. -/
@[simps]
def Lan [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] : (S ⥤ D) ⥤ L ⥤ D :=
  adjunction.left_adjoint_of_equiv (fun F G => Lan.equiv ι F G)
    (by
      tidy)

namespace Lan

variable (D)

/-- The adjunction associated to `Lan`. -/
def adjunction [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] : Lan ι ⊣ (whiskering_left _ _ D).obj ι :=
  adjunction.adjunction_of_equiv_left _ _

theorem coreflective [full ι] [faithful ι] [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] :
    is_iso (adjunction D ι).Unit := by
  apply nat_iso.is_iso_of_is_iso_app _
  intro F
  apply nat_iso.is_iso_of_is_iso_app _
  intro X
  dsimp [adjunction]
  simp only [category.comp_id]
  exact
    is_iso.of_iso
      ((colimit.is_colimit _).coconePointUniqueUpToIso
          (colimit_of_diagram_terminal costructured_arrow.mk_id_terminal _)).symm

end Lan

end CategoryTheory

