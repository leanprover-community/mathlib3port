import Mathbin.CategoryTheory.Category.Preorder 
import Mathbin.CategoryTheory.IsomorphismClasses 
import Mathbin.CategoryTheory.Thin

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of an arbitrary category by taking isomorphism classes, and show it is a
skeleton of the original category.

In addition, construct the skeleton of a thin category as a partial ordering, and (noncomputably)
show it is a skeleton of the original category. The advantage of this special case being handled
separately is that lemmas and definitions about orderings can be used directly, for example for the
subobject lattice. In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

variable(C : Type u₁)[category.{v₁} C]

variable(D : Type u₂)[category.{v₂} D]

variable{E : Type u₃}[category.{v₃} E]

/-- A category is skeletal if isomorphic objects are equal. -/
def skeletal : Prop :=
  ∀ ⦃X Y : C⦄, is_isomorphic X Y → X = Y

/--
`is_skeleton_of C D F` says that `F : D ⥤ C` exhibits `D` as a skeletal full subcategory of `C`,
in particular `F` is a (strong) equivalence and `D` is skeletal.
-/
structure is_skeleton_of(F : D ⥤ C) where 
  skel : skeletal D 
  eqv : is_equivalence F

attribute [local instance] is_isomorphic_setoid

variable{C D}

/-- If `C` is thin and skeletal, then any naturally isomorphic functors to `C` are equal. -/
theorem functor.eq_of_iso {F₁ F₂ : D ⥤ C} [∀ X Y : C, Subsingleton (X ⟶ Y)] (hC : skeletal C) (hF : F₁ ≅ F₂) :
  F₁ = F₂ :=
  Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elimₓ _ _

/--
If `C` is thin and skeletal, `D ⥤ C` is skeletal.
`category_theory.functor_thin` shows it is thin also.
-/
theorem functor_skeletal [∀ X Y : C, Subsingleton (X ⟶ Y)] (hC : skeletal C) : skeletal (D ⥤ C) :=
  fun F₁ F₂ h => h.elim (functor.eq_of_iso hC)

variable(C D)

-- error in CategoryTheory.Skeletal: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/--
Construct the skeleton category as the induced category on the isomorphism classes, and derive
its category structure.
-/ @[derive #[expr category]] def skeleton : Type u₁ :=
induced_category C quotient.out

instance  [Inhabited C] : Inhabited (skeleton C) :=
  ⟨«expr⟦ ⟧» (default C)⟩

-- error in CategoryTheory.Skeletal: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler full
/-- The functor from the skeleton of `C` to `C`. -/
@[simps #[], derive #["[", expr full, ",", expr faithful, "]"]]
noncomputable
def from_skeleton : «expr ⥤ »(skeleton C, C) :=
induced_functor _

instance  : ess_surj (from_skeleton C) :=
  { mem_ess_image := fun X => ⟨Quotientₓ.mk X, Quotientₓ.mk_out X⟩ }

noncomputable instance  : is_equivalence (from_skeleton C) :=
  equivalence.of_fully_faithfully_ess_surj (from_skeleton C)

/-- The equivalence between the skeleton and the category itself. -/
noncomputable def skeleton_equivalence : skeleton C ≌ C :=
  (from_skeleton C).asEquivalence

-- error in CategoryTheory.Skeletal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem skeleton_skeletal : skeletal (skeleton C) :=
begin
  rintro [ident X, ident Y, "⟨", ident h, "⟩"],
  have [] [":", expr «expr ≈ »(X.out, Y.out)] [":=", expr ⟨(from_skeleton C).map_iso h⟩],
  simpa [] [] [] [] [] ["using", expr quotient.sound this]
end

/-- The `skeleton` of `C` given by choice is a skeleton of `C`. -/
noncomputable def skeleton_is_skeleton : is_skeleton_of C (skeleton C) (from_skeleton C) :=
  { skel := skeleton_skeletal C, eqv := from_skeleton.is_equivalence C }

section 

variable{C D}

/--
Two categories which are categorically equivalent have skeletons with equivalent objects.
-/
noncomputable def equivalence.skeleton_equiv (e : C ≌ D) : skeleton C ≃ skeleton D :=
  let f := ((skeleton_equivalence C).trans e).trans (skeleton_equivalence D).symm
  { toFun := f.functor.obj, invFun := f.inverse.obj, left_inv := fun X => skeleton_skeletal C ⟨(f.unit_iso.app X).symm⟩,
    right_inv := fun Y => skeleton_skeletal D ⟨f.counit_iso.app Y⟩ }

end 

/--
Construct the skeleton category by taking the quotient of objects. This construction gives a
preorder with nice definitional properties, but is only really appropriate for thin categories.
If your original category is not thin, you probably want to be using `skeleton` instead of this.
-/
def thin_skeleton : Type u₁ :=
  Quotientₓ (is_isomorphic_setoid C)

instance inhabited_thin_skeleton [Inhabited C] : Inhabited (thin_skeleton C) :=
  ⟨Quotientₓ.mk (default _)⟩

instance thin_skeleton.preorder : Preorderₓ (thin_skeleton C) :=
  { le :=
      Quotientₓ.lift₂ (fun X Y => Nonempty (X ⟶ Y))
        (by 
          rintro _ _ _ _ ⟨i₁⟩ ⟨i₂⟩
          exact propext ⟨Nonempty.map fun f => i₁.inv ≫ f ≫ i₂.hom, Nonempty.map fun f => i₁.hom ≫ f ≫ i₂.inv⟩),
    le_refl :=
      by 
        refine' Quotientₓ.ind fun a => _ 
        exact ⟨𝟙 _⟩,
    le_trans := fun a b c => Quotientₓ.induction_on₃ a b c$ fun A B C => Nonempty.map2 (· ≫ ·) }

/-- The functor from a category to its thin skeleton. -/
@[simps]
def to_thin_skeleton : C ⥤ thin_skeleton C :=
  { obj := Quotientₓ.mk, map := fun X Y f => hom_of_le (Nonempty.intro f) }

/-!
The constructions here are intended to be used when the category `C` is thin, even though
some of the statements can be shown without this assumption.
-/


namespace ThinSkeleton

/-- The thin skeleton is thin. -/
instance thin {X Y : thin_skeleton C} : Subsingleton (X ⟶ Y) :=
  ⟨by 
      rintro ⟨⟨f₁⟩⟩ ⟨⟨f₂⟩⟩
      rfl⟩

variable{C}{D}

/-- A functor `C ⥤ D` computably lowers to a functor `thin_skeleton C ⥤ thin_skeleton D`. -/
@[simps]
def map (F : C ⥤ D) : thin_skeleton C ⥤ thin_skeleton D :=
  { obj := Quotientₓ.map F.obj$ fun X₁ X₂ ⟨hX⟩ => ⟨F.map_iso hX⟩,
    map := fun X Y => Quotientₓ.recOnSubsingleton₂ X Y$ fun x y k => hom_of_le (k.le.elim fun t => ⟨F.map t⟩) }

theorem comp_to_thin_skeleton (F : C ⥤ D) : F ⋙ to_thin_skeleton D = to_thin_skeleton C ⋙ map F :=
  rfl

/-- Given a natural transformation `F₁ ⟶ F₂`, induce a natural transformation `map F₁ ⟶ map F₂`.-/
def map_nat_trans {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ :=
  { app := fun X => Quotientₓ.recOnSubsingleton X fun x => ⟨⟨⟨k.app x⟩⟩⟩ }

/-- A functor `C ⥤ D ⥤ E` computably lowers to a functor
`thin_skeleton C ⥤ thin_skeleton D ⥤ thin_skeleton E` -/
@[simps]
def map₂ (F : C ⥤ D ⥤ E) : thin_skeleton C ⥤ thin_skeleton D ⥤ thin_skeleton E :=
  { obj :=
      fun x =>
        { obj :=
            fun y =>
              Quotientₓ.map₂ (fun X Y => (F.obj X).obj Y)
                (fun X₁ X₂ ⟨hX⟩ Y₁ Y₂ ⟨hY⟩ => ⟨(F.obj X₁).mapIso hY ≪≫ (F.map_iso hX).app Y₂⟩) x y,
          map :=
            fun y₁ y₂ =>
              Quotientₓ.recOnSubsingleton x$
                fun X =>
                  Quotientₓ.recOnSubsingleton₂ y₁ y₂$
                    fun Y₁ Y₂ hY => hom_of_le (hY.le.elim fun g => ⟨(F.obj X).map g⟩) },
    map :=
      fun x₁ x₂ =>
        Quotientₓ.recOnSubsingleton₂ x₁ x₂$
          fun X₁ X₂ f =>
            { app :=
                fun y => Quotientₓ.recOnSubsingleton y fun Y => hom_of_le (f.le.elim fun f' => ⟨(F.map f').app Y⟩) } }

variable(C)

section 

variable[∀ X Y : C, Subsingleton (X ⟶ Y)]

instance to_thin_skeleton_faithful : faithful (to_thin_skeleton C) :=
  {  }

/-- Use `quotient.out` to create a functor out of the thin skeleton. -/
@[simps]
noncomputable def from_thin_skeleton : thin_skeleton C ⥤ C :=
  { obj := Quotientₓ.out,
    map :=
      fun x y =>
        Quotientₓ.recOnSubsingleton₂ x y$
          fun X Y f => (Nonempty.some (Quotientₓ.mk_out X)).Hom ≫ f.le.some ≫ (Nonempty.some (Quotientₓ.mk_out Y)).inv }

noncomputable instance from_thin_skeleton_equivalence : is_equivalence (from_thin_skeleton C) :=
  { inverse := to_thin_skeleton C,
    counitIso :=
      nat_iso.of_components (fun X => Nonempty.some (Quotientₓ.mk_out X))
        (by 
          tidy),
    unitIso :=
      nat_iso.of_components
        (fun x =>
          Quotientₓ.recOnSubsingleton x
            fun X => eq_to_iso (Quotientₓ.sound ⟨(Nonempty.some (Quotientₓ.mk_out X)).symm⟩))
        (by 
          tidy) }

/-- The equivalence between the thin skeleton and the category itself. -/
noncomputable def Equivalenceₓ : thin_skeleton C ≌ C :=
  (from_thin_skeleton C).asEquivalence

variable{C}

theorem equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
  ⟨iso_of_both_ways f g⟩

instance thin_skeleton_partial_order : PartialOrderₓ (thin_skeleton C) :=
  { CategoryTheory.ThinSkeleton.preorder C with
    le_antisymm :=
      Quotientₓ.ind₂
        (by 
          rintro _ _ ⟨f⟩ ⟨g⟩
          apply Quotientₓ.sound (equiv_of_both_ways f g)) }

theorem skeletal : skeletal (thin_skeleton C) :=
  fun X Y => Quotientₓ.induction_on₂ X Y$ fun x y h => h.elim$ fun i => i.1.le.antisymm i.2.le

theorem map_comp_eq (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G :=
  functor.eq_of_iso skeletal$
    nat_iso.of_components (fun X => Quotientₓ.recOnSubsingleton X fun x => iso.refl _)
      (by 
        tidy)

theorem map_id_eq : map (𝟭 C) = 𝟭 (thin_skeleton C) :=
  functor.eq_of_iso skeletal$
    nat_iso.of_components (fun X => Quotientₓ.recOnSubsingleton X fun x => iso.refl _)
      (by 
        tidy)

theorem map_iso_eq {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂ :=
  functor.eq_of_iso skeletal { Hom := map_nat_trans h.hom, inv := map_nat_trans h.inv }

/-- `from_thin_skeleton C` exhibits the thin skeleton as a skeleton. -/
noncomputable def thin_skeleton_is_skeleton : is_skeleton_of C (thin_skeleton C) (from_thin_skeleton C) :=
  { skel := skeletal, eqv := thin_skeleton.from_thin_skeleton_equivalence C }

noncomputable instance is_skeleton_of_inhabited :
  Inhabited (is_skeleton_of C (thin_skeleton C) (from_thin_skeleton C)) :=
  ⟨thin_skeleton_is_skeleton⟩

end 

variable{C}

-- error in CategoryTheory.Skeletal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An adjunction between thin categories gives an adjunction between their thin skeletons. -/
def lower_adjunction
(R : «expr ⥤ »(D, C))
(L : «expr ⥤ »(C, D))
(h : «expr ⊣ »(L, R)) : «expr ⊣ »(thin_skeleton.map L, thin_skeleton.map R) :=
adjunction.mk_of_unit_counit { unit := { app := λ X, begin
      letI [] [] [":=", expr is_isomorphic_setoid C],
      refine [expr quotient.rec_on_subsingleton X (λ x, hom_of_le ⟨h.unit.app x⟩)]
    end },
  counit := { app := λ X, begin
      letI [] [] [":=", expr is_isomorphic_setoid D],
      refine [expr quotient.rec_on_subsingleton X (λ x, hom_of_le ⟨h.counit.app x⟩)]
    end } }

end ThinSkeleton

open ThinSkeleton

section 

variable{C}{α : Type _}[PartialOrderₓ α]

/--
When `e : C ≌ α` is a categorical equivalence from a thin category `C` to some partial order `α`,
the `thin_skeleton C` is order isomorphic to `α`.
-/
noncomputable def equivalence.thin_skeleton_order_iso [∀ X Y : C, Subsingleton (X ⟶ Y)] (e : C ≌ α) :
  thin_skeleton C ≃o α :=
  ((thin_skeleton.equivalence C).trans e).toOrderIso

end 

end CategoryTheory

