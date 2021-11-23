import Mathbin.CategoryTheory.Subobject.FactorThru 
import Mathbin.CategoryTheory.Subobject.WellPowered

/-!
# The lattice of subobjects

We provide the `semilattice_inf_top (subobject X)` instance when `[has_pullback C]`,
and the `semilattice_sup (subobject X)` instance when `[has_images C] [has_binary_coproducts C]`.
-/


universe v₁ v₂ u₁ u₂

noncomputable theory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable{C : Type u₁}[category.{v₁} C]{X Y Z : C}

variable{D : Type u₂}[category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

section HasTop

instance  {X : C} : HasTop (mono_over X) :=
  { top := mk' (𝟙 _) }

instance  {X : C} : Inhabited (mono_over X) :=
  ⟨⊤⟩

/-- The morphism to the top object in `mono_over X`. -/
def le_top (f : mono_over X) : f ⟶ ⊤ :=
  hom_mk f.arrow (comp_id _)

@[simp]
theorem top_left (X : C) : ((⊤ : mono_over X) : C) = X :=
  rfl

@[simp]
theorem top_arrow (X : C) : (⊤ : mono_over X).arrow = 𝟙 X :=
  rfl

/-- `map f` sends `⊤ : mono_over X` to `⟨X, f⟩ : mono_over Y`. -/
def map_top (f : X ⟶ Y) [mono f] : (map f).obj ⊤ ≅ mk' f :=
  iso_of_both_ways (hom_mk (𝟙 _) rfl)
    (hom_mk (𝟙 _)
      (by 
        simp [id_comp f]))

section 

variable[has_pullbacks C]

/-- The pullback of the top object in `mono_over Y`
is (isomorphic to) the top object in `mono_over X`. -/
def pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤ :=
  iso_of_both_ways (le_top _)
    (hom_mk
      (pullback.lift f (𝟙 _)
        (by 
          tidy))
      (pullback.lift_snd _ _ _))

/-- There is a morphism from `⊤ : mono_over A` to the pullback of a monomorphism along itself;
as the category is thin this is an isomorphism. -/
def top_le_pullback_self {A B : C} (f : A ⟶ B) [mono f] : (⊤ : mono_over A) ⟶ (pullback f).obj (mk' f) :=
  hom_mk _ (pullback.lift_snd _ _ rfl)

/-- The pullback of a monomorphism along itself is isomorphic to the top object. -/
def pullback_self {A B : C} (f : A ⟶ B) [mono f] : (pullback f).obj (mk' f) ≅ ⊤ :=
  iso_of_both_ways (le_top _) (top_le_pullback_self _)

end 

end HasTop

section HasBot

variable[has_initial C][initial_mono_class C]

instance  {X : C} : HasBot (mono_over X) :=
  { bot := mk' (initial.to X) }

@[simp]
theorem bot_left (X : C) : ((⊥ : mono_over X) : C) = ⊥_ C :=
  rfl

@[simp]
theorem bot_arrow {X : C} : (⊥ : mono_over X).arrow = initial.to X :=
  rfl

/-- The (unique) morphism from `⊥ : mono_over X` to any other `f : mono_over X`. -/
def bot_le {X : C} (f : mono_over X) : ⊥ ⟶ f :=
  hom_mk (initial.to _)
    (by 
      simp )

/-- `map f` sends `⊥ : mono_over X` to `⊥ : mono_over Y`. -/
def map_bot (f : X ⟶ Y) [mono f] : (map f).obj ⊥ ≅ ⊥ :=
  iso_of_both_ways
    (hom_mk (initial.to _)
      (by 
        simp ))
    (hom_mk (𝟙 _)
      (by 
        simp ))

end HasBot

section ZeroOrderBot

variable[has_zero_object C]

open_locale ZeroObject

/-- The object underlying `⊥ : subobject B` is (up to isomorphism) the zero object. -/
def bot_coe_iso_zero {B : C} : ((⊥ : mono_over B) : C) ≅ 0 :=
  initial_is_initial.uniqueUpToIso has_zero_object.zero_is_initial

@[simp]
theorem bot_arrow_eq_zero [has_zero_morphisms C] {B : C} : (⊥ : mono_over B).arrow = 0 :=
  zero_of_source_iso_zero _ bot_coe_iso_zero

end ZeroOrderBot

section Inf

variable[has_pullbacks C]

/--
When `[has_pullbacks C]`, `mono_over A` has "intersections", functorial in both arguments.

As `mono_over A` is only a preorder, this doesn't satisfy the axioms of `semilattice_inf`,
but we reuse all the names from `semilattice_inf` because they will be used to construct
`semilattice_inf (subobject A)` shortly.
-/
@[simps]
def inf {A : C} : mono_over A ⥤ mono_over A ⥤ mono_over A :=
  { obj := fun f => pullback f.arrow ⋙ map f.arrow,
    map :=
      fun f₁ f₂ k =>
        { app :=
            fun g =>
              by 
                apply hom_mk _ _ 
                apply pullback.lift pullback.fst (pullback.snd ≫ k.left) _ 
                rw [pullback.condition, assoc, w k]
                dsimp 
                rw [pullback.lift_snd_assoc, assoc, w k] } }

/-- A morphism from the "infimum" of two objects in `mono_over A` to the first object. -/
def inf_le_left {A : C} (f g : mono_over A) : (inf.obj f).obj g ⟶ f :=
  hom_mk _ rfl

/-- A morphism from the "infimum" of two objects in `mono_over A` to the second object. -/
def inf_le_right {A : C} (f g : mono_over A) : (inf.obj f).obj g ⟶ g :=
  hom_mk _ pullback.condition

/-- A morphism version of the `le_inf` axiom. -/
def le_inf {A : C} (f g h : mono_over A) : (h ⟶ f) → (h ⟶ g) → (h ⟶ (inf.obj f).obj g) :=
  by 
    intro k₁ k₂ 
    refine' hom_mk (pullback.lift k₂.left k₁.left _) _ 
    rw [w k₁, w k₂]
    erw [pullback.lift_snd_assoc, w k₁]

end Inf

section Sup

variable[has_images C][has_binary_coproducts C]

/-- When `[has_images C] [has_binary_coproducts C]`, `mono_over A` has a `sup` construction,
which is functorial in both arguments,
and which on `subobject A` will induce a `semilattice_sup`. -/
def sup {A : C} : mono_over A ⥤ mono_over A ⥤ mono_over A :=
  curry_obj ((forget A).Prod (forget A) ⋙ uncurry.obj over.coprod ⋙ image)

/-- A morphism version of `le_sup_left`. -/
def le_sup_left {A : C} (f g : mono_over A) : f ⟶ (sup.obj f).obj g :=
  by 
    refine' hom_mk (coprod.inl ≫ factor_thru_image _) _ 
    erw [category.assoc, image.fac, coprod.inl_desc]
    rfl

/-- A morphism version of `le_sup_right`. -/
def le_sup_right {A : C} (f g : mono_over A) : g ⟶ (sup.obj f).obj g :=
  by 
    refine' hom_mk (coprod.inr ≫ factor_thru_image _) _ 
    erw [category.assoc, image.fac, coprod.inr_desc]
    rfl

/-- A morphism version of `sup_le`. -/
def sup_le {A : C} (f g h : mono_over A) : (f ⟶ h) → (g ⟶ h) → ((sup.obj f).obj g ⟶ h) :=
  by 
    intro k₁ k₂ 
    refine' hom_mk _ _ 
    apply image.lift ⟨_, h.arrow, coprod.desc k₁.left k₂.left, _⟩
    ·
      dsimp 
      ext1
      ·
        simp [w k₁]
      ·
        simp [w k₂]
    ·
      apply image.lift_fac

end Sup

end MonoOver

namespace Subobject

section OrderTop

instance OrderTop {X : C} : OrderTop (subobject X) :=
  { top := Quotientₓ.mk' ⊤,
    le_top :=
      by 
        refine' Quotientₓ.ind' fun f => _ 
        exact ⟨mono_over.le_top f⟩ }

instance  {X : C} : Inhabited (subobject X) :=
  ⟨⊤⟩

theorem top_eq_id (B : C) : (⊤ : subobject B) = subobject.mk (𝟙 B) :=
  rfl

theorem underlying_iso_top_hom {B : C} : (underlying_iso (𝟙 B)).Hom = (⊤ : subobject B).arrow :=
  by 
    convert underlying_iso_hom_comp_eq_mk (𝟙 B)
    simp only [comp_id]

instance top_arrow_is_iso {B : C} : is_iso (⊤ : subobject B).arrow :=
  by 
    rw [←underlying_iso_top_hom]
    infer_instance

@[simp, reassoc]
theorem underlying_iso_inv_top_arrow {B : C} : (underlying_iso _).inv ≫ (⊤ : subobject B).arrow = 𝟙 B :=
  underlying_iso_arrow _

@[simp]
theorem map_top (f : X ⟶ Y) [mono f] : (map f).obj ⊤ = subobject.mk f :=
  Quotientₓ.sound' ⟨mono_over.map_top f⟩

theorem top_factors {A B : C} (f : A ⟶ B) : (⊤ : subobject B).Factors f :=
  ⟨f, comp_id _⟩

theorem is_iso_iff_mk_eq_top {X Y : C} (f : X ⟶ Y) [mono f] : is_iso f ↔ mk f = ⊤ :=
  ⟨fun _ =>
      by 
        exact mk_eq_mk_of_comm _ _ (as_iso f) (category.comp_id _),
    fun h =>
      by 
        rw [←of_mk_le_mk_comp h.le, category.comp_id]
        exact is_iso.of_iso (iso_of_mk_eq_mk _ _ h)⟩

theorem is_iso_arrow_iff_eq_top {Y : C} (P : subobject Y) : is_iso P.arrow ↔ P = ⊤ :=
  by 
    rw [is_iso_iff_mk_eq_top, mk_arrow]

instance is_iso_top_arrow {Y : C} : is_iso (⊤ : subobject Y).arrow :=
  by 
    rw [is_iso_arrow_iff_eq_top]

theorem mk_eq_top_of_is_iso {X Y : C} (f : X ⟶ Y) [is_iso f] : mk f = ⊤ :=
  (is_iso_iff_mk_eq_top f).mp inferInstance

theorem eq_top_of_is_iso_arrow {Y : C} (P : subobject Y) [is_iso P.arrow] : P = ⊤ :=
  (is_iso_arrow_iff_eq_top P).mp inferInstance

section 

variable[has_pullbacks C]

theorem pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤ :=
  Quotientₓ.sound' ⟨mono_over.pullback_top f⟩

theorem pullback_self {A B : C} (f : A ⟶ B) [mono f] : (pullback f).obj (mk f) = ⊤ :=
  Quotientₓ.sound' ⟨mono_over.pullback_self f⟩

end 

end OrderTop

section OrderBot

variable[has_initial C][initial_mono_class C]

instance OrderBot {X : C} : OrderBot (subobject X) :=
  { bot := Quotientₓ.mk' ⊥,
    bot_le :=
      by 
        refine' Quotientₓ.ind' fun f => _ 
        exact ⟨mono_over.bot_le f⟩ }

theorem bot_eq_initial_to {B : C} : (⊥ : subobject B) = subobject.mk (initial.to B) :=
  rfl

/-- The object underlying `⊥ : subobject B` is (up to isomorphism) the initial object. -/
def bot_coe_iso_initial {B : C} : ((⊥ : subobject B) : C) ≅ ⊥_ C :=
  underlying_iso _

theorem map_bot (f : X ⟶ Y) [mono f] : (map f).obj ⊥ = ⊥ :=
  Quotientₓ.sound' ⟨mono_over.map_bot f⟩

end OrderBot

section ZeroOrderBot

variable[has_zero_object C]

open_locale ZeroObject

/-- The object underlying `⊥ : subobject B` is (up to isomorphism) the zero object. -/
def bot_coe_iso_zero {B : C} : ((⊥ : subobject B) : C) ≅ 0 :=
  bot_coe_iso_initial ≪≫ initial_is_initial.uniqueUpToIso has_zero_object.zero_is_initial

variable[has_zero_morphisms C]

theorem bot_eq_zero {B : C} : (⊥ : subobject B) = subobject.mk (0 : 0 ⟶ B) :=
  mk_eq_mk_of_comm _ _ (initial_is_initial.uniqueUpToIso has_zero_object.zero_is_initial)
    (by 
      simp )

@[simp]
theorem bot_arrow {B : C} : (⊥ : subobject B).arrow = 0 :=
  zero_of_source_iso_zero _ bot_coe_iso_zero

theorem bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : subobject B).Factors f ↔ f = 0 :=
  ⟨by 
      rintro ⟨h, rfl⟩
      simp ,
    by 
      rintro rfl 
      exact
        ⟨0,
          by 
            simp ⟩⟩

end ZeroOrderBot

section Functor

variable(C)

/-- Sending `X : C` to `subobject X` is a contravariant functor `Cᵒᵖ ⥤ Type`. -/
@[simps]
def Functor [has_pullbacks C] : «expr ᵒᵖ» C ⥤ Type max u₁ v₁ :=
  { obj := fun X => subobject X.unop, map := fun X Y f => (pullback f.unop).obj, map_id' := fun X => funext pullback_id,
    map_comp' := fun X Y Z f g => funext (pullback_comp _ _) }

end Functor

section SemilatticeInfTop

variable[has_pullbacks C]

/-- The functorial infimum on `mono_over A` descends to an infimum on `subobject A`. -/
def inf {A : C} : subobject A ⥤ subobject A ⥤ subobject A :=
  thin_skeleton.map₂ mono_over.inf

theorem inf_le_left {A : C} (f g : subobject A) : (inf.obj f).obj g ≤ f :=
  Quotientₓ.induction_on₂' f g fun a b => ⟨mono_over.inf_le_left _ _⟩

theorem inf_le_right {A : C} (f g : subobject A) : (inf.obj f).obj g ≤ g :=
  Quotientₓ.induction_on₂' f g fun a b => ⟨mono_over.inf_le_right _ _⟩

theorem le_inf {A : C} (h f g : subobject A) : h ≤ f → h ≤ g → h ≤ (inf.obj f).obj g :=
  Quotientₓ.induction_on₃' h f g
    (by 
      rintro f g h ⟨k⟩ ⟨l⟩
      exact ⟨mono_over.le_inf _ _ _ k l⟩)

instance  {B : C} : SemilatticeInfTop (subobject B) :=
  { subobject.order_top, subobject.partial_order B with inf := fun m n => (inf.obj m).obj n, inf_le_left := inf_le_left,
    inf_le_right := inf_le_right, le_inf := le_inf }

theorem factors_left_of_inf_factors {A B : C} {X Y : subobject B} {f : A ⟶ B} (h : (X⊓Y).Factors f) : X.factors f :=
  factors_of_le _ (inf_le_left _ _) h

theorem factors_right_of_inf_factors {A B : C} {X Y : subobject B} {f : A ⟶ B} (h : (X⊓Y).Factors f) : Y.factors f :=
  factors_of_le _ (inf_le_right _ _) h

@[simp]
theorem inf_factors {A B : C} {X Y : subobject B} (f : A ⟶ B) : (X⊓Y).Factors f ↔ X.factors f ∧ Y.factors f :=
  ⟨fun h => ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩,
    by 
      revert X Y 
      refine' Quotientₓ.ind₂' _ 
      rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩
      exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩⟩

theorem inf_arrow_factors_left {B : C} (X Y : subobject B) : X.factors (X⊓Y).arrow :=
  (factors_iff _ _).mpr
    ⟨of_le (X⊓Y) X (inf_le_left X Y),
      by 
        simp ⟩

theorem inf_arrow_factors_right {B : C} (X Y : subobject B) : Y.factors (X⊓Y).arrow :=
  (factors_iff _ _).mpr
    ⟨of_le (X⊓Y) Y (inf_le_right X Y),
      by 
        simp ⟩

@[simp]
theorem finset_inf_factors {I : Type _} {A B : C} {s : Finset I} {P : I → subobject B} (f : A ⟶ B) :
  (s.inf P).Factors f ↔ ∀ i _ : i ∈ s, (P i).Factors f :=
  by 
    classical 
    apply Finset.induction_on s
    ·
      simp [top_factors]
    ·
      intro i s nm ih 
      simp [ih]

theorem finset_inf_arrow_factors {I : Type _} {B : C} (s : Finset I) (P : I → subobject B) (i : I) (m : i ∈ s) :
  (P i).Factors (s.inf P).arrow :=
  by 
    revert i m 
    classical 
    apply Finset.induction_on s
    ·
      rintro _ ⟨⟩
    ·
      intro i s nm ih j m 
      rw [Finset.inf_insert]
      simp only [Finset.mem_insert] at m 
      rcases m with (rfl | m)
      ·
        rw [←factor_thru_arrow _ _ (inf_arrow_factors_left _ _)]
        exact factors_comp_arrow _
      ·
        rw [←factor_thru_arrow _ _ (inf_arrow_factors_right _ _)]
        apply factors_of_factors_right 
        exact ih _ m

theorem inf_eq_map_pullback' {A : C} (f₁ : mono_over A) (f₂ : subobject A) :
  (subobject.inf.obj (Quotientₓ.mk' f₁)).obj f₂ = (subobject.map f₁.arrow).obj ((subobject.pullback f₁.arrow).obj f₂) :=
  by 
    apply Quotientₓ.induction_on' f₂ 
    intro f₂ 
    rfl

theorem inf_eq_map_pullback {A : C} (f₁ : mono_over A) (f₂ : subobject A) :
  (Quotientₓ.mk' f₁⊓f₂ : subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) :=
  inf_eq_map_pullback' f₁ f₂

theorem prod_eq_inf {A : C} {f₁ f₂ : subobject A} [has_binary_product f₁ f₂] : (f₁ ⨯ f₂) = f₁⊓f₂ :=
  le_antisymmₓ (_root_.le_inf limits.prod.fst.le limits.prod.snd.le)
    (prod.lift _root_.inf_le_left.Hom _root_.inf_le_right.Hom).le

theorem inf_def {B : C} (m m' : subobject B) : m⊓m' = (inf.obj m).obj m' :=
  rfl

/-- `⊓` commutes with pullback. -/
theorem inf_pullback {X Y : C} (g : X ⟶ Y) f₁ f₂ : (pullback g).obj (f₁⊓f₂) = (pullback g).obj f₁⊓(pullback g).obj f₂ :=
  by 
    revert f₁ 
    apply Quotientₓ.ind' 
    intro f₁ 
    erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ←pullback_comp,
      ←map_pullback pullback.condition (pullback_is_pullback f₁.arrow g), ←pullback_comp, pullback.condition]
    rfl

/-- `⊓` commutes with map. -/
theorem inf_map {X Y : C} (g : Y ⟶ X) [mono g] f₁ f₂ : (map g).obj (f₁⊓f₂) = (map g).obj f₁⊓(map g).obj f₂ :=
  by 
    revert f₁ 
    apply Quotientₓ.ind' 
    intro f₁ 
    erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ←map_comp]
    dsimp 
    rw [pullback_comp, pullback_map_self]

end SemilatticeInfTop

section SemilatticeSup

variable[has_images C][has_binary_coproducts C]

/-- The functorial supremum on `mono_over A` descends to an supremum on `subobject A`. -/
def sup {A : C} : subobject A ⥤ subobject A ⥤ subobject A :=
  thin_skeleton.map₂ mono_over.sup

instance  {B : C} : SemilatticeSup (subobject B) :=
  { subobject.partial_order B with sup := fun m n => (sup.obj m).obj n,
    le_sup_left := fun m n => Quotientₓ.induction_on₂' m n fun a b => ⟨mono_over.le_sup_left _ _⟩,
    le_sup_right := fun m n => Quotientₓ.induction_on₂' m n fun a b => ⟨mono_over.le_sup_right _ _⟩,
    sup_le := fun m n k => Quotientₓ.induction_on₃' m n k fun a b c ⟨i⟩ ⟨j⟩ => ⟨mono_over.sup_le _ _ _ i j⟩ }

theorem sup_factors_of_factors_left {A B : C} {X Y : subobject B} {f : A ⟶ B} (P : X.factors f) : (X⊔Y).Factors f :=
  factors_of_le f le_sup_left P

theorem sup_factors_of_factors_right {A B : C} {X Y : subobject B} {f : A ⟶ B} (P : Y.factors f) : (X⊔Y).Factors f :=
  factors_of_le f le_sup_right P

variable[has_initial C][initial_mono_class C]

instance  {B : C} : SemilatticeSupBot (subobject B) :=
  { subobject.order_bot, subobject.semilattice_sup with  }

theorem finset_sup_factors {I : Type _} {A B : C} {s : Finset I} {P : I → subobject B} {f : A ⟶ B}
  (h : ∃ (i : _)(_ : i ∈ s), (P i).Factors f) : (s.sup P).Factors f :=
  by 
    classical 
    revert h 
    apply Finset.induction_on s
    ·
      rintro ⟨_, ⟨⟨⟩, _⟩⟩
    ·
      rintro i s nm ih ⟨j, ⟨m, h⟩⟩
      simp only [Finset.sup_insert]
      simp  at m 
      rcases m with (rfl | m)
      ·
        exact sup_factors_of_factors_left h
      ·
        exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩)

end SemilatticeSup

section Lattice

variable[has_pullbacks C][has_images C][has_binary_coproducts C]

instance  {B : C} : Lattice (subobject B) :=
  { subobject.semilattice_inf_top, subobject.semilattice_sup with  }

variable[has_initial C][initial_mono_class C]

instance  {B : C} : BoundedLattice (subobject B) :=
  { subobject.semilattice_inf_top, subobject.semilattice_sup_bot with  }

end Lattice

section Inf

variable[well_powered C]

/--
The "wide cospan" diagram, with a small indexing type, constructed from a set of subobjects.
(This is just the diagram of all the subobjects pasted together, but using `well_powered C`
to make the diagram small.)
-/
def wide_cospan {A : C} (s : Set (subobject A)) : wide_pullback_shape (equivShrink _ '' s) ⥤ C :=
  wide_pullback_shape.wide_cospan A (fun j : equivShrink _ '' s => ((equivShrink (subobject A)).symm j : C))
    fun j => ((equivShrink (subobject A)).symm j).arrow

@[simp]
theorem wide_cospan_map_term {A : C} (s : Set (subobject A)) j :
  (wide_cospan s).map (wide_pullback_shape.hom.term j) = ((equivShrink (subobject A)).symm j).arrow :=
  rfl

/-- Auxiliary construction of a cone for `le_Inf`. -/
def le_Inf_cone {A : C} (s : Set (subobject A)) (f : subobject A) (k : ∀ g _ : g ∈ s, f ≤ g) : cone (wide_cospan s) :=
  wide_pullback_shape.mk_cone f.arrow
    (fun j =>
      underlying.map
        (hom_of_le
          (k _
            (by 
              rcases j with ⟨-, ⟨g, ⟨m, rfl⟩⟩⟩
              simpa using m))))
    (by 
      tidy)

@[simp]
theorem le_Inf_cone_π_app_none {A : C} (s : Set (subobject A)) (f : subobject A) (k : ∀ g _ : g ∈ s, f ≤ g) :
  (le_Inf_cone s f k).π.app none = f.arrow :=
  rfl

variable[has_wide_pullbacks C]

/--
The limit of `wide_cospan s`. (This will be the supremum of the set of subobjects.)
-/
def wide_pullback {A : C} (s : Set (subobject A)) : C :=
  limits.limit (wide_cospan s)

/--
The inclusion map from `wide_pullback s` to `A`
-/
def wide_pullback_ι {A : C} (s : Set (subobject A)) : wide_pullback s ⟶ A :=
  limits.limit.π (wide_cospan s) none

instance wide_pullback_ι_mono {A : C} (s : Set (subobject A)) : mono (wide_pullback_ι s) :=
  ⟨fun W u v h =>
      limit.hom_ext
        fun j =>
          by 
            cases j
            ·
              exact h
            ·
              apply (cancel_mono ((equivShrink (subobject A)).symm j).arrow).1
              rw [assoc, assoc]
              erw [limit.w (wide_cospan s) (wide_pullback_shape.hom.term j)]
              exact h⟩

/--
When `[well_powered C]` and `[has_wide_pullbacks C]`, `subobject A` has arbitrary infimums.
-/
def Inf {A : C} (s : Set (subobject A)) : subobject A :=
  subobject.mk (wide_pullback_ι s)

theorem Inf_le {A : C} (s : Set (subobject A)) f (_ : f ∈ s) : Inf s ≤ f :=
  by 
    fapply le_of_comm
    ·
      refine'
        (underlying_iso _).Hom ≫
          limits.limit.π (wide_cospan s) (some ⟨equivShrink _ f, Set.mem_image_of_mem (equivShrink (subobject A)) H⟩) ≫
            _ 
      apply eq_to_hom 
      apply congr_argₓ fun X : subobject A => (X : C)
      exact Equiv.symm_apply_apply _ _
    ·
      dsimp [Inf]
      simp only [category.comp_id, category.assoc, ←underlying_iso_hom_comp_eq_mk, subobject.arrow_congr,
        congr_arg_mpr_hom_left, iso.cancel_iso_hom_left]
      convert limit.w (wide_cospan s) (wide_pullback_shape.hom.term _)

theorem le_Inf {A : C} (s : Set (subobject A)) (f : subobject A) (k : ∀ g _ : g ∈ s, f ≤ g) : f ≤ Inf s :=
  by 
    fapply le_of_comm
    ·
      exact limits.limit.lift _ (le_Inf_cone s f k) ≫ (underlying_iso _).inv
    ·
      dsimp [Inf, wide_pullback_ι]
      simp 

instance  {B : C} : CompleteSemilatticeInf (subobject B) :=
  { subobject.partial_order B with inf := Inf, Inf_le := Inf_le, le_Inf := le_Inf }

end Inf

section Sup

variable[well_powered C][has_coproducts C]

/--
The univesal morphism out of the coproduct of a set of subobjects,
after using `[well_powered C]` to reindex by a small type.
-/
def small_coproduct_desc {A : C} (s : Set (subobject A)) : _ ⟶ A :=
  limits.sigma.desc fun j : equivShrink _ '' s => ((equivShrink (subobject A)).symm j).arrow

variable[has_images C]

/-- When `[well_powered C] [has_images C] [has_coproducts C]`,
`subobject A` has arbitrary supremums. -/
def Sup {A : C} (s : Set (subobject A)) : subobject A :=
  subobject.mk (image.ι (small_coproduct_desc s))

theorem le_Sup {A : C} (s : Set (subobject A)) f (_ : f ∈ s) : f ≤ Sup s :=
  by 
    fapply le_of_comm
    ·
      dsimp [Sup]
      refine' _ ≫ factor_thru_image _ ≫ (underlying_iso _).inv 
      refine'
        _ ≫
          sigma.ι _
            ⟨equivShrink _ f,
              by 
                simpa [Set.mem_image] using H⟩
      exact eq_to_hom (congr_argₓ (fun X : subobject A => (X : C)) (Equiv.symm_apply_apply _ _).symm)
    ·
      dsimp [Sup, small_coproduct_desc]
      simp 
      dsimp 
      simp 

theorem symm_apply_mem_iff_mem_image {α β : Type _} (e : α ≃ β) (s : Set α) (x : β) : e.symm x ∈ s ↔ x ∈ e '' s :=
  ⟨fun h =>
      ⟨e.symm x, h,
        by 
          simp ⟩,
    by 
      rintro ⟨a, m, rfl⟩
      simpa using m⟩

theorem Sup_le {A : C} (s : Set (subobject A)) (f : subobject A) (k : ∀ g _ : g ∈ s, g ≤ f) : Sup s ≤ f :=
  by 
    fapply le_of_comm
    ·
      dsimp [Sup]
      refine' (underlying_iso _).Hom ≫ image.lift ⟨_, f.arrow, _, _⟩
      ·
        refine' sigma.desc _ 
        rintro ⟨g, m⟩
        refine' underlying.map (hom_of_le (k _ _))
        simpa [symm_apply_mem_iff_mem_image] using m
      ·
        ext j 
        rcases j with ⟨j, m⟩
        dsimp [small_coproduct_desc]
        simp 
        dsimp 
        simp 
    ·
      dsimp [Sup]
      simp 

instance  {B : C} : CompleteSemilatticeSup (subobject B) :=
  { subobject.partial_order B with sup := Sup, le_Sup := le_Sup, Sup_le := Sup_le }

end Sup

section CompleteLattice

variable[well_powered C][has_wide_pullbacks C][has_images C][has_coproducts C][initial_mono_class C]

instance  {B : C} : CompleteLattice (subobject B) :=
  { subobject.semilattice_inf_top, subobject.semilattice_sup_bot, subobject.complete_semilattice_Inf,
    subobject.complete_semilattice_Sup with  }

end CompleteLattice

end Subobject

end CategoryTheory

