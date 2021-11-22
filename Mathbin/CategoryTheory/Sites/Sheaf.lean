import Mathbin.CategoryTheory.Sites.SheafOfTypes 
import Mathbin.CategoryTheory.Limits.Yoneda 
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers 
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products 
import Mathbin.CategoryTheory.ConcreteCategory.Default

/-!
# Sheaves taking values in a category

If C is a category with a Grothendieck topology, we define the notion of a sheaf taking values in
an arbitrary category `A`. We follow the definition in https://stacks.math.columbia.edu/tag/00VR,
noting that the presheaf of sets "defined above" can be seen in the comments between tags 00VQ and
00VR on the page https://stacks.math.columbia.edu/tag/00VL. The advantage of this definition is
that we need no assumptions whatsoever on `A` other than the assumption that the morphisms in `C`
and `A` live in the same universe.

* An `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is defined to be a sheaf (for the topology `J`) iff for
  every `X : A`, the type-valued presheaves of sets given by sending `U : Cᵒᵖ` to `Hom_{A}(X, P U)`
  are all sheaves of sets, see `category_theory.presheaf.is_sheaf`.
* When `A = Type`, this recovers the basic definition of sheaves of sets, see
  `category_theory.is_sheaf_iff_is_sheaf_of_type`.
* An alternate definition when `C` is small, has pullbacks and `A` has products is given by an
  equalizer condition `category_theory.presheaf.is_sheaf'`. This is equivalent to the earlier
  definition, shown in `category_theory.presheaf.is_sheaf_iff_is_sheaf'`.
* When `A = Type`, this is *definitionally* equal to the equalizer condition for presieves in
  `category_theory.sites.sheaf_of_types`.
* When `A` has limits and there is a functor `s : A ⥤ Type` which is faithful, reflects isomorphisms
  and preserves limits, then `P : C^op ⥤ A` is a sheaf iff the underlying presheaf of types
  `P ⋙ s : C^op ⥤ Type` is a sheaf (`category_theory.presheaf.is_sheaf_iff_is_sheaf_forget`).
  Cf https://stacks.math.columbia.edu/tag/0073, which is a weaker version of this statement (it's
  only over spaces, not sites) and https://stacks.math.columbia.edu/tag/00YR (a), which
  additionally assumes filtered colimits.
-/


universe w v₁ v₂ u₁ u₂

noncomputable theory

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve Classical

namespace Presheaf

variable{C : Type u₁}[category.{v₁} C]

variable{A : Type u₂}[category.{v₂} A]

variable(J : grothendieck_topology C)

/--
A sheaf of A is a presheaf P : C^op => A such that for every X : A, the
presheaf of types given by sending U : C to Hom_{A}(X, P U) is a sheaf of types.

https://stacks.math.columbia.edu/tag/00VR
-/
def is_sheaf (P : «expr ᵒᵖ» C ⥤ A) : Prop :=
  ∀ X : A, presieve.is_sheaf J (P ⋙ coyoneda.obj (op X))

variable{J}

/-- This is a wrapper around `presieve.is_sheaf_for.amalgamate` to be used below.
  If `P`s a sheaf, `S` is a cover of `X`, and `x` is a collection of morphisms from `E`
  to `P` evaluated at terms in the cover which are compatible, then we can amalgamate
  the `x`s to obtain a single morphism `E ⟶ P.obj (op X)`. -/
def is_sheaf.amalgamate {A : Type u₂} [category.{max v₁ u₁} A] {E : A} {X : C} {P : «expr ᵒᵖ» C ⥤ A}
  (hP : presheaf.is_sheaf J P) (S : J.cover X) (x : ∀ I : S.arrow, E ⟶ P.obj (op I.Y))
  (hx : ∀ I : S.relation, x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) : E ⟶ P.obj (op X) :=
  ((hP _ _ S.condition).amalgamate fun Y f hf => x ⟨Y, f, hf⟩)$
    fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w => hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩

@[simp, reassoc]
theorem is_sheaf.amalgamate_map {A : Type u₂} [category.{max v₁ u₁} A] {E : A} {X : C} {P : «expr ᵒᵖ» C ⥤ A}
  (hP : presheaf.is_sheaf J P) (S : J.cover X) (x : ∀ I : S.arrow, E ⟶ P.obj (op I.Y))
  (hx : ∀ I : S.relation, x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) (I : S.arrow) :
  hP.amalgamate S x hx ≫ P.map I.f.op = x _ :=
  by 
    rcases I with ⟨Y, f, hf⟩
    apply
      @presieve.is_sheaf_for.valid_glue _ _ _ _ _ _ (hP _ _ S.condition) (fun Y f hf => x ⟨Y, f, hf⟩)
        (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w => hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩) f hf

theorem is_sheaf.hom_ext {A : Type u₂} [category.{max v₁ u₁} A] {E : A} {X : C} {P : «expr ᵒᵖ» C ⥤ A}
  (hP : presheaf.is_sheaf J P) (S : J.cover X) (e₁ e₂ : E ⟶ P.obj (op X))
  (h : ∀ I : S.arrow, e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) : e₁ = e₂ :=
  (hP _ _ S.condition).IsSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩

variable(J)

end Presheaf

variable{C : Type u₁}[category.{v₁} C]

variable(J : grothendieck_topology C)

variable(A : Type u₂)[category.{v₂} A]

-- error in CategoryTheory.Sites.Sheaf: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler category
/-- The category of sheaves taking values in `A` on a grothendieck topology. -/
@[derive #[expr category]]
def Sheaf : Type* :=
{P : «expr ⥤ »(«expr ᵒᵖ»(C), A) // presheaf.is_sheaf J P}

-- error in CategoryTheory.Sites.Sheaf: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler full
/-- The inclusion functor from sheaves to presheaves. -/
@[simps #[expr { rhs_md := semireducible }], derive #["[", expr full, ",", expr faithful, "]"]]
def Sheaf_to_presheaf : «expr ⥤ »(Sheaf J A, «expr ⥤ »(«expr ᵒᵖ»(C), A)) :=
full_subcategory_inclusion (presheaf.is_sheaf J)

/-- The sheaf of sections guaranteed by the sheaf condition. -/
@[simps]
abbrev sheaf_over {A : Type u₂} [category.{v₂} A] {J : grothendieck_topology C} (ℱ : Sheaf J A) (X : A) :
  SheafOfTypes J :=
  ⟨ℱ.val ⋙ coyoneda.obj (op X), ℱ.property X⟩

theorem is_sheaf_iff_is_sheaf_of_type (P : «expr ᵒᵖ» C ⥤ Type w) : presheaf.is_sheaf J P ↔ presieve.is_sheaf J P :=
  by 
    split 
    ·
      intro hP 
      refine' presieve.is_sheaf_iso J _ (hP PUnit)
      exact iso_whisker_left _ coyoneda.punit_iso ≪≫ P.right_unitor
    ·
      intro hP X Y S hS z hz 
      refine' ⟨fun x => (hP S hS).amalgamate (fun Z f hf => z f hf x) _, _, _⟩
      ·
        intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h 
        exact congr_funₓ (hz g₁ g₂ hf₁ hf₂ h) x
      ·
        intro Z f hf 
        ext x 
        apply presieve.is_sheaf_for.valid_glue
      ·
        intro y hy 
        ext x 
        apply (hP S hS).IsSeparatedFor.ext 
        intro Y' f hf 
        rw [presieve.is_sheaf_for.valid_glue _ _ _ hf, ←hy _ hf]
        rfl

/--
The category of sheaves taking values in Type is the same as the category of set-valued sheaves.
-/
@[simps]
def Sheaf_equiv_SheafOfTypes : Sheaf J (Type w) ≌ SheafOfTypes J :=
  { Functor := { obj := fun S => ⟨S.1, (is_sheaf_iff_is_sheaf_of_type _ _).1 S.2⟩, map := fun S₁ S₂ f => f },
    inverse := { obj := fun S => ⟨S.1, (is_sheaf_iff_is_sheaf_of_type _ _).2 S.2⟩, map := fun S₁ S₂ f => f },
    unitIso :=
      nat_iso.of_components
        (fun X =>
          ⟨𝟙 _, 𝟙 _,
            by 
              tidy,
            by 
              tidy⟩)
        (by 
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun X =>
          ⟨𝟙 _, 𝟙 _,
            by 
              tidy,
            by 
              tidy⟩)
        (by 
          tidy) }

instance  : Inhabited (Sheaf (⊥ : grothendieck_topology C) (Type w)) :=
  ⟨(Sheaf_equiv_SheafOfTypes _).inverse.obj (default _)⟩

end CategoryTheory

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve Classical

namespace Presheaf

variable{C : Type u₁}[category.{v₁} C]

variable{A : Type u₂}[category.{max v₁ u₁} A]

variable(J : grothendieck_topology C)

variable{U : C}(R : presieve U)

variable(P : «expr ᵒᵖ» C ⥤ A)

section MultiequalizerConditions

/-- When `P` is a sheaf and `S` is a cover, the associated multifork is a limit. -/
def is_limit_of_is_sheaf {X : C} (S : J.cover X) (hP : is_sheaf J P) : is_limit (S.multifork P) :=
  { lift := fun E : multifork _ => hP.amalgamate S (fun I => E.ι _) fun I => E.condition _,
    fac' :=
      by 
        rintro (E : multifork _) (a | b)
        ·
          apply hP.amalgamate_map
        ·
          rw [←E.w (walking_multicospan.hom.fst b), ←(S.multifork P).w (walking_multicospan.hom.fst b), ←category.assoc]
          congr 1
          apply hP.amalgamate_map,
    uniq' :=
      by 
        rintro (E : multifork _) m hm 
        apply hP.hom_ext S 
        intro I 
        erw [hm (walking_multicospan.left I)]
        symm 
        apply hP.amalgamate_map }

theorem is_sheaf_iff_multifork : is_sheaf J P ↔ ∀ X : C S : J.cover X, Nonempty (is_limit (S.multifork P)) :=
  by 
    refine' ⟨fun hP X S => ⟨is_limit_of_is_sheaf _ _ _ hP⟩, _⟩
    intro h E X S hS x hx 
    let T : J.cover X := ⟨S, hS⟩
    obtain ⟨hh⟩ := h _ T 
    let K : multifork (T.index P) := multifork.of_ι _ E (fun I => x I.f I.hf) fun I => hx _ _ _ _ I.w 
    use hh.lift K 
    dsimp 
    split 
    ·
      intro Y f hf 
      apply hh.fac K (walking_multicospan.left ⟨Y, f, hf⟩)
    ·
      intro e he 
      apply hh.uniq K 
      rintro (a | b)
      ·
        apply he
      ·
        rw [←K.w (walking_multicospan.hom.fst b), ←(T.multifork P).w (walking_multicospan.hom.fst b), ←category.assoc]
        congr 1
        apply he

theorem is_sheaf_iff_multiequalizer [∀ X : C S : J.cover X, has_multiequalizer (S.index P)] :
  is_sheaf J P ↔ ∀ X : C S : J.cover X, is_iso (S.to_multiequalizer P) :=
  by 
    rw [is_sheaf_iff_multifork]
    apply forall_congrₓ fun X => _ 
    apply forall_congrₓ fun S => _ 
    split 
    ·
      rintro ⟨h⟩
      let e : P.obj (op X) ≅ multiequalizer (S.index P) := h.cone_point_unique_up_to_iso (limit.is_limit _)
      exact (inferInstance : is_iso e.hom)
    ·
      introI h 
      refine' ⟨is_limit.of_iso_limit (limit.is_limit _) (cones.ext _ _)⟩
      ·
        apply (@as_iso _ _ _ _ _ h).symm
      ·
        intro a 
        symm 
        erw [is_iso.inv_comp_eq]
        change _ = limit.lift _ _ ≫ _ 
        simp 

end MultiequalizerConditions

section 

variable[has_products A]

/--
The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of https://stacks.math.columbia.edu/tag/00VM.
-/
def first_obj : A :=
  ∏ fun f : ΣV, { f : V ⟶ U // R f } => P.obj (op f.1)

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of https://stacks.math.columbia.edu/tag/00VM.
-/
def fork_map : P.obj (op U) ⟶ first_obj R P :=
  pi.lift fun f => P.map f.2.1.op

variable[has_pullbacks C]

/--
The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
def second_obj : A :=
  ∏ fun fg : (ΣV, { f : V ⟶ U // R f }) × ΣW, { g : W ⟶ U // R g } => P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of https://stacks.math.columbia.edu/tag/00VM. -/
def first_map : first_obj R P ⟶ second_obj R P :=
  pi.lift fun fg => pi.π _ _ ≫ P.map pullback.fst.op

/-- The map `pr₁*` of https://stacks.math.columbia.edu/tag/00VM. -/
def second_map : first_obj R P ⟶ second_obj R P :=
  pi.lift fun fg => pi.π _ _ ≫ P.map pullback.snd.op

theorem w : fork_map R P ≫ first_map R P = fork_map R P ≫ second_map R P :=
  by 
    apply limit.hom_ext 
    rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
    simp only [first_map, second_map, fork_map, limit.lift_π, limit.lift_π_assoc, assoc, fan.mk_π_app, Subtype.coe_mk,
      Subtype.val_eq_coe]
    rw [←P.map_comp, ←op_comp, pullback.condition]
    simp 

/--
An alternative definition of the sheaf condition in terms of equalizers. This is shown to be
equivalent in `category_theory.presheaf.is_sheaf_iff_is_sheaf'`.
-/
def is_sheaf' (P : «expr ᵒᵖ» C ⥤ A) : Prop :=
  ∀ U : C R : presieve U hR : generate R ∈ J U, Nonempty (is_limit (fork.of_ι _ (w R P)))

/-- (Implementation). An auxiliary lemma to convert between sheaf conditions. -/
def is_sheaf_for_is_sheaf_for' (P : «expr ᵒᵖ» C ⥤ A) (s : A ⥤ Type max v₁ u₁)
  [∀ J, preserves_limits_of_shape (discrete J) s] (U : C) (R : presieve U) :
  is_limit (s.map_cone (fork.of_ι _ (w R P))) ≃ is_limit (fork.of_ι _ (equalizer.presieve.w (P ⋙ s) R)) :=
  by 
    apply Equiv.trans (is_limit_map_cone_fork_equiv _ _) _ 
    apply (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _)
    ·
      apply nat_iso.of_components _ _
      ·
        rintro (_ | _)
        ·
          apply preserves_product.iso s
        ·
          apply preserves_product.iso s
      ·
        rintro _ _ (_ | _)
        ·
          ext : 1
          dsimp [equalizer.presieve.first_map, first_map]
          simp only [limit.lift_π, map_lift_pi_comparison, assoc, fan.mk_π_app, functor.map_comp]
          erw [pi_comparison_comp_π_assoc]
        ·
          ext : 1
          dsimp [equalizer.presieve.second_map, second_map]
          simp only [limit.lift_π, map_lift_pi_comparison, assoc, fan.mk_π_app, functor.map_comp]
          erw [pi_comparison_comp_π_assoc]
        ·
          dsimp 
          simp 
    ·
      refine' fork.ext (iso.refl _) _ 
      dsimp [equalizer.fork_map, fork_map]
      simp 

/-- The equalizer definition of a sheaf given by `is_sheaf'` is equivalent to `is_sheaf`. -/
theorem is_sheaf_iff_is_sheaf' : is_sheaf J P ↔ is_sheaf' J P :=
  by 
    split 
    ·
      intro h U R hR 
      refine' ⟨_⟩
      apply coyoneda_jointly_reflects_limits 
      intro X 
      have q : presieve.is_sheaf_for (P ⋙ coyoneda.obj X) _ := h X.unop _ hR 
      rw [←presieve.is_sheaf_for_iff_generate] at q 
      rw [equalizer.presieve.sheaf_condition] at q 
      replace q := Classical.choice q 
      apply (is_sheaf_for_is_sheaf_for' _ _ _ _).symm q
    ·
      intro h U X S hS 
      rw [equalizer.presieve.sheaf_condition]
      refine' ⟨_⟩
      refine' is_sheaf_for_is_sheaf_for' _ _ _ _ _ 
      apply is_limit_of_preserves 
      apply Classical.choice (h _ S _)
      simpa

end 

section Concrete

variable[has_pullbacks C]

/--
For a concrete category `(A, s)` where the forgetful functor `s : A ⥤ Type v` preserves limits and
reflects isomorphisms, and `A` has limits, an `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is a sheaf iff its
underlying `Type`-valued presheaf `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf.

Note this lemma applies for "algebraic" categories, eg groups, abelian groups and rings, but not
for the category of topological spaces, topological rings, etc since reflecting isomorphisms doesn't
hold.
-/
theorem is_sheaf_iff_is_sheaf_forget (s : A ⥤ Type max v₁ u₁) [has_limits A] [preserves_limits s]
  [reflects_isomorphisms s] : is_sheaf J P ↔ is_sheaf J (P ⋙ s) :=
  by 
    rw [is_sheaf_iff_is_sheaf', is_sheaf_iff_is_sheaf']
    apply forall_congrₓ fun U => _ 
    apply ball_congr fun R hR => _ 
    letI this : reflects_limits s := reflects_limits_of_reflects_isomorphisms 
    have  : is_limit (s.map_cone (fork.of_ι _ (w R P))) ≃ is_limit (fork.of_ι _ (w R (P ⋙ s))) :=
      is_sheaf_for_is_sheaf_for' P s U R 
    rw [←Equiv.nonempty_congr this]
    split 
    ·
      exact Nonempty.map fun t => is_limit_of_preserves s t
    ·
      exact Nonempty.map fun t => is_limit_of_reflects s t

end Concrete

end Presheaf

end CategoryTheory

