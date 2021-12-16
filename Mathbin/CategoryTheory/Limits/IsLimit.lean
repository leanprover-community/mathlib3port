import Mathbin.CategoryTheory.Adjunction.Basic 
import Mathbin.CategoryTheory.Limits.Cones 
import Mathbin.CategoryTheory.ReflectsIsomorphisms

/-!
# Limits and colimits

We set up the general theory of limits and colimits in a category.
In this introduction we only describe the setup for limits;
it is repeated, with slightly different names, for colimits.

The main structures defined in this file is
* `is_limit c`, for `c : cone F`, `F : J ⥤ C`, expressing that `c` is a limit cone,

See also `category_theory.limits.limits` which further builds:
* `limit_cone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `has_limit F`, asserting the mere existence of some limit cone for `F`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/


noncomputable section 

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [category.{v₁} J] {K : Type u₂} [category.{v₂} K]

variable {C : Type u₃} [category.{v₃} C]

variable {F : J ⥤ C}

/--
A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
cone morphism to `t`.

See https://stacks.math.columbia.edu/tag/002E.
  -/
@[nolint has_inhabited_instance]
structure is_limit (t : cone F) where 
  lift : ∀ s : cone F, s.X ⟶ t.X 
  fac' : ∀ s : cone F j : J, lift s ≫ t.π.app j = s.π.app j :=  by 
  runTac 
    obviously 
  uniq' : ∀ s : cone F m : s.X ⟶ t.X w : ∀ j : J, m ≫ t.π.app j = s.π.app j, m = lift s :=  by 
  runTac 
    obviously

restate_axiom is_limit.fac'

attribute [simp, reassoc] is_limit.fac

restate_axiom is_limit.uniq'

namespace IsLimit

-- failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
-- failed to format: no declaration of attribute [formatter] found for 'Lean.Meta.solveByElim'
instance
  Subsingleton
  { t : cone F } : Subsingleton is_limit t
  := ⟨ by intro P Q <;> cases P <;> cases Q <;> congr <;> ext <;> solveByElim ⟩

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cone point
of any cone over `F` to the cone point of a limit cone over `G`. -/
def map {F G : J ⥤ C} (s : cone F) {t : cone G} (P : is_limit t) (α : F ⟶ G) : s.X ⟶ t.X :=
  P.lift ((cones.postcompose α).obj s)

@[simp, reassoc]
theorem map_π {F G : J ⥤ C} (c : cone F) {d : cone G} (hd : is_limit d) (α : F ⟶ G) (j : J) :
  hd.map c α ≫ d.π.app j = c.π.app j ≫ α.app j :=
  fac _ _ _

theorem lift_self {c : cone F} (t : is_limit c) : t.lift c = 𝟙 c.X :=
  (t.uniq _ _ fun j => id_comp _).symm

/-- The universal morphism from any other cone to a limit cone. -/
@[simps]
def lift_cone_morphism {t : cone F} (h : is_limit t) (s : cone F) : s ⟶ t :=
  { Hom := h.lift s }

theorem uniq_cone_morphism {s t : cone F} (h : is_limit t) {f f' : s ⟶ t} : f = f' :=
  have  : ∀ {g : s ⟶ t}, g = h.lift_cone_morphism s :=
    by 
      intro g <;> ext <;> exact h.uniq _ _ g.w 
  this.trans this.symm

/--
Alternative constructor for `is_limit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
@[simps]
def mk_cone_morphism {t : cone F} (lift : ∀ s : cone F, s ⟶ t) (uniq' : ∀ s : cone F m : s ⟶ t, m = lift s) :
  is_limit t :=
  { lift := fun s => (lift s).Hom,
    uniq' :=
      fun s m w =>
        have  : cone_morphism.mk m w = lift s :=
          by 
            apply uniq' 
        congr_argₓ cone_morphism.hom this }

/-- Limit cones on `F` are unique up to isomorphism. -/
@[simps]
def unique_up_to_iso {s t : cone F} (P : is_limit s) (Q : is_limit t) : s ≅ t :=
  { Hom := Q.lift_cone_morphism s, inv := P.lift_cone_morphism t, hom_inv_id' := P.uniq_cone_morphism,
    inv_hom_id' := Q.uniq_cone_morphism }

/-- Any cone morphism between limit cones is an isomorphism. -/
theorem hom_is_iso {s t : cone F} (P : is_limit s) (Q : is_limit t) (f : s ⟶ t) : is_iso f :=
  ⟨⟨P.lift_cone_morphism t, ⟨P.uniq_cone_morphism, Q.uniq_cone_morphism⟩⟩⟩

/-- Limits of `F` are unique up to isomorphism. -/
def cone_point_unique_up_to_iso {s t : cone F} (P : is_limit s) (Q : is_limit t) : s.X ≅ t.X :=
  (cones.forget F).mapIso (unique_up_to_iso P Q)

@[simp, reassoc]
theorem cone_point_unique_up_to_iso_hom_comp {s t : cone F} (P : is_limit s) (Q : is_limit t) (j : J) :
  (cone_point_unique_up_to_iso P Q).Hom ≫ t.π.app j = s.π.app j :=
  (unique_up_to_iso P Q).Hom.w _

@[simp, reassoc]
theorem cone_point_unique_up_to_iso_inv_comp {s t : cone F} (P : is_limit s) (Q : is_limit t) (j : J) :
  (cone_point_unique_up_to_iso P Q).inv ≫ s.π.app j = t.π.app j :=
  (unique_up_to_iso P Q).inv.w _

@[simp, reassoc]
theorem lift_comp_cone_point_unique_up_to_iso_hom {r s t : cone F} (P : is_limit s) (Q : is_limit t) :
  P.lift r ≫ (cone_point_unique_up_to_iso P Q).Hom = Q.lift r :=
  Q.uniq _ _
    (by 
      simp )

@[simp, reassoc]
theorem lift_comp_cone_point_unique_up_to_iso_inv {r s t : cone F} (P : is_limit s) (Q : is_limit t) :
  Q.lift r ≫ (cone_point_unique_up_to_iso P Q).inv = P.lift r :=
  P.uniq _ _
    (by 
      simp )

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
def of_iso_limit {r t : cone F} (P : is_limit r) (i : r ≅ t) : is_limit t :=
  is_limit.mk_cone_morphism (fun s => P.lift_cone_morphism s ≫ i.hom)
    fun s m =>
      by 
        rw [←i.comp_inv_eq] <;> apply P.uniq_cone_morphism

@[simp]
theorem of_iso_limit_lift {r t : cone F} (P : is_limit r) (i : r ≅ t) s :
  (P.of_iso_limit i).lift s = P.lift s ≫ i.hom.hom :=
  rfl

/-- Isomorphism of cones preserves whether or not they are limiting cones. -/
def equiv_iso_limit {r t : cone F} (i : r ≅ t) : is_limit r ≃ is_limit t :=
  { toFun := fun h => h.of_iso_limit i, invFun := fun h => h.of_iso_limit i.symm,
    left_inv :=
      by 
        tidy,
    right_inv :=
      by 
        tidy }

@[simp]
theorem equiv_iso_limit_apply {r t : cone F} (i : r ≅ t) (P : is_limit r) : equiv_iso_limit i P = P.of_iso_limit i :=
  rfl

@[simp]
theorem equiv_iso_limit_symm_apply {r t : cone F} (i : r ≅ t) (P : is_limit t) :
  (equiv_iso_limit i).symm P = P.of_iso_limit i.symm :=
  rfl

/--
If the canonical morphism from a cone point to a limiting cone point is an iso, then the
first cone was limiting also.
-/
def of_point_iso {r t : cone F} (P : is_limit r) [i : is_iso (P.lift t)] : is_limit t :=
  of_iso_limit P
    (by 
      have  : is_iso (P.lift_cone_morphism t).Hom := i 
      have  : is_iso (P.lift_cone_morphism t) := cones.cone_iso_of_hom_iso _ 
      symm 
      apply as_iso (P.lift_cone_morphism t))

variable {t : cone F}

theorem hom_lift (h : is_limit t) {W : C} (m : W ⟶ t.X) :
  m = h.lift { x := W, π := { app := fun b => m ≫ t.π.app b } } :=
  h.uniq { x := W, π := { app := fun b => m ≫ t.π.app b } } m fun b => rfl

/-- Two morphisms into a limit are equal if their compositions with
  each cone morphism are equal. -/
theorem hom_ext (h : is_limit t) {W : C} {f f' : W ⟶ t.X} (w : ∀ j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f' :=
  by 
    rw [h.hom_lift f, h.hom_lift f'] <;> congr <;> exact funext w

/--
Given a right adjoint functor between categories of cones,
the image of a limit cone is a limit cone.
-/
def of_right_adjoint {D : Type u₄} [category.{v₄} D] {G : K ⥤ D} (h : cone G ⥤ cone F) [is_right_adjoint h] {c : cone G}
  (t : is_limit c) : is_limit (h.obj c) :=
  mk_cone_morphism (fun s => (adjunction.of_right_adjoint h).homEquiv s c (t.lift_cone_morphism _))
    fun s m => (adjunction.eq_hom_equiv_apply _ _ _).2 t.uniq_cone_morphism

/--
Given two functors which have equivalent categories of cones, we can transport a limiting cone
across the equivalence.
-/
def of_cone_equiv {D : Type u₄} [category.{v₄} D] {G : K ⥤ D} (h : cone G ≌ cone F) {c : cone G} :
  is_limit (h.functor.obj c) ≃ is_limit c :=
  { toFun := fun P => of_iso_limit (of_right_adjoint h.inverse P) (h.unit_iso.symm.app c),
    invFun := of_right_adjoint h.functor,
    left_inv :=
      by 
        tidy,
    right_inv :=
      by 
        tidy }

@[simp]
theorem of_cone_equiv_apply_desc {D : Type u₄} [category.{v₄} D] {G : K ⥤ D} (h : cone G ≌ cone F) {c : cone G}
  (P : is_limit (h.functor.obj c)) s :
  (of_cone_equiv h P).lift s =
    ((h.unit_iso.hom.app s).Hom ≫ (h.functor.inv.map (P.lift_cone_morphism (h.functor.obj s))).Hom) ≫
      (h.unit_iso.inv.app c).Hom :=
  rfl

@[simp]
theorem of_cone_equiv_symm_apply_desc {D : Type u₄} [category.{v₄} D] {G : K ⥤ D} (h : cone G ≌ cone F) {c : cone G}
  (P : is_limit c) s :
  ((of_cone_equiv h).symm P).lift s =
    (h.counit_iso.inv.app s).Hom ≫ (h.functor.map (P.lift_cone_morphism (h.inverse.obj s))).Hom :=
  rfl

/--
A cone postcomposed with a natural isomorphism is a limit cone if and only if the original cone is.
-/
def postcompose_hom_equiv {F G : J ⥤ C} (α : F ≅ G) (c : cone F) :
  is_limit ((cones.postcompose α.hom).obj c) ≃ is_limit c :=
  of_cone_equiv (cones.postcompose_equivalence α)

/--
A cone postcomposed with the inverse of a natural isomorphism is a limit cone if and only if
the original cone is.
-/
def postcompose_inv_equiv {F G : J ⥤ C} (α : F ≅ G) (c : cone G) :
  is_limit ((cones.postcompose α.inv).obj c) ≃ is_limit c :=
  postcompose_hom_equiv α.symm c

/--
The cone points of two limit cones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simps]
def cone_points_iso_of_nat_iso {F G : J ⥤ C} {s : cone F} {t : cone G} (P : is_limit s) (Q : is_limit t) (w : F ≅ G) :
  s.X ≅ t.X :=
  { Hom := Q.map s w.hom, inv := P.map t w.inv,
    hom_inv_id' :=
      P.hom_ext
        (by 
          tidy),
    inv_hom_id' :=
      Q.hom_ext
        (by 
          tidy) }

@[reassoc]
theorem cone_points_iso_of_nat_iso_hom_comp {F G : J ⥤ C} {s : cone F} {t : cone G} (P : is_limit s) (Q : is_limit t)
  (w : F ≅ G) (j : J) : (cone_points_iso_of_nat_iso P Q w).Hom ≫ t.π.app j = s.π.app j ≫ w.hom.app j :=
  by 
    simp 

@[reassoc]
theorem cone_points_iso_of_nat_iso_inv_comp {F G : J ⥤ C} {s : cone F} {t : cone G} (P : is_limit s) (Q : is_limit t)
  (w : F ≅ G) (j : J) : (cone_points_iso_of_nat_iso P Q w).inv ≫ s.π.app j = t.π.app j ≫ w.inv.app j :=
  by 
    simp 

@[reassoc]
theorem lift_comp_cone_points_iso_of_nat_iso_hom {F G : J ⥤ C} {r s : cone F} {t : cone G} (P : is_limit s)
  (Q : is_limit t) (w : F ≅ G) : P.lift r ≫ (cone_points_iso_of_nat_iso P Q w).Hom = Q.map r w.hom :=
  Q.hom_ext
    (by 
      simp )

section Equivalenceₓ

open CategoryTheory.Equivalence

/--
If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whisker_equivalence {s : cone F} (P : is_limit s) (e : K ≌ J) : is_limit (s.whisker e.functor) :=
  of_right_adjoint (cones.whiskering_equivalence e).Functor P

/--
We can prove two cone points `(s : cone F).X` and `(t.cone F).X` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simps]
def cone_points_iso_of_equivalence {F : J ⥤ C} {s : cone F} {G : K ⥤ C} {t : cone G} (P : is_limit s) (Q : is_limit t)
  (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : s.X ≅ t.X :=
  let w' : e.inverse ⋙ F ≅ G := (iso_whisker_left e.inverse w).symm ≪≫ inv_fun_id_assoc e G
  { Hom := Q.lift ((cones.equivalence_of_reindexing e.symm w').Functor.obj s),
    inv := P.lift ((cones.equivalence_of_reindexing e w).Functor.obj t),
    hom_inv_id' :=
      by 
        apply hom_ext P 
        intro j 
        dsimp 
        simp only [limits.cone.whisker_π, limits.cones.postcompose_obj_π, fac, whisker_left_app, assoc, id_comp,
          inv_fun_id_assoc_hom_app, fac_assoc, nat_trans.comp_app]
        rw [counit_app_functor, ←functor.comp_map, w.hom.naturality]
        simp ,
    inv_hom_id' :=
      by 
        apply hom_ext Q 
        tidy }

end Equivalenceₓ

/-- The universal property of a limit cone: a map `W ⟶ X` is the same as
  a cone on `F` with vertex `W`. -/
def hom_iso (h : is_limit t) (W : C) : Ulift.{u₁} (W ⟶ t.X : Type v₃) ≅ (const J).obj W ⟶ F :=
  { Hom := fun f => (t.extend f.down).π, inv := fun π => ⟨h.lift { x := W, π }⟩,
    hom_inv_id' :=
      by 
        ext f <;> apply h.hom_ext <;> intro j <;> simp  <;> dsimp <;> rfl }

@[simp]
theorem hom_iso_hom (h : is_limit t) {W : C} (f : Ulift.{u₁} (W ⟶ t.X)) :
  (is_limit.hom_iso h W).Hom f = (t.extend f.down).π :=
  rfl

/-- The limit of `F` represents the functor taking `W` to
  the set of cones on `F` with vertex `W`. -/
def nat_iso (h : is_limit t) : yoneda.obj t.X ⋙ ulift_functor.{u₁} ≅ F.cones :=
  nat_iso.of_components (fun W => is_limit.hom_iso h (unop W))
    (by 
      tidy)

/--
Another, more explicit, formulation of the universal property of a limit cone.
See also `hom_iso`.
-/
def hom_iso' (h : is_limit t) (W : C) :
  Ulift.{u₁} (W ⟶ t.X : Type v₃) ≅ { p : ∀ j, W ⟶ F.obj j // ∀ {j j'} f : j ⟶ j', p j ≫ F.map f = p j' } :=
  h.hom_iso W ≪≫
    { Hom :=
        fun π =>
          ⟨fun j => π.app j,
            fun j j' f =>
              by 
                convert ← (π.naturality f).symm <;> apply id_comp⟩,
      inv :=
        fun p =>
          { app := fun j => p.1 j,
            naturality' :=
              fun j j' f =>
                by 
                  dsimp 
                  rw [id_comp]
                  exact (p.2 f).symm } }

/-- If G : C → D is a faithful functor which sends t to a limit cone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def of_faithful {t : cone F} {D : Type u₄} [category.{v₄} D] (G : C ⥤ D) [faithful G] (ht : is_limit (G.map_cone t))
  (lift : ∀ s : cone F, s.X ⟶ t.X) (h : ∀ s, G.map (lift s) = ht.lift (G.map_cone s)) : is_limit t :=
  { lift,
    fac' :=
      fun s j =>
        by 
          apply G.map_injective <;> rw [G.map_comp, h] <;> apply ht.fac,
    uniq' :=
      fun s m w =>
        by 
          apply G.map_injective 
          rw [h]
          refine' ht.uniq (G.map_cone s) _ fun j => _ 
          convert ← congr_argₓ (fun f => G.map f) (w j)
          apply G.map_comp }

/--
If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a limit implies
`G.map_cone c` is also a limit.
-/
def map_cone_equiv {D : Type u₄} [category.{v₄} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : cone K}
  (t : is_limit (F.map_cone c)) : is_limit (G.map_cone c) :=
  by 
    apply postcompose_inv_equiv (iso_whisker_left K h : _) (G.map_cone c) _ 
    apply t.of_iso_limit (postcompose_whisker_left_map_cone h.symm c).symm

/--
A cone is a limit cone exactly if
there is a unique cone morphism from any other cone.
-/
def iso_unique_cone_morphism {t : cone F} : is_limit t ≅ ∀ s, Unique (s ⟶ t) :=
  { Hom := fun h s => { default := h.lift_cone_morphism s, uniq := fun _ => h.uniq_cone_morphism },
    inv :=
      fun h =>
        { lift := fun s => (h s).default.Hom, uniq' := fun s f w => congr_argₓ cone_morphism.hom ((h s).uniq ⟨f, w⟩) } }

namespace OfNatIso

variable {X : C} (h : yoneda.obj X ⋙ ulift_functor.{u₁} ≅ F.cones)

/-- If `F.cones` is represented by `X`, each morphism `f : Y ⟶ X` gives a cone with cone point
`Y`. -/
def cone_of_hom {Y : C} (f : Y ⟶ X) : cone F :=
  { x := Y, π := h.hom.app (op Y) ⟨f⟩ }

/-- If `F.cones` is represented by `X`, each cone `s` gives a morphism `s.X ⟶ X`. -/
def hom_of_cone (s : cone F) : s.X ⟶ X :=
  (h.inv.app (op s.X) s.π).down

@[simp]
theorem cone_of_hom_of_cone (s : cone F) : cone_of_hom h (hom_of_cone h s) = s :=
  by 
    dsimp [cone_of_hom, hom_of_cone]
    cases s 
    congr 
    dsimp 
    convert congr_funₓ (congr_funₓ (congr_argₓ nat_trans.app h.inv_hom_id) (op s_X)) s_π 
    exact Ulift.up_down _

@[simp]
theorem hom_of_cone_of_hom {Y : C} (f : Y ⟶ X) : hom_of_cone h (cone_of_hom h f) = f :=
  congr_argₓ Ulift.down (congr_funₓ (congr_funₓ (congr_argₓ nat_trans.app h.hom_inv_id) (op Y)) ⟨f⟩ : _)

/-- If `F.cones` is represented by `X`, the cone corresponding to the identity morphism on `X`
will be a limit cone. -/
def limit_cone : cone F :=
  cone_of_hom h (𝟙 X)

/-- If `F.cones` is represented by `X`, the cone corresponding to a morphism `f : Y ⟶ X` is
the limit cone extended by `f`. -/
theorem cone_of_hom_fac {Y : C} (f : Y ⟶ X) : cone_of_hom h f = (limit_cone h).extend f :=
  by 
    dsimp [cone_of_hom, limit_cone, cone.extend]
    congr with j 
    have t := congr_funₓ (h.hom.naturality f.op) ⟨𝟙 X⟩
    dsimp  at t 
    simp only [comp_id] at t 
    rw [congr_funₓ (congr_argₓ nat_trans.app t) j]
    rfl

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
    If `F.cones` is represented by `X`, any cone is the extension of the limit cone by the
    corresponding morphism. -/
  theorem
    cone_fac
    ( s : cone F ) : limit_cone h . extend hom_of_cone h s = s
    := by rw [ ← cone_of_hom_of_cone h s ] convLHS => simp only [ hom_of_cone_of_hom ] apply cone_of_hom_fac _ _ . symm

end OfNatIso

section 

open OfNatIso

/--
If `F.cones` is representable, then the cone corresponding to the identity morphism on
the representing object is a limit cone.
-/
def of_nat_iso {X : C} (h : yoneda.obj X ⋙ ulift_functor.{u₁} ≅ F.cones) : is_limit (limit_cone h) :=
  { lift := fun s => hom_of_cone h s,
    fac' :=
      fun s j =>
        by 
          have h := cone_fac h s 
          cases s 
          injection h with h₁ h₂ 
          simp only [heq_iff_eq] at h₂ 
          convRHS => rw [←h₂]
          rfl,
    uniq' :=
      fun s m w =>
        by 
          rw [←hom_of_cone_of_hom h m]
          congr 
          rw [cone_of_hom_fac]
          dsimp [cone.extend]
          cases s 
          congr with j 
          exact w j }

end 

end IsLimit

/--
A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
cocone morphism from `t`.

See https://stacks.math.columbia.edu/tag/002F.
-/
@[nolint has_inhabited_instance]
structure is_colimit (t : cocone F) where 
  desc : ∀ s : cocone F, t.X ⟶ s.X 
  fac' : ∀ s : cocone F j : J, t.ι.app j ≫ desc s = s.ι.app j :=  by 
  runTac 
    obviously 
  uniq' : ∀ s : cocone F m : t.X ⟶ s.X w : ∀ j : J, t.ι.app j ≫ m = s.ι.app j, m = desc s :=  by 
  runTac 
    obviously

restate_axiom is_colimit.fac'

attribute [simp, reassoc] is_colimit.fac

restate_axiom is_colimit.uniq'

namespace IsColimit

-- failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
-- failed to format: no declaration of attribute [formatter] found for 'Lean.Meta.solveByElim'
instance
  Subsingleton
  { t : cocone F } : Subsingleton is_colimit t
  := ⟨ by intro P Q <;> cases P <;> cases Q <;> congr <;> ext <;> solveByElim ⟩

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cocone point
of a colimit cocone over `F` to the cocone point of any cocone over `G`. -/
def map {F G : J ⥤ C} {s : cocone F} (P : is_colimit s) (t : cocone G) (α : F ⟶ G) : s.X ⟶ t.X :=
  P.desc ((cocones.precompose α).obj t)

@[simp, reassoc]
theorem ι_map {F G : J ⥤ C} {c : cocone F} (hc : is_colimit c) (d : cocone G) (α : F ⟶ G) (j : J) :
  c.ι.app j ≫ is_colimit.map hc d α = α.app j ≫ d.ι.app j :=
  fac _ _ _

@[simp]
theorem desc_self {t : cocone F} (h : is_colimit t) : h.desc t = 𝟙 t.X :=
  (h.uniq _ _ fun j => comp_id _).symm

/-- The universal morphism from a colimit cocone to any other cocone. -/
@[simps]
def desc_cocone_morphism {t : cocone F} (h : is_colimit t) (s : cocone F) : t ⟶ s :=
  { Hom := h.desc s }

theorem uniq_cocone_morphism {s t : cocone F} (h : is_colimit t) {f f' : t ⟶ s} : f = f' :=
  have  : ∀ {g : t ⟶ s}, g = h.desc_cocone_morphism s :=
    by 
      intro g <;> ext <;> exact h.uniq _ _ g.w 
  this.trans this.symm

/--
Alternative constructor for `is_colimit`,
providing a morphism of cocones rather than a morphism between the cocone points
and separately the factorisation condition.
-/
@[simps]
def mk_cocone_morphism {t : cocone F} (desc : ∀ s : cocone F, t ⟶ s) (uniq' : ∀ s : cocone F m : t ⟶ s, m = desc s) :
  is_colimit t :=
  { desc := fun s => (desc s).Hom,
    uniq' :=
      fun s m w =>
        have  : cocone_morphism.mk m w = desc s :=
          by 
            apply uniq' 
        congr_argₓ cocone_morphism.hom this }

/-- Colimit cocones on `F` are unique up to isomorphism. -/
@[simps]
def unique_up_to_iso {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) : s ≅ t :=
  { Hom := P.desc_cocone_morphism t, inv := Q.desc_cocone_morphism s, hom_inv_id' := P.uniq_cocone_morphism,
    inv_hom_id' := Q.uniq_cocone_morphism }

/-- Any cocone morphism between colimit cocones is an isomorphism. -/
theorem hom_is_iso {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) (f : s ⟶ t) : is_iso f :=
  ⟨⟨Q.desc_cocone_morphism s, ⟨P.uniq_cocone_morphism, Q.uniq_cocone_morphism⟩⟩⟩

/-- Colimits of `F` are unique up to isomorphism. -/
def cocone_point_unique_up_to_iso {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) : s.X ≅ t.X :=
  (cocones.forget F).mapIso (unique_up_to_iso P Q)

@[simp, reassoc]
theorem comp_cocone_point_unique_up_to_iso_hom {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) (j : J) :
  s.ι.app j ≫ (cocone_point_unique_up_to_iso P Q).Hom = t.ι.app j :=
  (unique_up_to_iso P Q).Hom.w _

@[simp, reassoc]
theorem comp_cocone_point_unique_up_to_iso_inv {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) (j : J) :
  t.ι.app j ≫ (cocone_point_unique_up_to_iso P Q).inv = s.ι.app j :=
  (unique_up_to_iso P Q).inv.w _

@[simp, reassoc]
theorem cocone_point_unique_up_to_iso_hom_desc {r s t : cocone F} (P : is_colimit s) (Q : is_colimit t) :
  (cocone_point_unique_up_to_iso P Q).Hom ≫ Q.desc r = P.desc r :=
  P.uniq _ _
    (by 
      simp )

@[simp, reassoc]
theorem cocone_point_unique_up_to_iso_inv_desc {r s t : cocone F} (P : is_colimit s) (Q : is_colimit t) :
  (cocone_point_unique_up_to_iso P Q).inv ≫ P.desc r = Q.desc r :=
  Q.uniq _ _
    (by 
      simp )

/-- Transport evidence that a cocone is a colimit cocone across an isomorphism of cocones. -/
def of_iso_colimit {r t : cocone F} (P : is_colimit r) (i : r ≅ t) : is_colimit t :=
  is_colimit.mk_cocone_morphism (fun s => i.inv ≫ P.desc_cocone_morphism s)
    fun s m =>
      by 
        rw [i.eq_inv_comp] <;> apply P.uniq_cocone_morphism

@[simp]
theorem of_iso_colimit_desc {r t : cocone F} (P : is_colimit r) (i : r ≅ t) s :
  (P.of_iso_colimit i).desc s = i.inv.hom ≫ P.desc s :=
  rfl

/-- Isomorphism of cocones preserves whether or not they are colimiting cocones. -/
def equiv_iso_colimit {r t : cocone F} (i : r ≅ t) : is_colimit r ≃ is_colimit t :=
  { toFun := fun h => h.of_iso_colimit i, invFun := fun h => h.of_iso_colimit i.symm,
    left_inv :=
      by 
        tidy,
    right_inv :=
      by 
        tidy }

@[simp]
theorem equiv_iso_colimit_apply {r t : cocone F} (i : r ≅ t) (P : is_colimit r) :
  equiv_iso_colimit i P = P.of_iso_colimit i :=
  rfl

@[simp]
theorem equiv_iso_colimit_symm_apply {r t : cocone F} (i : r ≅ t) (P : is_colimit t) :
  (equiv_iso_colimit i).symm P = P.of_iso_colimit i.symm :=
  rfl

/--
If the canonical morphism to a cocone point from a colimiting cocone point is an iso, then the
first cocone was colimiting also.
-/
def of_point_iso {r t : cocone F} (P : is_colimit r) [i : is_iso (P.desc t)] : is_colimit t :=
  of_iso_colimit P
    (by 
      have  : is_iso (P.desc_cocone_morphism t).Hom := i 
      have  : is_iso (P.desc_cocone_morphism t) := cocones.cocone_iso_of_hom_iso _ 
      apply as_iso (P.desc_cocone_morphism t))

variable {t : cocone F}

theorem hom_desc (h : is_colimit t) {W : C} (m : t.X ⟶ W) :
  m =
    h.desc
      { x := W,
        ι :=
          { app := fun b => t.ι.app b ≫ m,
            naturality' :=
              by 
                intros  <;> erw [←assoc, t.ι.naturality, comp_id, comp_id] } } :=
  h.uniq { x := W, ι := { app := fun b => t.ι.app b ≫ m, naturality' := _ } } m fun b => rfl

/-- Two morphisms out of a colimit are equal if their compositions with
  each cocone morphism are equal. -/
theorem hom_ext (h : is_colimit t) {W : C} {f f' : t.X ⟶ W} (w : ∀ j, t.ι.app j ≫ f = t.ι.app j ≫ f') : f = f' :=
  by 
    rw [h.hom_desc f, h.hom_desc f'] <;> congr <;> exact funext w

/--
Given a left adjoint functor between categories of cocones,
the image of a colimit cocone is a colimit cocone.
-/
def of_left_adjoint {D : Type u₄} [category.{v₄} D] {G : K ⥤ D} (h : cocone G ⥤ cocone F) [is_left_adjoint h]
  {c : cocone G} (t : is_colimit c) : is_colimit (h.obj c) :=
  mk_cocone_morphism (fun s => ((adjunction.of_left_adjoint h).homEquiv c s).symm (t.desc_cocone_morphism _))
    fun s m => (adjunction.hom_equiv_apply_eq _ _ _).1 t.uniq_cocone_morphism

/--
Given two functors which have equivalent categories of cocones,
we can transport a colimiting cocone across the equivalence.
-/
def of_cocone_equiv {D : Type u₄} [category.{v₄} D] {G : K ⥤ D} (h : cocone G ≌ cocone F) {c : cocone G} :
  is_colimit (h.functor.obj c) ≃ is_colimit c :=
  { toFun := fun P => of_iso_colimit (of_left_adjoint h.inverse P) (h.unit_iso.symm.app c),
    invFun := of_left_adjoint h.functor,
    left_inv :=
      by 
        tidy,
    right_inv :=
      by 
        tidy }

@[simp]
theorem of_cocone_equiv_apply_desc {D : Type u₄} [category.{v₄} D] {G : K ⥤ D} (h : cocone G ≌ cocone F) {c : cocone G}
  (P : is_colimit (h.functor.obj c)) s :
  (of_cocone_equiv h P).desc s =
    (h.unit.app c).Hom ≫ (h.inverse.map (P.desc_cocone_morphism (h.functor.obj s))).Hom ≫ (h.unit_inv.app s).Hom :=
  rfl

@[simp]
theorem of_cocone_equiv_symm_apply_desc {D : Type u₄} [category.{v₄} D] {G : K ⥤ D} (h : cocone G ≌ cocone F)
  {c : cocone G} (P : is_colimit c) s :
  ((of_cocone_equiv h).symm P).desc s =
    (h.functor.map (P.desc_cocone_morphism (h.inverse.obj s))).Hom ≫ (h.counit.app s).Hom :=
  rfl

/--
A cocone precomposed with a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/
def precompose_hom_equiv {F G : J ⥤ C} (α : F ≅ G) (c : cocone G) :
  is_colimit ((cocones.precompose α.hom).obj c) ≃ is_colimit c :=
  of_cocone_equiv (cocones.precompose_equivalence α)

/--
A cocone precomposed with the inverse of a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/
def precompose_inv_equiv {F G : J ⥤ C} (α : F ≅ G) (c : cocone F) :
  is_colimit ((cocones.precompose α.inv).obj c) ≃ is_colimit c :=
  precompose_hom_equiv α.symm c

/--
The cocone points of two colimit cocones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simps]
def cocone_points_iso_of_nat_iso {F G : J ⥤ C} {s : cocone F} {t : cocone G} (P : is_colimit s) (Q : is_colimit t)
  (w : F ≅ G) : s.X ≅ t.X :=
  { Hom := P.map t w.hom, inv := Q.map s w.inv,
    hom_inv_id' :=
      P.hom_ext
        (by 
          tidy),
    inv_hom_id' :=
      Q.hom_ext
        (by 
          tidy) }

@[reassoc]
theorem comp_cocone_points_iso_of_nat_iso_hom {F G : J ⥤ C} {s : cocone F} {t : cocone G} (P : is_colimit s)
  (Q : is_colimit t) (w : F ≅ G) (j : J) :
  s.ι.app j ≫ (cocone_points_iso_of_nat_iso P Q w).Hom = w.hom.app j ≫ t.ι.app j :=
  by 
    simp 

@[reassoc]
theorem comp_cocone_points_iso_of_nat_iso_inv {F G : J ⥤ C} {s : cocone F} {t : cocone G} (P : is_colimit s)
  (Q : is_colimit t) (w : F ≅ G) (j : J) :
  t.ι.app j ≫ (cocone_points_iso_of_nat_iso P Q w).inv = w.inv.app j ≫ s.ι.app j :=
  by 
    simp 

@[reassoc]
theorem cocone_points_iso_of_nat_iso_hom_desc {F G : J ⥤ C} {s : cocone F} {r t : cocone G} (P : is_colimit s)
  (Q : is_colimit t) (w : F ≅ G) : (cocone_points_iso_of_nat_iso P Q w).Hom ≫ Q.desc r = P.map _ w.hom :=
  P.hom_ext
    (by 
      simp )

section Equivalenceₓ

open CategoryTheory.Equivalence

/--
If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whisker_equivalence {s : cocone F} (P : is_colimit s) (e : K ≌ J) : is_colimit (s.whisker e.functor) :=
  of_left_adjoint (cocones.whiskering_equivalence e).Functor P

/--
We can prove two cocone points `(s : cocone F).X` and `(t.cocone F).X` are isomorphic if
* both cocones are colimit ccoones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cocone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simps]
def cocone_points_iso_of_equivalence {F : J ⥤ C} {s : cocone F} {G : K ⥤ C} {t : cocone G} (P : is_colimit s)
  (Q : is_colimit t) (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : s.X ≅ t.X :=
  let w' : e.inverse ⋙ F ≅ G := (iso_whisker_left e.inverse w).symm ≪≫ inv_fun_id_assoc e G
  { Hom := P.desc ((cocones.equivalence_of_reindexing e w).Functor.obj t),
    inv := Q.desc ((cocones.equivalence_of_reindexing e.symm w').Functor.obj s),
    hom_inv_id' :=
      by 
        apply hom_ext P 
        intro j 
        dsimp 
        simp only [limits.cocone.whisker_ι, fac, inv_fun_id_assoc_inv_app, whisker_left_app, assoc, comp_id,
          limits.cocones.precompose_obj_ι, fac_assoc, nat_trans.comp_app]
        rw [counit_inv_app_functor, ←functor.comp_map, ←w.inv.naturality_assoc]
        dsimp 
        simp ,
    inv_hom_id' :=
      by 
        apply hom_ext Q 
        tidy }

end Equivalenceₓ

/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
  a cocone on `F` with vertex `W`. -/
def hom_iso (h : is_colimit t) (W : C) : Ulift.{u₁} (t.X ⟶ W : Type v₃) ≅ F ⟶ (const J).obj W :=
  { Hom := fun f => (t.extend f.down).ι, inv := fun ι => ⟨h.desc { x := W, ι }⟩,
    hom_inv_id' :=
      by 
        ext f <;> apply h.hom_ext <;> intro j <;> simp  <;> dsimp <;> rfl }

@[simp]
theorem hom_iso_hom (h : is_colimit t) {W : C} (f : Ulift (t.X ⟶ W)) :
  (is_colimit.hom_iso h W).Hom f = (t.extend f.down).ι :=
  rfl

/-- The colimit of `F` represents the functor taking `W` to
  the set of cocones on `F` with vertex `W`. -/
def nat_iso (h : is_colimit t) : coyoneda.obj (op t.X) ⋙ ulift_functor.{u₁} ≅ F.cocones :=
  nat_iso.of_components (is_colimit.hom_iso h)
    (by 
      intros  <;> ext <;> dsimp <;> rw [←assoc] <;> rfl)

/--
Another, more explicit, formulation of the universal property of a colimit cocone.
See also `hom_iso`.
-/
def hom_iso' (h : is_colimit t) (W : C) :
  Ulift.{u₁} (t.X ⟶ W : Type v₃) ≅ { p : ∀ j, F.obj j ⟶ W // ∀ {j j' : J} f : j ⟶ j', F.map f ≫ p j' = p j } :=
  h.hom_iso W ≪≫
    { Hom :=
        fun ι =>
          ⟨fun j => ι.app j,
            fun j j' f =>
              by 
                convert ← ι.naturality f <;> apply comp_id⟩,
      inv :=
        fun p =>
          { app := fun j => p.1 j,
            naturality' :=
              fun j j' f =>
                by 
                  dsimp 
                  rw [comp_id]
                  exact p.2 f } }

/-- If G : C → D is a faithful functor which sends t to a colimit cocone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def of_faithful {t : cocone F} {D : Type u₄} [category.{v₄} D] (G : C ⥤ D) [faithful G]
  (ht : is_colimit (G.map_cocone t)) (desc : ∀ s : cocone F, t.X ⟶ s.X)
  (h : ∀ s, G.map (desc s) = ht.desc (G.map_cocone s)) : is_colimit t :=
  { desc,
    fac' :=
      fun s j =>
        by 
          apply G.map_injective <;> rw [G.map_comp, h] <;> apply ht.fac,
    uniq' :=
      fun s m w =>
        by 
          apply G.map_injective 
          rw [h]
          refine' ht.uniq (G.map_cocone s) _ fun j => _ 
          convert ← congr_argₓ (fun f => G.map f) (w j)
          apply G.map_comp }

/--
If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a colimit implies
`G.map_cone c` is also a colimit.
-/
def map_cocone_equiv {D : Type u₄} [category.{v₄} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : cocone K}
  (t : is_colimit (F.map_cocone c)) : is_colimit (G.map_cocone c) :=
  by 
    apply is_colimit.of_iso_colimit _ (precompose_whisker_left_map_cocone h c)
    apply (precompose_inv_equiv (iso_whisker_left K h : _) _).symm t

/--
A cocone is a colimit cocone exactly if
there is a unique cocone morphism from any other cocone.
-/
def iso_unique_cocone_morphism {t : cocone F} : is_colimit t ≅ ∀ s, Unique (t ⟶ s) :=
  { Hom := fun h s => { default := h.desc_cocone_morphism s, uniq := fun _ => h.uniq_cocone_morphism },
    inv :=
      fun h =>
        { desc := fun s => (h s).default.Hom,
          uniq' := fun s f w => congr_argₓ cocone_morphism.hom ((h s).uniq ⟨f, w⟩) } }

namespace OfNatIso

variable {X : C} (h : coyoneda.obj (op X) ⋙ ulift_functor.{u₁} ≅ F.cocones)

/-- If `F.cocones` is corepresented by `X`, each morphism `f : X ⟶ Y` gives a cocone with cone
point `Y`. -/
def cocone_of_hom {Y : C} (f : X ⟶ Y) : cocone F :=
  { x := Y, ι := h.hom.app Y ⟨f⟩ }

/-- If `F.cocones` is corepresented by `X`, each cocone `s` gives a morphism `X ⟶ s.X`. -/
def hom_of_cocone (s : cocone F) : X ⟶ s.X :=
  (h.inv.app s.X s.ι).down

@[simp]
theorem cocone_of_hom_of_cocone (s : cocone F) : cocone_of_hom h (hom_of_cocone h s) = s :=
  by 
    dsimp [cocone_of_hom, hom_of_cocone]
    cases s 
    congr 
    dsimp 
    convert congr_funₓ (congr_funₓ (congr_argₓ nat_trans.app h.inv_hom_id) s_X) s_ι 
    exact Ulift.up_down _

@[simp]
theorem hom_of_cocone_of_hom {Y : C} (f : X ⟶ Y) : hom_of_cocone h (cocone_of_hom h f) = f :=
  congr_argₓ Ulift.down (congr_funₓ (congr_funₓ (congr_argₓ nat_trans.app h.hom_inv_id) Y) ⟨f⟩ : _)

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to the identity morphism on `X`
will be a colimit cocone. -/
def colimit_cocone : cocone F :=
  cocone_of_hom h (𝟙 X)

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to a morphism `f : Y ⟶ X` is
the colimit cocone extended by `f`. -/
theorem cocone_of_hom_fac {Y : C} (f : X ⟶ Y) : cocone_of_hom h f = (colimit_cocone h).extend f :=
  by 
    dsimp [cocone_of_hom, colimit_cocone, cocone.extend]
    congr with j 
    have t := congr_funₓ (h.hom.naturality f) ⟨𝟙 X⟩
    dsimp  at t 
    simp only [id_comp] at t 
    rw [congr_funₓ (congr_argₓ nat_trans.app t) j]
    rfl

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
    If `F.cocones` is corepresented by `X`, any cocone is the extension of the colimit cocone by the
    corresponding morphism. -/
  theorem
    cocone_fac
    ( s : cocone F ) : colimit_cocone h . extend hom_of_cocone h s = s
    :=
      by
        rw [ ← cocone_of_hom_of_cocone h s ]
          convLHS => simp only [ hom_of_cocone_of_hom ]
          apply cocone_of_hom_fac _ _ . symm

end OfNatIso

section 

open OfNatIso

/--
If `F.cocones` is corepresentable, then the cocone corresponding to the identity morphism on
the representing object is a colimit cocone.
-/
def of_nat_iso {X : C} (h : coyoneda.obj (op X) ⋙ ulift_functor.{u₁} ≅ F.cocones) : is_colimit (colimit_cocone h) :=
  { desc := fun s => hom_of_cocone h s,
    fac' :=
      fun s j =>
        by 
          have h := cocone_fac h s 
          cases s 
          injection h with h₁ h₂ 
          simp only [heq_iff_eq] at h₂ 
          convRHS => rw [←h₂]
          rfl,
    uniq' :=
      fun s m w =>
        by 
          rw [←hom_of_cocone_of_hom h m]
          congr 
          rw [cocone_of_hom_fac]
          dsimp [cocone.extend]
          cases s 
          congr with j 
          exact w j }

end 

end IsColimit

end CategoryTheory.Limits

