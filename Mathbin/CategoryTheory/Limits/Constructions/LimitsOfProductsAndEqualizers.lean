import Mathbin.CategoryTheory.Limits.Shapes.Equalizers 
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts 
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products 
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

If a functor preserves all products and equalizers, then it preserves all limits.
Similarly, if it preserves all finite products and equalizers, then it preserves all finite limits.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/


open CategoryTheory

open Opposite

namespace CategoryTheory.Limits

universe v u u₂

variable{C : Type u}[category.{v} C]

variable{J : Type v}[small_category J]

namespace HasLimitOfHasProductsOfHasEqualizers

-- error in CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
variables
{F : «expr ⥤ »(J, C)}
{c₁ : fan F.obj}
{c₂ : fan (λ f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.1, p.2)), F.obj f.1.2)}
(s t : «expr ⟶ »(c₁.X, c₂.X))
(hs : ∀
 f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.1, p.2)), «expr = »(«expr ≫ »(s, c₂.π.app f), «expr ≫ »(c₁.π.app f.1.1, F.map f.2)))
(ht : ∀ f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.1, p.2)), «expr = »(«expr ≫ »(t, c₂.π.app f), c₁.π.app f.1.2))
(i : fork s t)

include hs ht

/--
(Implementation) Given the appropriate product and equalizer cones, build the cone for `F` which is
limiting if the given cones are also.
-/
@[simps]
def build_limit : cone F :=
  { x := i.X,
    π :=
      { app := fun j => i.ι ≫ c₁.π.app _,
        naturality' :=
          fun j₁ j₂ f =>
            by 
              dsimp 
              rw [category.id_comp, category.assoc, ←hs ⟨⟨_, _⟩, f⟩, i.condition_assoc, ht] } }

variable{i}

/--
(Implementation) Show the cone constructed in `build_limit` is limiting, provided the cones used in
its construction are.
-/
def build_is_limit (t₁ : is_limit c₁) (t₂ : is_limit c₂) (hi : is_limit i) : is_limit (build_limit s t hs ht i) :=
  { lift :=
      fun q =>
        by 
          refine' hi.lift (fork.of_ι _ _)
          ·
            refine' t₁.lift (fan.mk _ fun j => _)
            apply q.π.app j
          ·
            apply t₂.hom_ext 
            simp [hs, ht],
    uniq' :=
      fun q m w =>
        hi.hom_ext
          (i.equalizer_ext
            (t₁.hom_ext
              (by 
                simpa using w))) }

end HasLimitOfHasProductsOfHasEqualizers

open HasLimitOfHasProductsOfHasEqualizers

-- error in CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
Given the existence of the appropriate (possibly finite) products and equalizers, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
theorem has_limit_of_equalizer_and_product
(F : «expr ⥤ »(J, C))
[has_limit (discrete.functor F.obj)]
[has_limit (discrete.functor (λ f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.1, p.2)), F.obj f.1.2))]
[has_equalizers C] : has_limit F :=
has_limit.mk { cone := _,
  is_limit := build_is_limit (pi.lift (λ
    f, «expr ≫ »(limit.π _ _, F.map f.2))) (pi.lift (λ
    f, limit.π _ f.1.2)) (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] []) (limit.is_limit _) (limit.is_limit _) (limit.is_limit _) }

/--
Any category with products and equalizers has all limits.

See https://stacks.math.columbia.edu/tag/002N.
-/
theorem limits_from_equalizers_and_products [has_products C] [has_equalizers C] : has_limits C :=
  { HasLimitsOfShape :=
      fun J 𝒥 =>
        { HasLimit :=
            fun F =>
              by 
                exact has_limit_of_equalizer_and_product F } }

/--
Any category with finite products and equalizers has all finite limits.

See https://stacks.math.columbia.edu/tag/002O.
-/
theorem finite_limits_from_equalizers_and_finite_products [has_finite_products C] [has_equalizers C] :
  has_finite_limits C :=
  ⟨fun J _ _ =>
      { HasLimit :=
          fun F =>
            by 
              exact has_limit_of_equalizer_and_product F }⟩

variable{D : Type u₂}[category.{v} D]

noncomputable theory

section 

variable[has_limits_of_shape (discrete J) C][has_limits_of_shape (discrete (Σp : J × J, p.1 ⟶ p.2)) C][has_equalizers C]

variable(G :
    C ⥤
      D)[preserves_limits_of_shape walking_parallel_pair
      G][preserves_limits_of_shape (discrete J) G][preserves_limits_of_shape (discrete (Σp : J × J, p.1 ⟶ p.2)) G]

-- error in CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If a functor preserves equalizers and the appropriate products, it preserves limits. -/
def preserves_limit_of_preserves_equalizers_and_product : preserves_limits_of_shape J G :=
{ preserves_limit := λ K, begin
    let [ident P] [] [":=", expr «expr∏ »(K.obj)],
    let [ident Q] [] [":=", expr «expr∏ »(λ
      f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.fst, p.snd)), K.obj f.1.2)],
    let [ident s] [":", expr «expr ⟶ »(P, Q)] [":=", expr pi.lift (λ f, «expr ≫ »(limit.π _ _, K.map f.2))],
    let [ident t] [":", expr «expr ⟶ »(P, Q)] [":=", expr pi.lift (λ f, limit.π _ f.1.2)],
    let [ident I] [] [":=", expr equalizer s t],
    let [ident i] [":", expr «expr ⟶ »(I, P)] [":=", expr equalizer.ι s t],
    apply [expr preserves_limit_of_preserves_limit_cone (build_is_limit s t (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] []) (limit.is_limit _) (limit.is_limit _) (limit.is_limit _))],
    refine [expr is_limit.of_iso_limit (build_is_limit _ _ _ _ _ _ _) _],
    { exact [expr fan.mk _ (λ j, G.map (pi.π _ j))] },
    { exact [expr fan.mk (G.obj Q) (λ f, G.map (pi.π _ f))] },
    { apply [expr G.map s] },
    { apply [expr G.map t] },
    { intro [ident f],
      dsimp [] [] [] [],
      simp [] [] ["only"] ["[", "<-", expr G.map_comp, ",", expr limit.lift_π, ",", expr fan.mk_π_app, "]"] [] [] },
    { intro [ident f],
      dsimp [] [] [] [],
      simp [] [] ["only"] ["[", "<-", expr G.map_comp, ",", expr limit.lift_π, ",", expr fan.mk_π_app, "]"] [] [] },
    { apply [expr fork.of_ι (G.map i) _],
      simp [] [] ["only"] ["[", "<-", expr G.map_comp, ",", expr equalizer.condition, "]"] [] [] },
    { apply [expr is_limit_of_has_product_of_preserves_limit] },
    { apply [expr is_limit_of_has_product_of_preserves_limit] },
    { apply [expr is_limit_fork_map_of_is_limit],
      apply [expr equalizer_is_equalizer] },
    refine [expr cones.ext (iso.refl _) _],
    intro [ident j],
    dsimp [] [] [] [],
    simp [] [] [] [] [] []
  end }

end 

/-- If G preserves equalizers and finite products, it preserves finite limits. -/
def preserves_finite_limits_of_preserves_equalizers_and_finite_products [has_equalizers C] [has_finite_products C]
  (G : C ⥤ D) [preserves_limits_of_shape walking_parallel_pair G]
  [∀ J [Fintype J], preserves_limits_of_shape (discrete J) G] (J : Type v) [small_category J] [fin_category J] :
  preserves_limits_of_shape J G :=
  preserves_limit_of_preserves_equalizers_and_product G

/-- If G preserves equalizers and products, it preserves all limits. -/
def preserves_limits_of_preserves_equalizers_and_products [has_equalizers C] [has_products C] (G : C ⥤ D)
  [preserves_limits_of_shape walking_parallel_pair G] [∀ J, preserves_limits_of_shape (discrete J) G] :
  preserves_limits G :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact preserves_limit_of_preserves_equalizers_and_product G }

/-!
We now dualize the above constructions, resorting to copy-paste.
-/


namespace HasColimitOfHasCoproductsOfHasCoequalizers

-- error in CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
variables
{F : «expr ⥤ »(J, C)}
{c₁ : cofan (λ f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.1, p.2)), F.obj f.1.1)}
{c₂ : cofan F.obj}
(s t : «expr ⟶ »(c₁.X, c₂.X))
(hs : ∀
 f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.1, p.2)), «expr = »(«expr ≫ »(c₁.ι.app f, s), «expr ≫ »(F.map f.2, c₂.ι.app f.1.2)))
(ht : ∀ f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.1, p.2)), «expr = »(«expr ≫ »(c₁.ι.app f, t), c₂.ι.app f.1.1))
(i : cofork s t)

include hs ht

/--
(Implementation) Given the appropriate coproduct and coequalizer cocones,
build the cocone for `F` which is colimiting if the given cocones are also.
-/
@[simps]
def build_colimit : cocone F :=
  { x := i.X,
    ι :=
      { app := fun j => c₂.ι.app _ ≫ i.π,
        naturality' :=
          fun j₁ j₂ f =>
            by 
              dsimp 
              rw [category.comp_id, ←reassoc_of (hs ⟨⟨_, _⟩, f⟩), i.condition, ←category.assoc, ht] } }

variable{i}

/--
(Implementation) Show the cocone constructed in `build_colimit` is colimiting,
provided the cocones used in its construction are.
-/
def build_is_colimit (t₁ : is_colimit c₁) (t₂ : is_colimit c₂) (hi : is_colimit i) :
  is_colimit (build_colimit s t hs ht i) :=
  { desc :=
      fun q =>
        by 
          refine' hi.desc (cofork.of_π _ _)
          ·
            refine' t₂.desc (cofan.mk _ fun j => _)
            apply q.ι.app j
          ·
            apply t₁.hom_ext 
            simp [reassoc_of hs, reassoc_of ht],
    uniq' :=
      fun q m w =>
        hi.hom_ext
          (i.coequalizer_ext
            (t₂.hom_ext
              (by 
                simpa using w))) }

end HasColimitOfHasCoproductsOfHasCoequalizers

open HasColimitOfHasCoproductsOfHasCoequalizers

-- error in CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we know a colimit of `F` exists.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
theorem has_colimit_of_coequalizer_and_coproduct
(F : «expr ⥤ »(J, C))
[has_colimit (discrete.functor F.obj)]
[has_colimit (discrete.functor (λ f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.1, p.2)), F.obj f.1.1))]
[has_coequalizers C] : has_colimit F :=
has_colimit.mk { cocone := _,
  is_colimit := build_is_colimit (sigma.desc (λ
    f, «expr ≫ »(F.map f.2, colimit.ι (discrete.functor F.obj) f.1.2))) (sigma.desc (λ
    f, colimit.ι (discrete.functor F.obj) f.1.1)) (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] []) (colimit.is_colimit _) (colimit.is_colimit _) (colimit.is_colimit _) }

/--
Any category with coproducts and coequalizers has all colimits.

See https://stacks.math.columbia.edu/tag/002P.
-/
theorem colimits_from_coequalizers_and_coproducts [has_coproducts C] [has_coequalizers C] : has_colimits C :=
  { HasColimitsOfShape :=
      fun J 𝒥 =>
        { HasColimit :=
            fun F =>
              by 
                exact has_colimit_of_coequalizer_and_coproduct F } }

/--
Any category with finite coproducts and coequalizers has all finite colimits.

See https://stacks.math.columbia.edu/tag/002Q.
-/
theorem finite_colimits_from_coequalizers_and_finite_coproducts [has_finite_coproducts C] [has_coequalizers C] :
  has_finite_colimits C :=
  ⟨fun J _ _ =>
      { HasColimit :=
          fun F =>
            by 
              exact has_colimit_of_coequalizer_and_coproduct F }⟩

noncomputable theory

section 

variable[has_colimits_of_shape (discrete J)
      C][has_colimits_of_shape (discrete (Σp : J × J, p.1 ⟶ p.2)) C][has_coequalizers C]

variable(G :
    C ⥤
      D)[preserves_colimits_of_shape walking_parallel_pair
      G][preserves_colimits_of_shape (discrete J) G][preserves_colimits_of_shape (discrete (Σp : J × J, p.1 ⟶ p.2)) G]

-- error in CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If a functor preserves coequalizers and the appropriate coproducts, it preserves colimits. -/
def preserves_colimit_of_preserves_coequalizers_and_coproduct : preserves_colimits_of_shape J G :=
{ preserves_colimit := λ K, begin
    let [ident P] [] [":=", expr «expr∐ »(K.obj)],
    let [ident Q] [] [":=", expr «expr∐ »(λ
      f : «exprΣ , »((p : «expr × »(J, J)), «expr ⟶ »(p.fst, p.snd)), K.obj f.1.1)],
    let [ident s] [":", expr «expr ⟶ »(Q, P)] [":=", expr sigma.desc (λ
      f, «expr ≫ »(K.map f.2, colimit.ι (discrete.functor K.obj) _))],
    let [ident t] [":", expr «expr ⟶ »(Q, P)] [":=", expr sigma.desc (λ f, colimit.ι (discrete.functor K.obj) f.1.1)],
    let [ident I] [] [":=", expr coequalizer s t],
    let [ident i] [":", expr «expr ⟶ »(P, I)] [":=", expr coequalizer.π s t],
    apply [expr preserves_colimit_of_preserves_colimit_cocone (build_is_colimit s t (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] []) (colimit.is_colimit _) (colimit.is_colimit _) (colimit.is_colimit _))],
    refine [expr is_colimit.of_iso_colimit (build_is_colimit _ _ _ _ _ _ _) _],
    { exact [expr cofan.mk (G.obj Q) (λ j, G.map (sigma.ι _ j))] },
    { exact [expr cofan.mk _ (λ f, G.map (sigma.ι _ f))] },
    { apply [expr G.map s] },
    { apply [expr G.map t] },
    { intro [ident f],
      dsimp [] [] [] [],
      simp [] [] ["only"] ["[", "<-", expr G.map_comp, ",", expr colimit.ι_desc, ",", expr cofan.mk_ι_app, "]"] [] [] },
    { intro [ident f],
      dsimp [] [] [] [],
      simp [] [] ["only"] ["[", "<-", expr G.map_comp, ",", expr colimit.ι_desc, ",", expr cofan.mk_ι_app, "]"] [] [] },
    { apply [expr cofork.of_π (G.map i) _],
      simp [] [] ["only"] ["[", "<-", expr G.map_comp, ",", expr coequalizer.condition, "]"] [] [] },
    { apply [expr is_colimit_of_has_coproduct_of_preserves_colimit] },
    { apply [expr is_colimit_of_has_coproduct_of_preserves_colimit] },
    { apply [expr is_colimit_cofork_map_of_is_colimit],
      apply [expr coequalizer_is_coequalizer] },
    refine [expr cocones.ext (iso.refl _) _],
    intro [ident j],
    dsimp [] [] [] [],
    simp [] [] [] [] [] []
  end }

end 

/-- If G preserves coequalizers and finite coproducts, it preserves finite colimits. -/
def preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts [has_coequalizers C]
  [has_finite_coproducts C] (G : C ⥤ D) [preserves_colimits_of_shape walking_parallel_pair G]
  [∀ J [Fintype J], preserves_colimits_of_shape (discrete J) G] (J : Type v) [small_category J] [fin_category J] :
  preserves_colimits_of_shape J G :=
  preserves_colimit_of_preserves_coequalizers_and_coproduct G

/-- If G preserves coequalizers and coproducts, it preserves all colimits. -/
def preserves_colimits_of_preserves_coequalizers_and_coproducts [has_coequalizers C] [has_coproducts C] (G : C ⥤ D)
  [preserves_colimits_of_shape walking_parallel_pair G] [∀ J, preserves_colimits_of_shape (discrete J) G] :
  preserves_colimits G :=
  { PreservesColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact preserves_colimit_of_preserves_coequalizers_and_coproduct G }

end CategoryTheory.Limits

