/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import Mathbin.CategoryTheory.CommSq
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathbin.CategoryTheory.Limits.Opposites

/-!
# Pullback and pushout squares

We provide another API for pullbacks and pushouts.

`is_pullback fst snd f g` is the proposition that
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square.

(And similarly for `is_pushout`.)

We provide the glue to go back and forth to the usual `is_limit` API for pullbacks, and prove
`is_pullback (pullback.fst : pullback f g ⟶ X) (pullback.snd : pullback f g ⟶ Y) f g`
for the usual `pullback f g` provided by the `has_limit` API.

We don't attempt to restate everything we know about pullbacks in this language,
but do restate the pasting lemmas.

## Future work
Bicartesian squares, and
show that the pullback and pushout squares for a biproduct are bicartesian.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

namespace CommSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/-- The (not necessarily limiting) `pullback_cone h i` implicit in the statement
that we have `comm_sq f g h i`.
-/
def cone (s : CommSq f g h i) : PullbackCone h i :=
  PullbackCone.mk _ _ s.w

/-- The (not necessarily limiting) `pushout_cocone f g` implicit in the statement
that we have `comm_sq f g h i`.
-/
def cocone (s : CommSq f g h i) : PushoutCocone f g :=
  PushoutCocone.mk _ _ s.w

/-- The pushout cocone in the opposite category associated to the cone of
a commutative square identifies to the cocone of the flipped commutative square in
the opposite category -/
def coneOp (p : CommSq f g h i) : p.Cone.op ≅ p.flip.op.Cocone :=
  PushoutCocone.ext (Iso.refl _)
    (by
      tidy)
    (by
      tidy)

/-- The pullback cone in the opposite category associated to the cocone of
a commutative square identifies to the cone of the flipped commutative square in
the opposite category -/
def coconeOp (p : CommSq f g h i) : p.Cocone.op ≅ p.flip.op.Cone :=
  PullbackCone.ext (Iso.refl _)
    (by
      tidy)
    (by
      tidy)

/-- The pushout cocone obtained from the pullback cone associated to a
commutative square in the opposite category identifies to the cocone associated
to the flipped square. -/
def coneUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    p.Cone.unop ≅ p.flip.unop.Cocone :=
  PushoutCocone.ext (Iso.refl _)
    (by
      tidy)
    (by
      tidy)

/-- The pullback cone obtained from the pushout cone associated to a
commutative square in the opposite category identifies to the cone associated
to the flipped square. -/
def coconeUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    p.Cocone.unop ≅ p.flip.unop.Cone :=
  PullbackCone.ext (Iso.refl _)
    (by
      tidy)
    (by
      tidy)

end CommSq

/-- The proposition that a square
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square.
-/
structure IsPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) extends CommSq fst snd f g :
  Prop where
  is_limit' : Nonempty (IsLimit (PullbackCone.mk _ _ w))

/-- The proposition that a square
```
  Z ---f---> X
  |          |
  g         inl
  |          |
  v          v
  Y --inr--> P

```
is a pushout square.
-/
structure IsPushout {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) extends CommSq f g inl inr :
  Prop where
  is_colimit' : Nonempty (IsColimit (PushoutCocone.mk _ _ w))

/-!
We begin by providing some glue between `is_pullback` and the `is_limit` and `has_limit` APIs.
(And similarly for `is_pushout`.)
-/


namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The (limiting) `pullback_cone f g` implicit in the statement
that we have a `is_pullback fst snd f g`.
-/
def cone (h : IsPullback fst snd f g) : PullbackCone f g :=
  h.to_comm_sq.Cone

/-- The cone obtained from `is_pullback fst snd f g` is a limit cone.
-/
noncomputable def isLimit (h : IsPullback fst snd f g) : IsLimit h.Cone :=
  h.is_limit'.some

/-- If `c` is a limiting pullback cone, then we have a `is_pullback c.fst c.snd f g`. -/
theorem of_is_limit {c : PullbackCone f g} (h : Limits.IsLimit c) : IsPullback c.fst c.snd f g :=
  { w := c.condition,
    is_limit' :=
      ⟨IsLimit.ofIsoLimit h
          (Limits.PullbackCone.ext (Iso.refl _)
            (by
              tidy)
            (by
              tidy))⟩ }

/-- A variant of `of_is_limit` that is more useful with `apply`. -/
theorem of_is_limit' (w : CommSq fst snd f g) (h : Limits.IsLimit w.Cone) : IsPullback fst snd f g :=
  of_is_limit h

/-- The pullback provided by `has_pullback f g` fits into a `is_pullback`. -/
theorem of_has_pullback (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsPullback (pullback.fst : pullback f g ⟶ X) (pullback.snd : pullback f g ⟶ Y) f g :=
  of_is_limit (limit.isLimit (cospan f g))

/-- If `c` is a limiting binary product cone, and we have a terminal object,
then we have `is_pullback c.fst c.snd 0 0`
(where each `0` is the unique morphism to the terminal object). -/
theorem of_is_product {c : BinaryFan X Y} (h : Limits.IsLimit c) (t : IsTerminal Z) :
    IsPullback c.fst c.snd (t.from _) (t.from _) :=
  of_is_limit
    (isPullbackOfIsTerminalIsProduct _ _ _ _ t
      (IsLimit.ofIsoLimit h
        (Limits.Cones.ext (Iso.refl c.x)
          (by
            rintro ⟨⟨⟩⟩ <;>
              · dsimp'
                simp
                ))))

variable (X Y)

theorem of_has_binary_product' [HasBinaryProduct X Y] [HasTerminal C] :
    IsPullback Limits.prod.fst Limits.prod.snd (terminal.from X) (terminal.from Y) :=
  of_is_product (limit.isLimit _) terminalIsTerminal

open ZeroObject

theorem of_has_binary_product [HasBinaryProduct X Y] [HasZeroObject C] [HasZeroMorphisms C] :
    IsPullback Limits.prod.fst Limits.prod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert of_is_product (limit.is_limit _) has_zero_object.zero_is_terminal

variable {X Y}

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `has_limit` API. -/
noncomputable def isoPullback (h : IsPullback fst snd f g) [HasPullback f g] : P ≅ pullback f g :=
  (limit.isoLimitCone ⟨_, h.IsLimit⟩).symm

@[simp]
theorem iso_pullback_hom_fst (h : IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.Hom ≫ pullback.fst = fst :=
  by
  dsimp' [← iso_pullback, ← cone, ← comm_sq.cone]
  simp

@[simp]
theorem iso_pullback_hom_snd (h : IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.Hom ≫ pullback.snd = snd :=
  by
  dsimp' [← iso_pullback, ← cone, ← comm_sq.cone]
  simp

@[simp]
theorem iso_pullback_inv_fst (h : IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ fst = pullback.fst :=
  by
  simp [← iso.inv_comp_eq]

@[simp]
theorem iso_pullback_inv_snd (h : IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ snd = pullback.snd :=
  by
  simp [← iso.inv_comp_eq]

theorem of_iso_pullback (h : CommSq fst snd f g) [HasPullback f g] (i : P ≅ pullback f g)
    (w₁ : i.Hom ≫ pullback.fst = fst) (w₂ : i.Hom ≫ pullback.snd = snd) : IsPullback fst snd f g :=
  of_is_limit' h
    (Limits.IsLimit.ofIsoLimit (limit.isLimit _)
      (@PullbackCone.ext _ _ _ _ _ _ _ (PullbackCone.mk _ _ _) _ i w₁.symm w₂.symm).symm)

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/-- The (colimiting) `pushout_cocone f g` implicit in the statement
that we have a `is_pushout f g inl inr`.
-/
def cocone (h : IsPushout f g inl inr) : PushoutCocone f g :=
  h.to_comm_sq.Cocone

/-- The cocone obtained from `is_pushout f g inl inr` is a colimit cocone.
-/
noncomputable def isColimit (h : IsPushout f g inl inr) : IsColimit h.Cocone :=
  h.is_colimit'.some

/-- If `c` is a colimiting pushout cocone, then we have a `is_pushout f g c.inl c.inr`. -/
theorem of_is_colimit {c : PushoutCocone f g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr :=
  { w := c.condition,
    is_colimit' :=
      ⟨IsColimit.ofIsoColimit h
          (Limits.PushoutCocone.ext (Iso.refl _)
            (by
              tidy)
            (by
              tidy))⟩ }

/-- A variant of `of_is_colimit` that is more useful with `apply`. -/
theorem of_is_colimit' (w : CommSq f g inl inr) (h : Limits.IsColimit w.Cocone) : IsPushout f g inl inr :=
  of_is_colimit h

/-- The pushout provided by `has_pushout f g` fits into a `is_pushout`. -/
theorem of_has_pushout (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] :
    IsPushout f g (pushout.inl : X ⟶ pushout f g) (pushout.inr : Y ⟶ pushout f g) :=
  of_is_colimit (colimit.isColimit (span f g))

/-- If `c` is a colimiting binary coproduct cocone, and we have an initial object,
then we have `is_pushout 0 0 c.inl c.inr`
(where each `0` is the unique morphism from the initial object). -/
theorem of_is_coproduct {c : BinaryCofan X Y} (h : Limits.IsColimit c) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) c.inl c.inr :=
  of_is_colimit
    (isPushoutOfIsInitialIsCoproduct _ _ _ _ t
      (IsColimit.ofIsoColimit h
        (Limits.Cocones.ext (Iso.refl c.x)
          (by
            rintro ⟨⟨⟩⟩ <;>
              · dsimp'
                simp
                ))))

variable (X Y)

theorem of_has_binary_coproduct' [HasBinaryCoproduct X Y] [HasInitial C] :
    IsPushout (initial.to _) (initial.to _) (coprod.inl : X ⟶ _) (coprod.inr : Y ⟶ _) :=
  of_is_coproduct (colimit.isColimit _) initialIsInitial

open ZeroObject

theorem of_has_binary_coproduct [HasBinaryCoproduct X Y] [HasZeroObject C] [HasZeroMorphisms C] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) coprod.inl coprod.inr := by
  convert of_is_coproduct (colimit.is_colimit _) has_zero_object.zero_is_initial

variable {X Y}

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `has_limit` API. -/
noncomputable def isoPushout (h : IsPushout f g inl inr) [HasPushout f g] : P ≅ pushout f g :=
  (colimit.isoColimitCocone ⟨_, h.IsColimit⟩).symm

@[simp]
theorem inl_iso_pushout_inv (h : IsPushout f g inl inr) [HasPushout f g] : pushout.inl ≫ h.isoPushout.inv = inl := by
  dsimp' [← iso_pushout, ← cocone, ← comm_sq.cocone]
  simp

@[simp]
theorem inr_iso_pushout_inv (h : IsPushout f g inl inr) [HasPushout f g] : pushout.inr ≫ h.isoPushout.inv = inr := by
  dsimp' [← iso_pushout, ← cocone, ← comm_sq.cocone]
  simp

@[simp]
theorem inl_iso_pushout_hom (h : IsPushout f g inl inr) [HasPushout f g] : inl ≫ h.isoPushout.Hom = pushout.inl := by
  simp [iso.eq_comp_inv]

@[simp]
theorem inr_iso_pushout_hom (h : IsPushout f g inl inr) [HasPushout f g] : inr ≫ h.isoPushout.Hom = pushout.inr := by
  simp [iso.eq_comp_inv]

theorem of_iso_pushout (h : CommSq f g inl inr) [HasPushout f g] (i : P ≅ pushout f g) (w₁ : inl ≫ i.Hom = pushout.inl)
    (w₂ : inr ≫ i.Hom = pushout.inr) : IsPushout f g inl inr :=
  of_is_colimit' h
    (Limits.IsColimit.ofIsoColimit (colimit.isColimit _)
      (@PushoutCocone.ext _ _ _ _ _ _ _ (PushoutCocone.mk _ _ _) _ i w₁ w₂).symm)

end IsPushout

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem flip (h : IsPullback fst snd f g) : IsPullback snd fst g f :=
  of_is_limit (@PullbackCone.flipIsLimit _ _ _ _ _ _ _ _ _ _ h.w.symm h.IsLimit)

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/-- The square with `0 : 0 ⟶ 0` on the left and `𝟙 X` on the right is a pullback square. -/
theorem zero_left (X : C) : IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  { w := by
      simp ,
    is_limit' :=
      ⟨{ lift := fun s => 0,
          fac' := fun s => by
            simpa using
              @pullback_cone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by
                  simpa using (pullback_cone.condition s).symm) }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pullback square. -/
theorem zero_top (X : C) : IsPullback (0 : 0 ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip

end

/-- Paste two pullback squares "vertically" to obtain another pullback square. -/
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁}
    {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂} (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁)
    (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_is_limit (bigSquareIsPullback _ _ _ _ _ _ _ s.w t.w t.IsLimit s.IsLimit)

/-- Paste two pullback squares "horizontally" to obtain another pullback square. -/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃} (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁)
    (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip

/-- Given a pullback square assembled from a commuting square on the top and
a pullback square on the bottom, the top square is a pullback square. -/
theorem of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁}
    {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂} (s : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁)
    (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  of_is_limit (leftSquareIsPullback _ _ _ _ _ _ _ p _ t.IsLimit s.IsLimit)

/-- Given a pullback square assembled from a commuting square on the left and
a pullback square on the right, the left square is a pullback square. -/
theorem of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃} (s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂))
    (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  (of_bot s.flip p.symm t.flip).flip

theorem op (h : IsPullback fst snd f g) : IsPushout g.op f.op snd.op fst.op :=
  IsPushout.of_is_colimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitOp h.flip.Cone h.flip.IsLimit)
      h.to_comm_sq.flip.coneOp)

theorem unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    IsPushout g.unop f.unop snd.unop fst.unop :=
  IsPushout.of_is_colimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitUnop h.flip.Cone h.flip.IsLimit)
      h.to_comm_sq.flip.coneUnop)

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

theorem flip (h : IsPushout f g inl inr) : IsPushout g f inr inl :=
  of_is_colimit (@PushoutCocone.flipIsColimit _ _ _ _ _ _ _ _ _ _ h.w.symm h.IsColimit)

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pushout square. -/
theorem zero_right (X : C) : IsPushout (0 : X ⟶ 0) (𝟙 X) (0 : 0 ⟶ 0) (0 : X ⟶ 0) :=
  { w := by
      simp ,
    is_colimit' :=
      ⟨{ desc := fun s => 0,
          fac' := fun s => by
            have c :=
              @pushout_cocone.coequalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by
                  simp )
                (by
                  simpa using pushout_cocone.condition s)
            dsimp'  at c
            simpa using c }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pushout square. -/
theorem zero_bot (X : C) : IsPushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : 0 ⟶ 0) :=
  (zero_right X).flip

end

/-- Paste two pushout squares "vertically" to obtain another pushout square. -/
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁}
    {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂} (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁)
    (t : IsPushout h₂₁ v₂₁ v₂₂ h₃₁) : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_is_colimit (bigSquareIsPushout _ _ _ _ _ _ _ s.w t.w t.IsColimit s.IsColimit)

/-- Paste two pushout squares "horizontally" to obtain another pushout square. -/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃} (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁)
    (t : IsPushout h₁₂ v₁₂ v₁₃ h₂₂) : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip

/-- Given a pushout square assembled from a pushout square on the top and
a commuting square on the bottom, the bottom square is a pushout square. -/
theorem of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁}
    {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂} (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁)
    (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  of_is_colimit (rightSquareIsPushout _ _ _ _ _ _ _ _ p t.IsColimit s.IsColimit)

/-- Given a pushout square assembled from a pushout square on the left and
a commuting square on the right, the right square is a pushout square. -/
theorem of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃} (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂))
    (p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  (of_bot s.flip p.symm t.flip).flip

theorem op (h : IsPushout f g inl inr) : IsPullback inr.op inl.op g.op f.op :=
  IsPullback.of_is_limit
    (IsLimit.ofIsoLimit (Limits.PushoutCocone.isColimitEquivIsLimitOp h.flip.Cocone h.flip.IsColimit)
      h.to_comm_sq.flip.coconeOp)

theorem unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) :
    IsPullback inr.unop inl.unop g.unop f.unop :=
  IsPullback.of_is_limit
    (IsLimit.ofIsoLimit (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.Cocone h.flip.IsColimit)
      h.to_comm_sq.flip.coconeUnop)

end IsPushout

namespace Functor

variable {D : Type u₂} [Category.{v₂} D]

variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

theorem map_is_pullback [PreservesLimit (cospan h i) F] (s : IsPullback f g h i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) := by
  -- This is made slightly awkward because `C` and `D` have different universes,
  -- and so the relevant `walking_cospan` diagrams live in different universes too!
  refine'
    is_pullback.of_is_limit' (F.map_comm_sq s.to_comm_sq)
      (is_limit.equiv_of_nat_iso_of_iso (cospan_comp_iso F h i) _ _ (walking_cospan.ext _ _ _)
        (is_limit_of_preserves F s.is_limit))
  · rfl
    
  · dsimp'
    simp
    rfl
    
  · dsimp'
    simp
    rfl
    

theorem map_is_pushout [PreservesColimit (span f g) F] (s : IsPushout f g h i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine'
    is_pushout.of_is_colimit' (F.map_comm_sq s.to_comm_sq)
      (is_colimit.equiv_of_nat_iso_of_iso (span_comp_iso F f g) _ _ (walking_span.ext _ _ _)
        (is_colimit_of_preserves F s.is_colimit))
  · rfl
    
  · dsimp'
    simp
    rfl
    
  · dsimp'
    simp
    rfl
    

end Functor

alias functor.map_is_pullback ← is_pullback.map

alias functor.map_is_pushout ← is_pushout.map

end CategoryTheory

