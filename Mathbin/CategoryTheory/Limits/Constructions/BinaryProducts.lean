import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Constructing binary product from pullbacks and terminal object.

The product is the pullback over the terminal objects. In particular, if a category
has pullbacks and a terminal object, then it has binary products.

We also provide the dual.
-/


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [category.{v} C]

/--  The pullback over the terminal object is the product -/
def isProductOfIsTerminalIsPullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y) (H₁ : is_terminal Z)
    (H₂ : is_limit (pullback_cone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) : is_limit (binary_fan.mk h k) :=
  { lift := fun c =>
      H₂.lift (pullback_cone.mk (c.π.app walking_pair.left) (c.π.app walking_pair.right) (H₁.hom_ext _ _)),
    fac' := fun c j => by
      convert
        H₂.fac (pullback_cone.mk (c.π.app walking_pair.left) (c.π.app walking_pair.right) (H₁.hom_ext _ _))
          (some j) using
        1
      cases j <;> rfl,
    uniq' := fun c m hm => by
      apply pullback_cone.is_limit.hom_ext H₂
      ·
        exact
          (hm walking_pair.left).trans
            (H₂.fac (pullback_cone.mk (c.π.app walking_pair.left) (c.π.app walking_pair.right) (H₁.hom_ext _ _))
                walking_cospan.left).symm
      ·
        exact
          (hm walking_pair.right).trans
            (H₂.fac (pullback_cone.mk (c.π.app walking_pair.left) (c.π.app walking_pair.right) (H₁.hom_ext _ _))
                walking_cospan.right).symm }

/--  The product is the pullback over the terminal object. -/
def isPullbackOfIsTerminalIsProduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y) (H₁ : is_terminal Z)
    (H₂ : is_limit (binary_fan.mk h k)) : is_limit (pullback_cone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply pullback_cone.is_limit_aux'
  intro s
  use H₂.lift (binary_fan.mk s.fst s.snd)
  use H₂.fac (binary_fan.mk s.fst s.snd) walking_pair.left
  use H₂.fac (binary_fan.mk s.fst s.snd) walking_pair.right
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟩
  ·
    exact h₁.trans (H₂.fac (binary_fan.mk s.fst s.snd) walking_pair.left).symm
  ·
    exact h₂.trans (H₂.fac (binary_fan.mk s.fst s.snd) walking_pair.right).symm

variable (C)

/--  Any category with pullbacks and terminal object has binary products. -/
theorem has_binary_products_of_terminal_and_pullbacks [has_terminal C] [has_pullbacks C] : has_binary_products C :=
  { HasLimit := fun F =>
      has_limit.mk
        { Cone :=
            { x := pullback (terminal.from (F.obj walking_pair.left)) (terminal.from (F.obj walking_pair.right)),
              π := discrete.nat_trans fun x => walking_pair.cases_on x pullback.fst pullback.snd },
          IsLimit :=
            { lift := fun c =>
                pullback.lift (c.π.app walking_pair.left) (c.π.app walking_pair.right) (Subsingleton.elimₓ _ _),
              fac' := fun s c => walking_pair.cases_on c (limit.lift_π _ _) (limit.lift_π _ _),
              uniq' := fun s m J => by
                rw [← J, ← J]
                ext <;> rw [limit.lift_π] <;> rfl } } }

variable {C}

/--  The pushout under the initial object is the coproduct -/
def isCoproductOfIsInitialIsPushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y) (H₁ : is_initial W)
    (H₂ : is_colimit (pushout_cocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    is_colimit (binary_cofan.mk f g) :=
  { desc := fun c =>
      H₂.desc (pushout_cocone.mk (c.ι.app walking_pair.left) (c.ι.app walking_pair.right) (H₁.hom_ext _ _)),
    fac' := fun c j => by
      convert
        H₂.fac (pushout_cocone.mk (c.ι.app walking_pair.left) (c.ι.app walking_pair.right) (H₁.hom_ext _ _))
          (some j) using
        1
      cases j <;> rfl,
    uniq' := fun c m hm => by
      apply pushout_cocone.is_colimit.hom_ext H₂
      ·
        exact
          (hm walking_pair.left).trans
            (H₂.fac (pushout_cocone.mk (c.ι.app walking_pair.left) (c.ι.app walking_pair.right) (H₁.hom_ext _ _))
                walking_cospan.left).symm
      ·
        exact
          (hm walking_pair.right).trans
            (H₂.fac (pushout_cocone.mk (c.ι.app walking_pair.left) (c.ι.app walking_pair.right) (H₁.hom_ext _ _))
                walking_cospan.right).symm }

/--  The coproduct is the pushout under the initial object. -/
def isPushoutOfIsInitialIsCoproduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y) (H₁ : is_terminal Z)
    (H₂ : is_limit (binary_fan.mk h k)) : is_limit (pullback_cone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply pullback_cone.is_limit_aux'
  intro s
  use H₂.lift (binary_fan.mk s.fst s.snd)
  use H₂.fac (binary_fan.mk s.fst s.snd) walking_pair.left
  use H₂.fac (binary_fan.mk s.fst s.snd) walking_pair.right
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟩
  ·
    exact h₁.trans (H₂.fac (binary_fan.mk s.fst s.snd) walking_pair.left).symm
  ·
    exact h₂.trans (H₂.fac (binary_fan.mk s.fst s.snd) walking_pair.right).symm

variable (C)

/--  Any category with pushouts and initial object has binary coproducts. -/
theorem has_binary_coproducts_of_initial_and_pushouts [has_initial C] [has_pushouts C] : has_binary_coproducts C :=
  { HasColimit := fun F =>
      has_colimit.mk
        { Cocone :=
            { x := pushout (initial.to (F.obj walking_pair.left)) (initial.to (F.obj walking_pair.right)),
              ι := discrete.nat_trans fun x => walking_pair.cases_on x pushout.inl pushout.inr },
          IsColimit :=
            { desc := fun c =>
                pushout.desc (c.ι.app walking_pair.left) (c.ι.app walking_pair.right) (Subsingleton.elimₓ _ _),
              fac' := fun s c => walking_pair.cases_on c (colimit.ι_desc _ _) (colimit.ι_desc _ _),
              uniq' := fun s m J => by
                rw [← J, ← J]
                ext <;> rw [colimit.ι_desc] <;> rfl } } }

