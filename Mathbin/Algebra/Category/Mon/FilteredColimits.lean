/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer

! This file was ported from Lean 3 source module algebra.category.Mon.filtered_colimits
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.CategoryTheory.Limits.Preserves.Filtered
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise
import Mathbin.CategoryTheory.Limits.Types

/-!
# The forgetful functor from (commutative) (additive) monoids preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Mon`.
We then construct a monoid structure on the colimit of `F ⋙ forget Mon` (in `Type`), thereby
showing that the forgetful functor `forget Mon` preserves filtered colimits. Similarly for `AddMon`,
`CommMon` and `AddCommMon`.

-/


universe v u

noncomputable section

open Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max'

-- avoid name collision with `_root_.max`.
namespace Mon.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `M` and `M.mk` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J](F : J ⥤ Mon.{max v u})

/-- The colimit of `F ⋙ forget Mon` in the category of types.
In the following, we will construct a monoid structure on `M`.
-/
@[to_additive
      "The colimit of `F ⋙ forget AddMon` in the category of types.\nIn the following, we will construct an additive monoid structure on `M`."]
abbrev M : Type max v u :=
  Types.Quot (F ⋙ forget Mon)
#align Mon.filtered_colimits.M Mon.FilteredColimits.M
#align AddMon.filtered_colimits.M AddMon.FilteredColimits.M

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
abbrev M.mk : (Σj, F.obj j) → M :=
  Quot.mk (Types.Quot.Rel (F ⋙ forget Mon))
#align Mon.filtered_colimits.M.mk Mon.FilteredColimits.M.mk
#align AddMon.filtered_colimits.M.mk AddMon.FilteredColimits.M.mk

@[to_additive]
theorem M.mk_eq (x y : Σj, F.obj j)
    (h : ∃ (k : J)(f : x.1 ⟶ k)(g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk x = M.mk y :=
  Quot.EqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget Mon) x y h)
#align Mon.filtered_colimits.M.mk_eq Mon.FilteredColimits.M.mk_eq
#align AddMon.filtered_colimits.M.mk_eq AddMon.FilteredColimits.M.mk_eq

variable [IsFiltered J]

/-- As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to define the
"one" in the colimit as the equivalence class of `⟨j₀, 1 : F.obj j₀⟩`.
-/
@[to_additive
      "As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to\ndefine the \"zero\" in the colimit as the equivalence class of `⟨j₀, 0 : F.obj j₀⟩`."]
instance colimitHasOne : One M where one := M.mk ⟨IsFiltered.nonempty.some, 1⟩
#align Mon.filtered_colimits.colimit_has_one Mon.FilteredColimits.colimitHasOne
#align AddMon.filtered_colimits.colimit_has_zero AddMon.FilteredColimits.colimitHasZero

/-- The definition of the "one" in the colimit is independent of the chosen object of `J`.
In particular, this lemma allows us to "unfold" the definition of `colimit_one` at a custom chosen
object `j`.
-/
@[to_additive
      "The definition of the \"zero\" in the colimit is independent of the chosen object\nof `J`. In particular, this lemma allows us to \"unfold\" the definition of `colimit_zero` at a\ncustom chosen object `j`."]
theorem colimit_one_eq (j : J) : (1 : M) = M.mk ⟨j, 1⟩ :=
  by
  apply M.mk_eq
  refine' ⟨max' _ j, left_to_max _ j, right_to_max _ j, _⟩
  simp
#align Mon.filtered_colimits.colimit_one_eq Mon.FilteredColimits.colimit_one_eq
#align AddMon.filtered_colimits.colimit_zero_eq AddMon.FilteredColimits.colimit_zero_eq

/-- The "unlifted" version of multiplication in the colimit. To multiply two dependent pairs
`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `is_filtered.max`)
and multiply them there.
-/
@[to_additive
      "The \"unlifted\" version of addition in the colimit. To add two dependent pairs\n`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `is_filtered.max`)\nand add them there."]
def colimitMulAux (x y : Σj, F.obj j) : M :=
  M.mk ⟨max x.1 y.1, F.map (leftToMax x.1 y.1) x.2 * F.map (rightToMax x.1 y.1) y.2⟩
#align Mon.filtered_colimits.colimit_mul_aux Mon.FilteredColimits.colimitMulAux
#align AddMon.filtered_colimits.colimit_add_aux AddMon.FilteredColimits.colimitAddAux

/-- Multiplication in the colimit is well-defined in the left argument. -/
@[to_additive "Addition in the colimit is well-defined in the left argument."]
theorem colimitMulAux_eq_of_rel_left {x x' y : Σj, F.obj j}
    (hxx' : Types.FilteredColimit.Rel (F ⋙ forget Mon) x x') :
    colimit_mul_aux x y = colimit_mul_aux x' y :=
  by
  cases' x with j₁ x; cases' y with j₂ y; cases' x' with j₃ x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  simp at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    tulip (left_to_max j₁ j₂) (right_to_max j₁ j₂) (right_to_max j₃ j₂) (left_to_max j₃ j₂) f g
  apply M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [MonoidHom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
#align Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_left Mon.FilteredColimits.colimitMulAux_eq_of_rel_left
#align AddMon.filtered_colimits.colimit_add_aux_eq_of_rel_left AddMon.FilteredColimits.colimit_add_aux_eq_of_rel_left

/-- Multiplication in the colimit is well-defined in the right argument. -/
@[to_additive "Addition in the colimit is well-defined in the right argument."]
theorem colimitMulAux_eq_of_rel_right {x y y' : Σj, F.obj j}
    (hyy' : Types.FilteredColimit.Rel (F ⋙ forget Mon) y y') :
    colimit_mul_aux x y = colimit_mul_aux x y' :=
  by
  cases' y with j₁ y; cases' x with j₂ x; cases' y' with j₃ y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    tulip (right_to_max j₂ j₁) (left_to_max j₂ j₁) (left_to_max j₂ j₃) (right_to_max j₂ j₃) f g
  apply M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [MonoidHom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
#align Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_right Mon.FilteredColimits.colimitMulAux_eq_of_rel_right
#align AddMon.filtered_colimits.colimit_add_aux_eq_of_rel_right AddMon.FilteredColimits.colimit_add_aux_eq_of_rel_right

/-- Multiplication in the colimit. See also `colimit_mul_aux`. -/
@[to_additive "Addition in the colimit. See also `colimit_add_aux`."]
instance colimitHasMul : Mul M
    where mul x y := by
    refine' Quot.lift₂ (colimit_mul_aux F) _ _ x y
    · intro x y y' h
      apply colimit_mul_aux_eq_of_rel_right
      apply types.filtered_colimit.rel_of_quot_rel
      exact h
    · intro x x' y h
      apply colimit_mul_aux_eq_of_rel_left
      apply types.filtered_colimit.rel_of_quot_rel
      exact h
#align Mon.filtered_colimits.colimit_has_mul Mon.FilteredColimits.colimitHasMul
#align AddMon.filtered_colimits.colimit_has_add AddMon.FilteredColimits.colimitHasAdd

/-- Multiplication in the colimit is independent of the chosen "maximum" in the filtered category.
In particular, this lemma allows us to "unfold" the definition of the multiplication of `x` and `y`,
using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`.
-/
@[to_additive
      "Addition in the colimit is independent of the chosen \"maximum\" in the filtered\ncategory. In particular, this lemma allows us to \"unfold\" the definition of the addition of `x`\nand `y`, using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`."]
theorem colimit_mul_mk_eq (x y : Σj, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk x * M.mk y = M.mk ⟨k, F.map f x.2 * F.map g y.2⟩ :=
  by
  cases' x with j₁ x; cases' y with j₂ y
  obtain ⟨s, α, β, h₁, h₂⟩ := bowtie (left_to_max j₁ j₂) f (right_to_max j₁ j₂) g
  apply M.mk_eq
  use s, α, β
  dsimp
  simp_rw [MonoidHom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂]
#align Mon.filtered_colimits.colimit_mul_mk_eq Mon.FilteredColimits.colimit_mul_mk_eq
#align AddMon.filtered_colimits.colimit_add_mk_eq AddMon.FilteredColimits.colimit_add_mk_eq

@[to_additive]
instance colimitMonoid : Monoid M :=
  { colimit_has_one,
    colimit_has_mul with
    one_mul := fun x => by
      apply Quot.inductionOn x; clear x; intro x; cases' x with j x
      rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, 1⟩ ⟨j, x⟩ j (𝟙 j) (𝟙 j), MonoidHom.map_one,
        one_mul, F.map_id, id_apply]
    mul_one := fun x => by
      apply Quot.inductionOn x; clear x; intro x; cases' x with j x
      rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, 1⟩ j (𝟙 j) (𝟙 j), MonoidHom.map_one,
        mul_one, F.map_id, id_apply]
    mul_assoc := fun x y z => by
      apply Quot.induction_on₃ x y z; clear x y z; intro x y z
      cases' x with j₁ x; cases' y with j₂ y; cases' z with j₃ z
      rw [colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨j₂, y⟩ _ (first_to_max₃ j₁ j₂ j₃) (second_to_max₃ j₁ j₂ j₃),
        colimit_mul_mk_eq F ⟨max₃ j₁ j₂ j₃, _⟩ ⟨j₃, z⟩ _ (𝟙 _) (third_to_max₃ j₁ j₂ j₃),
        colimit_mul_mk_eq F ⟨j₂, y⟩ ⟨j₃, z⟩ _ (second_to_max₃ j₁ j₂ j₃) (third_to_max₃ j₁ j₂ j₃),
        colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨max₃ j₁ j₂ j₃, _⟩ _ (first_to_max₃ j₁ j₂ j₃) (𝟙 _)]
      simp only [F.map_id, id_apply, mul_assoc] }
#align Mon.filtered_colimits.colimit_monoid Mon.FilteredColimits.colimitMonoid
#align AddMon.filtered_colimits.colimit_add_monoid AddMon.FilteredColimits.colimitAddMonoid

/-- The bundled monoid giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive monoid giving the filtered colimit of a diagram."]
def colimit : Mon :=
  Mon.of M
#align Mon.filtered_colimits.colimit Mon.FilteredColimits.colimit
#align AddMon.filtered_colimits.colimit AddMon.FilteredColimits.colimit

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
@[to_additive
      "The additive monoid homomorphism from a given additive monoid in the diagram to the\ncolimit additive monoid."]
def coconeMorphism (j : J) : F.obj j ⟶ colimit
    where
  toFun := (Types.colimitCocone (F ⋙ forget Mon)).ι.app j
  map_one' := (colimit_one_eq j).symm
  map_mul' x y := by
    convert (colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 j) (𝟙 j)).symm
    rw [F.map_id, id_apply, id_apply]; rfl
#align Mon.filtered_colimits.cocone_morphism Mon.FilteredColimits.coconeMorphism
#align AddMon.filtered_colimits.cocone_morphism AddMon.FilteredColimits.coconeMorphism

@[simp, to_additive]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ cocone_morphism j' = cocone_morphism j :=
  MonoidHom.coe_inj ((Types.colimitCocone (F ⋙ forget Mon)).ι.naturality f)
#align Mon.filtered_colimits.cocone_naturality Mon.FilteredColimits.cocone_naturality
#align AddMon.filtered_colimits.cocone_naturality AddMon.FilteredColimits.cocone_naturality

/-- The cocone over the proposed colimit monoid. -/
@[to_additive "The cocone over the proposed colimit additive monoid."]
def colimitCocone : cocone F where
  x := colimit
  ι := { app := cocone_morphism }
#align Mon.filtered_colimits.colimit_cocone Mon.FilteredColimits.colimitCocone
#align AddMon.filtered_colimits.colimit_cocone AddMon.FilteredColimits.colimitCocone

/-- Given a cocone `t` of `F`, the induced monoid homomorphism from the colimit to the cocone point.
As a function, this is simply given by the induced map of the corresponding cocone in `Type`.
The only thing left to see is that it is a monoid homomorphism.
-/
@[to_additive
      "Given a cocone `t` of `F`, the induced additive monoid homomorphism from the colimit\nto the cocone point. As a function, this is simply given by the induced map of the corresponding\ncocone in `Type`. The only thing left to see is that it is an additive monoid homomorphism."]
def colimitDesc (t : cocone F) : colimit ⟶ t.x
    where
  toFun := (Types.colimitCoconeIsColimit (F ⋙ forget Mon)).desc ((forget Mon).mapCocone t)
  map_one' := by
    rw [colimit_one_eq F is_filtered.nonempty.some]
    exact MonoidHom.map_one _
  map_mul' x y := by
    apply Quot.induction_on₂ x y; clear x y; intro x y
    cases' x with i x; cases' y with j y
    rw [colimit_mul_mk_eq F ⟨i, x⟩ ⟨j, y⟩ (max' i j) (left_to_max i j) (right_to_max i j)]
    dsimp [types.colimit_cocone_is_colimit]
    rw [MonoidHom.map_mul, t.w_apply, t.w_apply]
#align Mon.filtered_colimits.colimit_desc Mon.FilteredColimits.colimitDesc
#align AddMon.filtered_colimits.colimit_desc AddMon.FilteredColimits.colimitDesc

/-- The proposed colimit cocone is a colimit in `Mon`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddMon`."]
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc := colimit_desc
  fac' t j :=
    MonoidHom.coe_inj
      ((Types.colimitCoconeIsColimit (F ⋙ forget Mon)).fac ((forget Mon).mapCocone t) j)
  uniq' t m h :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget Mon)).uniq ((forget Mon).mapCocone t) m fun j =>
        funext fun x => MonoidHom.congr_fun (h j) x
#align Mon.filtered_colimits.colimit_cocone_is_colimit Mon.FilteredColimits.colimitCoconeIsColimit
#align AddMon.filtered_colimits.colimit_cocone_is_colimit AddMon.FilteredColimits.colimit_cocone_is_colimit

@[to_additive]
instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget Mon.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (types.colimit_cocone_is_colimit (F ⋙ forget Mon.{u})) }
#align Mon.filtered_colimits.forget_preserves_filtered_colimits Mon.FilteredColimits.forgetPreservesFilteredColimits
#align AddMon.filtered_colimits.forget_preserves_filtered_colimits AddMon.FilteredColimits.forget_preserves_filtered_colimits

end

end Mon.FilteredColimits

namespace CommMon.FilteredColimits

open Mon.FilteredColimits (colimit_mul_mk_eq)

section

-- We use parameters here, mainly so we can have the abbreviation `M` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J][IsFiltered J](F : J ⥤ CommMon.{max v u})

/-- The colimit of `F ⋙ forget₂ CommMon Mon` in the category `Mon`.
In the following, we will show that this has the structure of a _commutative_ monoid.
-/
@[to_additive
      "The colimit of `F ⋙ forget₂ AddCommMon AddMon` in the category `AddMon`. In the\nfollowing, we will show that this has the structure of a _commutative_ additive monoid."]
abbrev m : Mon :=
  Mon.FilteredColimits.colimit (F ⋙ forget₂ CommMon Mon.{max v u})
#align CommMon.filtered_colimits.M CommMon.FilteredColimits.m
#align AddCommMon.filtered_colimits.M AddCommMon.FilteredColimits.m

@[to_additive]
instance colimitCommMonoid : CommMonoid M :=
  { M.Monoid with
    mul_comm := fun x y => by
      apply Quot.induction_on₂ x y; clear x y; intro x y
      let k := max' x.1 y.1
      let f := left_to_max x.1 y.1
      let g := right_to_max x.1 y.1
      rw [colimit_mul_mk_eq _ x y k f g, colimit_mul_mk_eq _ y x k g f]
      dsimp
      rw [mul_comm] }
#align CommMon.filtered_colimits.colimit_comm_monoid CommMon.FilteredColimits.colimitCommMonoid
#align AddCommMon.filtered_colimits.colimit_add_comm_monoid AddCommMon.FilteredColimits.colimitAddCommMonoid

/-- The bundled commutative monoid giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative monoid giving the filtered colimit of a diagram."]
def colimit : CommMon :=
  CommMon.of M
#align CommMon.filtered_colimits.colimit CommMon.FilteredColimits.colimit
#align AddCommMon.filtered_colimits.colimit AddCommMon.FilteredColimits.colimit

/-- The cocone over the proposed colimit commutative monoid. -/
@[to_additive "The cocone over the proposed colimit additive commutative monoid."]
def colimitCocone : cocone F where
  x := colimit
  ι := { (Mon.FilteredColimits.colimitCocone (F ⋙ forget₂ CommMon Mon.{max v u})).ι with }
#align CommMon.filtered_colimits.colimit_cocone CommMon.FilteredColimits.colimitCocone
#align AddCommMon.filtered_colimits.colimit_cocone AddCommMon.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `CommMon`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommMon`."]
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc t :=
    Mon.FilteredColimits.colimitDesc (F ⋙ forget₂ CommMon Mon.{max v u})
      ((forget₂ CommMon Mon.{max v u}).mapCocone t)
  fac' t j :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommMon)).fac ((forget CommMon).mapCocone t) j
  uniq' t m h :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommMon)).uniq ((forget CommMon).mapCocone t) m
        fun j => funext fun x => MonoidHom.congr_fun (h j) x
#align CommMon.filtered_colimits.colimit_cocone_is_colimit CommMon.FilteredColimits.colimitCoconeIsColimit
#align AddCommMon.filtered_colimits.colimit_cocone_is_colimit AddCommMon.FilteredColimits.colimit_cocone_is_colimit

@[to_additive forget₂_AddMon_preserves_filtered_colimits]
instance forget₂MonPreservesFilteredColimits : PreservesFilteredColimits (forget₂ CommMon Mon.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (Mon.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommMon Mon.{u})) }
#align CommMon.filtered_colimits.forget₂_Mon_preserves_filtered_colimits CommMon.FilteredColimits.forget₂MonPreservesFilteredColimits
#align AddCommMon.filtered_colimits.forget₂_AddMon_preserves_filtered_colimits AddCommMon.FilteredColimits.forget₂_AddMon_preserves_filtered_colimits

@[to_additive]
instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommMon.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommMon Mon) (forget Mon)
#align CommMon.filtered_colimits.forget_preserves_filtered_colimits CommMon.FilteredColimits.forgetPreservesFilteredColimits
#align AddCommMon.filtered_colimits.forget_preserves_filtered_colimits AddCommMon.FilteredColimits.forget_preserves_filtered_colimits

end

end CommMon.FilteredColimits

