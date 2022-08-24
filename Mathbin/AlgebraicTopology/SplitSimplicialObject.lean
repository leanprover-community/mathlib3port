/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.SimplicialObject
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts

/-!

# Split simplicial objects

In this file, we introduce the notion of split simplicial object.
If `C` is a category that has finite coproducts, a splitting
`s : splitting X` of a simplical object `X` in `C` consists
of the datum of a sequence of objects `s.N : ℕ → C` and a
sequence of morphisms `s.ι n : s.N n → X _[n]` that have
the property that a certain canonical map identifies `X _[n]`
with the coproduct of objects `s.N i` indexed by all possible
epimorphisms `[n] ⟶ [i]` in `simplex_category`. (We do not
assume that the morphisms `s.ι n` are monomorphisms: in the
most common categories, this would be a consequence of the
axioms.)

## References
* [Stacks: Splitting simplicial objects] https://stacks.math.columbia.edu/tag/017O

-/


noncomputable section

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits

open Opposite

open Simplicial

universe u

variable {C : Type _} [Category C]

namespace SimplicialObject

namespace Splitting

/-- The index set which appears in the definition of split simplicial objects. -/
def IndexSet (Δ : SimplexCategoryᵒᵖ) :=
  ΣΔ' : SimplexCategoryᵒᵖ, { α : Δ.unop ⟶ Δ'.unop // Epi α }

namespace IndexSet

/-- The element in `splitting.index_set Δ` attached to an epimorphism `f : Δ ⟶ Δ'`. -/
@[simps]
def mk {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') [Epi f] : IndexSet (op Δ) :=
  ⟨op Δ', f, inferInstance⟩

variable {Δ' Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)

/-- The epimorphism in `simplex_category` associated to `A : splitting.index_set Δ` -/
def e :=
  A.2.1

instance : Epi A.e :=
  A.2.2

theorem ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := by
  tidy

theorem ext (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1)
    (h₂ :
      A₁.e ≫
          eqToHom
            (by
              rw [h₁]) =
        A₂.e) :
    A₁ = A₂ := by
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩
  simp only at h₁
  subst h₁
  simp only [eq_to_hom_refl, comp_id, index_set.e] at h₂
  simp only [h₂]

instance : Fintype (IndexSet Δ) :=
  Fintype.ofInjective
    (fun A =>
      ⟨⟨A.1.unop.len, Nat.lt_succ_iffₓ.mpr (SimplexCategory.len_le_of_epi (inferInstance : Epi A.e))⟩, A.e.toOrderHom⟩ :
      IndexSet Δ → Sigma fun k : Finₓ (Δ.unop.len + 1) => Finₓ (Δ.unop.len + 1) → Finₓ (k + 1))
    (by
      rintro ⟨Δ₁, α₁⟩ ⟨Δ₂, α₂⟩ h₁
      induction Δ₁ using Opposite.rec
      induction Δ₂ using Opposite.rec
      simp only at h₁
      have h₂ : Δ₁ = Δ₂ := by
        ext1
        simpa only [Subtype.mk_eq_mk] using h₁.1
      subst h₂
      refine' ext _ _ rfl _
      ext : 2
      exact eq_of_heq h₁.2)

variable (Δ)

/-- The distinguished element in `splitting.index_set Δ` which corresponds to the
identity of `Δ`. -/
def id : IndexSet Δ :=
  ⟨Δ,
    ⟨𝟙 _, by
      infer_instance⟩⟩

instance : Inhabited (IndexSet Δ) :=
  ⟨id Δ⟩

end IndexSet

variable (N : ℕ → C) (Δ : SimplexCategoryᵒᵖ) (X : SimplicialObject C) (φ : ∀ n, N n ⟶ X _[n])

/-- Given a sequences of objects `N : ℕ → C` in a category `C`, this is
a family of objects indexed by the elements `A : splitting.index_set Δ`.
The `Δ`-simplices of a split simplicial objects shall identify to the
coproduct of objects in such a family. -/
@[simp, nolint unused_arguments]
def summand (A : IndexSet Δ) : C :=
  N A.1.unop.len

variable [HasFiniteCoproducts C]

/-- The coproduct of the family `summand N Δ` -/
@[simp]
def coprod :=
  ∐ summand N Δ

variable {Δ}

/-- The inclusion of a summand in the coproduct. -/
@[simp]
def ιCoprod (A : IndexSet Δ) : N A.1.unop.len ⟶ coprod N Δ :=
  Sigma.ι _ A

variable {N}

/-- The canonical morphism `coprod N Δ ⟶ X.obj Δ` attached to a sequence
of objects `N` and a sequence of morphisms `N n ⟶ X _[n]`. -/
@[simp]
def map (Δ : SimplexCategoryᵒᵖ) : coprod N Δ ⟶ X.obj Δ :=
  Sigma.desc fun A => φ A.1.unop.len ≫ X.map A.e.op

end Splitting

variable [HasFiniteCoproducts C]

/-- A splitting of a simplicial object `X` consists of the datum of a sequence
of objects `N`, a sequence of morphisms `ι : N n ⟶ X _[n]` such that
for all `Δ : simplex_categoryhᵒᵖ`, the canonical map `splitting.map X ι Δ`
is an isomorphism. -/
@[nolint has_nonempty_instance]
structure Splitting (X : SimplicialObject C) where
  n : ℕ → C
  ι : ∀ n, N n ⟶ X _[n]
  map_is_iso' : ∀ Δ : SimplexCategoryᵒᵖ, IsIso (Splitting.map X ι Δ)

namespace Splitting

variable {X Y : SimplicialObject C} (s : Splitting X)

instance map_is_iso (Δ : SimplexCategoryᵒᵖ) : IsIso (Splitting.map X s.ι Δ) :=
  s.map_is_iso' Δ

/-- The isomorphism on simplices given by the axiom `splitting.map_is_iso'` -/
@[simps]
def iso (Δ : SimplexCategoryᵒᵖ) : coprod s.n Δ ≅ X.obj Δ :=
  asIso (Splitting.map X s.ι Δ)

/-- Via the isomorphism `s.iso Δ`, this is the inclusion of a summand
in the direct sum decomposition given by the splitting `s : splitting X`. -/
def ιSummand {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) : s.n A.1.unop.len ⟶ X.obj Δ :=
  Splitting.ιCoprod s.n A ≫ (s.Iso Δ).Hom

@[reassoc]
theorem ι_summand_eq {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) : s.ιSummand A = s.ι A.1.unop.len ≫ X.map A.e.op := by
  dsimp' only [ι_summand, iso.hom]
  erw [colimit.ι_desc, cofan.mk_ι_app]

theorem ι_summand_id (n : ℕ) : s.ιSummand (IndexSet.id (op [n])) = s.ι n := by
  erw [ι_summand_eq, X.map_id, comp_id]
  rfl

/-- As it is stated in `splitting.hom_ext`, a morphism `f : X ⟶ Y` from a split
simplicial object to any simplicial object is determined by its restrictions
`s.φ f n : s.N n ⟶ Y _[n]` to the distinguished summands in each degree `n`. -/
@[simp]
def φ (f : X ⟶ Y) (n : ℕ) : s.n n ⟶ Y _[n] :=
  s.ι n ≫ f.app (op [n])

@[simp, reassoc]
theorem ι_summand_comp_app (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    s.ιSummand A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op := by
  simp only [ι_summand_eq_assoc, φ, nat_trans.naturality, assoc]

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `discrete_cases #[]
theorem hom_ext' {Z : C} {Δ : SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
    (h : ∀ A : IndexSet Δ, s.ιSummand A ≫ f = s.ιSummand A ≫ g) : f = g := by
  rw [← cancel_epi (s.iso Δ).Hom]
  ext A
  trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `discrete_cases #[]"
  simpa only [ι_summand_eq, iso_hom, colimit.ι_desc_assoc, cofan.mk_ι_app, assoc] using h A

theorem hom_ext (f g : X ⟶ Y) (h : ∀ n : ℕ, s.φ f n = s.φ g n) : f = g := by
  ext Δ
  apply s.hom_ext'
  intro A
  induction Δ using Opposite.rec
  induction' Δ using SimplexCategory.rec with n
  dsimp'
  simp only [s.ι_summand_comp_app, h]

/-- The map `X.obj Δ ⟶ Z` obtained by providing a family of morphisms on all the
terms of decomposition given by a splitting `s : splitting X`  -/
def desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : ∀ A : IndexSet Δ, s.n A.1.unop.len ⟶ Z) : X.obj Δ ⟶ Z :=
  (s.Iso Δ).inv ≫ Sigma.desc F

@[simp, reassoc]
theorem ι_desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : ∀ A : IndexSet Δ, s.n A.1.unop.len ⟶ Z) (A : IndexSet Δ) :
    s.ιSummand A ≫ s.desc Δ F = F A := by
  dsimp' only [ι_summand, desc]
  simp only [assoc, iso.hom_inv_id_assoc, ι_coprod]
  erw [colimit.ι_desc, cofan.mk_ι_app]

end Splitting

end SimplicialObject

