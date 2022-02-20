/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.Algebra.Group.Hom
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Module.Basic
import Mathbin.CategoryTheory.Endomorphism

/-!
# Preadditive categories

A preadditive category is a category in which `X ⟶ Y` is an abelian group in such a way that
composition of morphisms is linear in both variables.

This file contains a definition of preadditive category that directly encodes the definition given
above. The definition could also be phrased as follows: A preadditive category is a category
enriched over the category of Abelian groups. Once the general framework to state this in Lean is
available, the contents of this file should become obsolete.

## Main results

* Definition of preadditive categories and basic properties
* In a preadditive category, `f : Q ⟶ R` is mono if and only if `g ≫ f = 0 → g = 0` for all
  composable `g`.
* A preadditive category with kernels has equalizers.

## Implementation notes

The simp normal form for negation and composition is to push negations as far as possible to
the outside. For example, `f ≫ (-g)` and `(-f) ≫ g` both become `-(f ≫ g)`, and `(-f) ≫ (-g)`
is simplified to `f ≫ g`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

## Tags

additive, preadditive, Hom group, Ab-category, Ab-enriched
-/


universe v u

open CategoryTheory.Limits

open_locale BigOperators

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroupₓ (P ⟶ Q) := by
    run_tac
      tactic.apply_instance
  add_comp' : ∀ P Q R : C f f' : P ⟶ Q g : Q ⟶ R, (f + f') ≫ g = f ≫ g + f' ≫ g := by
    run_tac
      obviously
  comp_add' : ∀ P Q R : C f : P ⟶ Q g g' : Q ⟶ R, f ≫ (g + g') = f ≫ g + f ≫ g' := by
    run_tac
      obviously

attribute [instance] preadditive.hom_group

restate_axiom preadditive.add_comp'

restate_axiom preadditive.comp_add'

attribute [simp, reassoc] preadditive.add_comp

attribute [reassoc] preadditive.comp_add

-- (the linter doesn't like `simp` on this lemma)
attribute [simp] preadditive.comp_add

end CategoryTheory

open CategoryTheory

namespace CategoryTheory

namespace Preadditive

section Preadditive

open AddMonoidHom

variable {C : Type u} [Category.{v} C] [Preadditive C]

section InducedCategory

universe u'

variable {C} {D : Type u'} (F : D → C)

instance InducedCategory.category : Preadditive.{v} (InducedCategory C F) where
  homGroup := fun P Q => @Preadditive.homGroup C _ _ (F P) (F Q)
  add_comp' := fun P Q R f f' g => add_comp' _ _ _ _ _ _
  comp_add' := fun P Q R f g g' => comp_add' _ _ _ _ _ _

end InducedCategory

instance (X : C) : AddCommGroupₓ (End X) := by
  dsimp [End]
  infer_instance

instance (X : C) : Ringₓ (End X) :=
  { (inferInstance : AddCommGroupₓ (End X)), (inferInstance : Monoidₓ (End X)) with
    left_distrib := fun f g h => Preadditive.add_comp X X X g h f,
    right_distrib := fun f g h => Preadditive.comp_add X X X h f g }

/-- Composition by a fixed left argument as a group homomorphism -/
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  (mk' fun g => f ≫ g) fun g g' => by
    simp

/-- Composition by a fixed right argument as a group homomorphism -/
def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  (mk' fun f => f ≫ g) fun f f' => by
    simp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

/-- Composition as a bilinear group homomorphism -/
def compHom : (P ⟶ Q) →+ (Q ⟶ R) →+ (P ⟶ R) :=
  (AddMonoidHom.mk' fun f => leftComp _ f) fun f₁ f₂ => AddMonoidHom.ext fun g => (rightComp _ g).map_add f₁ f₂

@[simp, reassoc]
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (leftComp R f) g g'

@[simp, reassoc]
theorem neg_comp : -f ≫ g = -(f ≫ g) :=
  map_neg (rightComp P g) f

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem comp_neg : f ≫ -g = -(f ≫ g) :=
  map_neg (leftComp R f) g

@[reassoc]
theorem neg_comp_neg : -f ≫ -g = f ≫ g := by
  simp

theorem nsmul_comp (n : ℕ) : (n • f) ≫ g = n • f ≫ g :=
  map_nsmul (rightComp P g) f n

theorem comp_nsmul (n : ℕ) : f ≫ (n • g) = n • f ≫ g :=
  map_nsmul (leftComp R f) g n

theorem zsmul_comp (n : ℤ) : (n • f) ≫ g = n • f ≫ g :=
  map_zsmul (rightComp P g) f n

theorem comp_zsmul (n : ℤ) : f ≫ (n • g) = n • f ≫ g :=
  map_zsmul (leftComp R f) g n

@[reassoc]
theorem comp_sum {P Q R : C} {J : Type _} (s : Finset J) (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
    (f ≫ ∑ j in s, g j) = ∑ j in s, f ≫ g j :=
  map_sum (leftComp R f) _ _

@[reassoc]
theorem sum_comp {P Q R : C} {J : Type _} (s : Finset J) (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
    (∑ j in s, f j) ≫ g = ∑ j in s, f j ≫ g :=
  map_sum (rightComp P g) _ _

instance {P Q : C} {f : P ⟶ Q} [Epi f] : Epi (-f) :=
  ⟨fun R g g' H => by
    rwa [neg_comp, neg_comp, ← comp_neg, ← comp_neg, cancel_epi, neg_inj] at H⟩

instance {P Q : C} {f : P ⟶ Q} [Mono f] : Mono (-f) :=
  ⟨fun R g g' H => by
    rwa [comp_neg, comp_neg, ← neg_comp, ← neg_comp, cancel_mono, neg_inj] at H⟩

instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  HasZero := inferInstance
  comp_zero' := fun P Q f R => show leftComp R f 0 = 0 from map_zero _
  zero_comp' := fun P Q R f => show rightComp P f 0 = 0 from map_zero _

instance moduleEndRight {X Y : C} : Module (End Y) (X ⟶ Y) where
  smul_add := fun r f g => add_comp _ _ _ _ _ _
  smul_zero := fun r => zero_comp
  add_smul := fun r s f => comp_add _ _ _ _ _ _
  zero_smul := fun r => comp_zero

theorem mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : ∀ {P : C} g : P ⟶ Q, g ≫ f = 0 → g = 0) : Mono f :=
  ⟨fun P g g' hg => sub_eq_zero.1 <| h _ <| (map_sub (rightComp P f) g g').trans <| sub_eq_zero.2 hg⟩

theorem mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) : Mono f ↔ ∀ P : C g : P ⟶ Q, g ≫ f = 0 → g = 0 :=
  ⟨fun m P g => zero_of_comp_mono _, mono_of_cancel_zero f⟩

theorem mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)] (w : kernel.ι f = 0) : Mono f :=
  mono_of_cancel_zero f fun P g h => by
    rw [← kernel.lift_ι f g h, w, limits.comp_zero]

theorem epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : ∀ {R : C} g : Q ⟶ R, f ≫ g = 0 → g = 0) : Epi f :=
  ⟨fun R g g' hg => sub_eq_zero.1 <| h _ <| (map_sub (leftComp R f) g g').trans <| sub_eq_zero.2 hg⟩

theorem epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) : Epi f ↔ ∀ R : C g : Q ⟶ R, f ≫ g = 0 → g = 0 :=
  ⟨fun e R g => zero_of_epi_comp _, epi_of_cancel_zero f⟩

theorem epi_of_cokernel_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)] (w : cokernel.π f = 0) : Epi f :=
  epi_of_cancel_zero f fun P g h => by
    rw [← cokernel.π_desc f g h, w, limits.zero_comp]

open_locale ZeroObject

variable [HasZeroObject C]

theorem mono_of_kernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)] (w : kernel f ≅ 0) : Mono f :=
  mono_of_kernel_zero (zero_of_source_iso_zero _ w)

theorem epi_of_cokernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)] (w : cokernel f ≅ 0) : Epi f :=
  epi_of_cokernel_zero (zero_of_target_iso_zero _ w)

end Preadditive

section Equalizers

variable {C : Type u} [Category.{v} C] [Preadditive C]

section

variable {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
theorem has_limit_parallel_pair [HasKernel (f - g)] : HasLimit (parallelPair f g) :=
  HasLimit.mk
    { Cone :=
        Fork.ofι (kernel.ι (f - g))
          (sub_eq_zero.1 <| by
            rw [← comp_sub]
            exact kernel.condition _),
      IsLimit :=
        Fork.IsLimit.mk _
          (fun s =>
            kernel.lift (f - g) (Fork.ι s) <| by
              rw [comp_sub]
              apply sub_eq_zero.2
              exact fork.condition _)
          (fun s => by
            simp )
          fun s m h => by
          ext
          simpa using h walking_parallel_pair.zero }

/-- Conversely, an equalizer of `f` and `g` is a kernel of `f - g`. -/
theorem has_kernel_of_has_equalizer [HasEqualizer f g] : HasKernel (f - g) :=
  HasLimit.mk
    { Cone :=
        Fork.ofι (equalizer.ι f g)
          (by
            erw [comp_zero, comp_sub, equalizer.condition f g, sub_self]),
      IsLimit :=
        Fork.IsLimit.mk _
          (fun s =>
            equalizer.lift s.ι
              (by
                simpa only [comp_sub, comp_zero, sub_eq_zero] using s.condition))
          (fun s => by
            simp only [fork.ι_eq_app_zero, fork.of_ι_π_app, equalizer.lift_ι])
          fun s m h => by
          ext
          simpa only [equalizer.lift_ι] using h walking_parallel_pair.zero }

end

section

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
theorem has_equalizers_of_has_kernels [HasKernels C] : HasEqualizers C :=
  @has_equalizers_of_has_limit_parallel_pair _ _ fun _ _ f g => has_limit_parallel_pair f g

end

section

variable {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
theorem has_colimit_parallel_pair [HasCokernel (f - g)] : HasColimit (parallelPair f g) :=
  HasColimit.mk
    { Cocone :=
        Cofork.ofπ (cokernel.π (f - g))
          (sub_eq_zero.1 <| by
            rw [← sub_comp]
            exact cokernel.condition _),
      IsColimit :=
        Cofork.IsColimit.mk _
          (fun s =>
            cokernel.desc (f - g) (Cofork.π s) <| by
              rw [sub_comp]
              apply sub_eq_zero.2
              exact cofork.condition _)
          (fun s => by
            simp )
          fun s m h => by
          ext
          simpa using h walking_parallel_pair.one }

end

section

/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
theorem has_coequalizers_of_has_cokernels [HasCokernels C] : HasCoequalizers C :=
  @has_coequalizers_of_has_colimit_parallel_pair _ _ fun _ _ f g => has_colimit_parallel_pair f g

end

end Equalizers

end Preadditive

end CategoryTheory

