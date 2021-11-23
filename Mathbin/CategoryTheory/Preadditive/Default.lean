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

variable(C : Type u)[category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class preadditive where 
  homGroup : ∀ P Q : C, AddCommGroupₓ (P ⟶ Q) :=  by 
  runTac 
    tactic.apply_instance 
  add_comp' : ∀ P Q R : C f f' : P ⟶ Q g : Q ⟶ R, (f+f') ≫ g = (f ≫ g)+f' ≫ g :=  by 
  runTac 
    obviously 
  comp_add' : ∀ P Q R : C f : P ⟶ Q g g' : Q ⟶ R, (f ≫ g+g') = (f ≫ g)+f ≫ g' :=  by 
  runTac 
    obviously

attribute [instance] preadditive.hom_group

restate_axiom preadditive.add_comp'

restate_axiom preadditive.comp_add'

attribute [simp, reassoc] preadditive.add_comp

attribute [reassoc] preadditive.comp_add

attribute [simp] preadditive.comp_add

end CategoryTheory

open CategoryTheory

namespace CategoryTheory

namespace Preadditive

section Preadditive

open AddMonoidHom

variable{C : Type u}[category.{v} C][preadditive C]

section InducedCategory

universe u'

variable{C}{D : Type u'}(F : D → C)

instance induced_category.category : preadditive.{v} (induced_category C F) :=
  { homGroup := fun P Q => @preadditive.hom_group C _ _ (F P) (F Q),
    add_comp' := fun P Q R f f' g => add_comp' _ _ _ _ _ _, comp_add' := fun P Q R f g g' => comp_add' _ _ _ _ _ _ }

end InducedCategory

instance  (X : C) : AddCommGroupₓ (End X) :=
  by 
    dsimp [End]
    infer_instance

instance  (X : C) : Ringₓ (End X) :=
  { (inferInstance : AddCommGroupₓ (End X)), (inferInstance : Monoidₓ (End X)) with
    left_distrib := fun f g h => preadditive.add_comp X X X g h f,
    right_distrib := fun f g h => preadditive.comp_add X X X h f g }

/-- Composition by a fixed left argument as a group homomorphism -/
def left_comp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  (mk' fun g => f ≫ g)$
    fun g g' =>
      by 
        simp 

/-- Composition by a fixed right argument as a group homomorphism -/
def right_comp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  (mk' fun f => f ≫ g)$
    fun f f' =>
      by 
        simp 

variable{P Q R : C}(f f' : P ⟶ Q)(g g' : Q ⟶ R)

/-- Composition as a bilinear group homomorphism -/
def comp_hom : (P ⟶ Q) →+ (Q ⟶ R) →+ (P ⟶ R) :=
  (AddMonoidHom.mk' fun f => left_comp _ f)$ fun f₁ f₂ => AddMonoidHom.ext$ fun g => (right_comp _ g).map_add f₁ f₂

@[simp, reassoc]
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (right_comp P g) f f'

@[reassoc, simp]
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (left_comp R f) g g'

@[simp, reassoc]
theorem neg_comp : -f ≫ g = -(f ≫ g) :=
  map_neg (right_comp _ _) _

@[reassoc, simp]
theorem comp_neg : f ≫ -g = -(f ≫ g) :=
  map_neg (left_comp _ _) _

@[reassoc]
theorem neg_comp_neg : -f ≫ -g = f ≫ g :=
  by 
    simp 

theorem nsmul_comp (n : ℕ) : (n • f) ≫ g = n • f ≫ g :=
  map_nsmul (right_comp _ _) _ _

theorem comp_nsmul (n : ℕ) : f ≫ (n • g) = n • f ≫ g :=
  map_nsmul (left_comp _ _) _ _

theorem zsmul_comp (n : ℤ) : (n • f) ≫ g = n • f ≫ g :=
  map_zsmul (right_comp _ _) _ _

theorem comp_zsmul (n : ℤ) : f ≫ (n • g) = n • f ≫ g :=
  map_zsmul (left_comp _ _) _ _

@[reassoc]
theorem comp_sum {P Q R : C} {J : Type _} (s : Finset J) (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
  (f ≫ ∑j in s, g j) = ∑j in s, f ≫ g j :=
  map_sum (left_comp R f) _ _

@[reassoc]
theorem sum_comp {P Q R : C} {J : Type _} (s : Finset J) (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
  (∑j in s, f j) ≫ g = ∑j in s, f j ≫ g :=
  map_sum (right_comp P g) _ _

instance  {P Q : C} {f : P ⟶ Q} [epi f] : epi (-f) :=
  ⟨fun R g g' H =>
      by 
        rwa [neg_comp, neg_comp, ←comp_neg, ←comp_neg, cancel_epi, neg_inj] at H⟩

instance  {P Q : C} {f : P ⟶ Q} [mono f] : mono (-f) :=
  ⟨fun R g g' H =>
      by 
        rwa [comp_neg, comp_neg, ←neg_comp, ←neg_comp, cancel_mono, neg_inj] at H⟩

instance (priority := 100)preadditive_has_zero_morphisms : has_zero_morphisms C :=
  { HasZero := inferInstance, comp_zero' := fun P Q f R => map_zero$ left_comp R f,
    zero_comp' := fun P Q R f => map_zero$ right_comp P f }

theorem mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : ∀ {P : C} g : P ⟶ Q, g ≫ f = 0 → g = 0) : mono f :=
  ⟨fun P g g' hg => sub_eq_zero.1$ h _$ (map_sub (right_comp P f) g g').trans$ sub_eq_zero.2 hg⟩

theorem mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) : mono f ↔ ∀ P : C g : P ⟶ Q, g ≫ f = 0 → g = 0 :=
  ⟨fun m P g =>
      by 
        exact zero_of_comp_mono _,
    mono_of_cancel_zero f⟩

theorem mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [has_limit (parallel_pair f 0)] (w : kernel.ι f = 0) : mono f :=
  mono_of_cancel_zero f
    fun P g h =>
      by 
        rw [←kernel.lift_ι f g h, w, limits.comp_zero]

theorem epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : ∀ {R : C} g : Q ⟶ R, f ≫ g = 0 → g = 0) : epi f :=
  ⟨fun R g g' hg => sub_eq_zero.1$ h _$ (map_sub (left_comp R f) g g').trans$ sub_eq_zero.2 hg⟩

theorem epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) : epi f ↔ ∀ R : C g : Q ⟶ R, f ≫ g = 0 → g = 0 :=
  ⟨fun e R g =>
      by 
        exact zero_of_epi_comp _,
    epi_of_cancel_zero f⟩

theorem epi_of_cokernel_zero {X Y : C} {f : X ⟶ Y} [has_colimit (parallel_pair f 0)] (w : cokernel.π f = 0) : epi f :=
  epi_of_cancel_zero f
    fun P g h =>
      by 
        rw [←cokernel.π_desc f g h, w, limits.zero_comp]

open_locale ZeroObject

variable[has_zero_object C]

theorem mono_of_kernel_iso_zero {X Y : C} {f : X ⟶ Y} [has_limit (parallel_pair f 0)] (w : kernel f ≅ 0) : mono f :=
  mono_of_kernel_zero (zero_of_source_iso_zero _ w)

theorem epi_of_cokernel_iso_zero {X Y : C} {f : X ⟶ Y} [has_colimit (parallel_pair f 0)] (w : cokernel f ≅ 0) : epi f :=
  epi_of_cokernel_zero (zero_of_target_iso_zero _ w)

end Preadditive

section Equalizers

variable{C : Type u}[category.{v} C][preadditive C]

section 

variable{X Y : C}(f : X ⟶ Y)(g : X ⟶ Y)

/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
theorem has_limit_parallel_pair [has_kernel (f - g)] : has_limit (parallel_pair f g) :=
  has_limit.mk
    { Cone :=
        fork.of_ι (kernel.ι (f - g))
          (sub_eq_zero.1$
            by 
              rw [←comp_sub]
              exact kernel.condition _),
      IsLimit :=
        fork.is_limit.mk _
          (fun s =>
            kernel.lift (f - g) (fork.ι s)$
              by 
                rw [comp_sub]
                apply sub_eq_zero.2 
                exact fork.condition _)
          (fun s =>
            by 
              simp )
          fun s m h =>
            by 
              ext 
              simpa using h walking_parallel_pair.zero }

end 

section 

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
theorem has_equalizers_of_has_kernels [has_kernels C] : has_equalizers C :=
  @has_equalizers_of_has_limit_parallel_pair _ _ fun _ _ f g => has_limit_parallel_pair f g

end 

section 

variable{X Y : C}(f : X ⟶ Y)(g : X ⟶ Y)

/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
theorem has_colimit_parallel_pair [has_cokernel (f - g)] : has_colimit (parallel_pair f g) :=
  has_colimit.mk
    { Cocone :=
        cofork.of_π (cokernel.π (f - g))
          (sub_eq_zero.1$
            by 
              rw [←sub_comp]
              exact cokernel.condition _),
      IsColimit :=
        cofork.is_colimit.mk _
          (fun s =>
            cokernel.desc (f - g) (cofork.π s)$
              by 
                rw [sub_comp]
                apply sub_eq_zero.2 
                exact cofork.condition _)
          (fun s =>
            by 
              simp )
          fun s m h =>
            by 
              ext 
              simpa using h walking_parallel_pair.one }

end 

section 

/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
theorem has_coequalizers_of_has_cokernels [has_cokernels C] : has_coequalizers C :=
  @has_coequalizers_of_has_colimit_parallel_pair _ _ fun _ _ f g => has_colimit_parallel_pair f g

end 

end Equalizers

end Preadditive

end CategoryTheory

