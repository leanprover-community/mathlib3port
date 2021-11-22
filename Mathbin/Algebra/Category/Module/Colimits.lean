import Mathbin.Algebra.Category.Module.Basic 
import Mathbin.GroupTheory.QuotientGroup 
import Mathbin.CategoryTheory.Limits.ConcreteCategory 
import Mathbin.CategoryTheory.Limits.Shapes.Kernels 
import Mathbin.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# The category of R-modules has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.

Note that finite colimits can already be obtained from the instance `abelian (Module R)`.

TODO:
In fact, in `Module R` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

variable{R : Type v}[Ringₓ R]

namespace ModuleCat.Colimits

/-!
We build the colimit of a diagram in `Module` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/


variable{J : Type v}[small_category J](F : J ⥤ ModuleCat.{v} R)

/--
An inductive type representing all module expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
  | of : ∀ j : J x : F.obj j, prequotient
  | zero : prequotient
  | neg : prequotient → prequotient
  | add : prequotient → prequotient → prequotient
  | smul : R → prequotient → prequotient

instance  : Inhabited (prequotient F) :=
  ⟨prequotient.zero⟩

open Prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the module laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive relation : prequotient F → prequotient F → Prop
  | refl : ∀ x, relation x x
  | symm : ∀ x y h : relation x y, relation y x
  | trans : ∀ x y z h : relation x y k : relation y z, relation x z
  | map : ∀ j j' : J f : j ⟶ j' x : F.obj j, relation (of j' (F.map f x)) (of j x)
  | zero : ∀ j, relation (of j 0) zero
  | neg : ∀ j x : F.obj j, relation (of j (-x)) (neg (of j x))
  | add : ∀ j x y : F.obj j, relation (of j (x+y)) (add (of j x) (of j y))
  | smul : ∀ j s x : F.obj j, relation (of j (s • x)) (smul s (of j x))
  | neg_1 : ∀ x x' r : relation x x', relation (neg x) (neg x')
  | add_1 : ∀ x x' y r : relation x x', relation (add x y) (add x' y)
  | add_2 : ∀ x y y' r : relation y y', relation (add x y) (add x y')
  | smul_1 : ∀ s x x' r : relation x x', relation (smul s x) (smul s x')
  | zero_addₓ : ∀ x, relation (add zero x) x
  | add_zeroₓ : ∀ x, relation (add x zero) x
  | add_left_negₓ : ∀ x, relation (add (neg x) x) zero
  | add_commₓ : ∀ x y, relation (add x y) (add y x)
  | add_assocₓ : ∀ x y z, relation (add (add x y) z) (add x (add y z))
  | one_smul : ∀ x, relation (smul 1 x) x
  | mul_smul : ∀ s t x, relation (smul (s*t) x) (smul s (smul t x))
  | smul_add : ∀ s x y, relation (smul s (add x y)) (add (smul s x) (smul s y))
  | smul_zero : ∀ s, relation (smul s zero) zero
  | add_smul : ∀ s t x, relation (smul (s+t) x) (add (smul s x) (smul t x))
  | zero_smul : ∀ x, relation (smul 0 x) zero

/--
The setoid corresponding to module expressions modulo module relations and identifications.
-/
def colimit_setoid : Setoidₓ (prequotient F) :=
  { R := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }

attribute [instance] colimit_setoid

-- error in Algebra.Category.Module.Colimits: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler inhabited
/--
The underlying type of the colimit of a diagram in `Module R`.
-/ @[derive #[expr inhabited]] def colimit_type : Type v :=
quotient (colimit_setoid F)

instance  : AddCommGroupₓ (colimit_type F) :=
  { zero :=
      by 
        exact Quot.mk _ zero,
    neg :=
      by 
        fapply @Quot.lift
        ·
          intro x 
          exact Quot.mk _ (neg x)
        ·
          intro x x' r 
          apply Quot.sound 
          exact relation.neg_1 _ _ r,
    add :=
      by 
        fapply @Quot.lift _ _ (colimit_type F → colimit_type F)
        ·
          intro x 
          fapply @Quot.lift
          ·
            intro y 
            exact Quot.mk _ (add x y)
          ·
            intro y y' r 
            apply Quot.sound 
            exact relation.add_2 _ _ _ r
        ·
          intro x x' r 
          funext y 
          induction y 
          dsimp 
          apply Quot.sound
          ·
            exact relation.add_1 _ _ _ r
          ·
            rfl,
    zero_add :=
      fun x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.zero_add 
          rfl,
    add_zero :=
      fun x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.add_zero 
          rfl,
    add_left_neg :=
      fun x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.add_left_neg 
          rfl,
    add_comm :=
      fun x y =>
        by 
          induction x 
          induction y 
          dsimp 
          apply Quot.sound 
          apply relation.add_comm 
          rfl 
          rfl,
    add_assoc :=
      fun x y z =>
        by 
          induction x 
          induction y 
          induction z 
          dsimp 
          apply Quot.sound 
          apply relation.add_assoc 
          rfl 
          rfl 
          rfl }

instance  : Module R (colimit_type F) :=
  { smul :=
      fun s =>
        by 
          fapply @Quot.lift
          ·
            intro x 
            exact Quot.mk _ (smul s x)
          ·
            intro x x' r 
            apply Quot.sound 
            exact relation.smul_1 s _ _ r,
    one_smul :=
      fun x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.one_smul 
          rfl,
    mul_smul :=
      fun s t x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.mul_smul 
          rfl,
    smul_add :=
      fun s x y =>
        by 
          induction x 
          induction y 
          dsimp 
          apply Quot.sound 
          apply relation.smul_add 
          rfl 
          rfl,
    smul_zero :=
      fun s =>
        by 
          apply Quot.sound 
          apply relation.smul_zero,
    add_smul :=
      fun s t x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.add_smul 
          rfl,
    zero_smul :=
      fun x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.zero_smul 
          rfl }

@[simp]
theorem quot_zero : Quot.mk Setoidₓ.R zero = (0 : colimit_type F) :=
  rfl

@[simp]
theorem quot_neg x : Quot.mk Setoidₓ.R (neg x) = (-Quot.mk Setoidₓ.R x : colimit_type F) :=
  rfl

@[simp]
theorem quot_add x y : Quot.mk Setoidₓ.R (add x y) = (Quot.mk Setoidₓ.R x+Quot.mk Setoidₓ.R y : colimit_type F) :=
  rfl

@[simp]
theorem quot_smul s x : Quot.mk Setoidₓ.R (smul s x) = (s • Quot.mk Setoidₓ.R x : colimit_type F) :=
  rfl

/-- The bundled module giving the colimit of a diagram. -/
def colimit : ModuleCat R :=
  ModuleCat.of R (colimit_type F)

/-- The function from a given module in the diagram to the colimit module. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
  Quot.mk _ (of j x)

/-- The group homomorphism from a given module in the diagram to the colimit module. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
  { toFun := cocone_fun F j,
    map_smul' :=
      by 
        intros 
        apply Quot.sound 
        apply relation.smul,
    map_add' :=
      by 
        intros  <;> apply Quot.sound <;> apply relation.add }

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') : F.map f ≫ cocone_morphism F j' = cocone_morphism F j :=
  by 
    ext 
    apply Quot.sound 
    apply Relation.Map

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
  (cocone_morphism F j') (F.map f x) = (cocone_morphism F j) x :=
  by 
    rw [←cocone_naturality F f]
    rfl

/-- The cocone over the proposed colimit module. -/
def colimit_cocone : cocone F :=
  { x := colimit F, ι := { app := cocone_morphism F } }

/-- The function from the free module on the diagram to the cone point of any other cocone. -/
@[simp]
def desc_fun_lift (s : cocone F) : prequotient F → s.X
| of j x => (s.ι.app j) x
| zero => 0
| neg x => -desc_fun_lift x
| add x y => desc_fun_lift x+desc_fun_lift y
| smul s x => s • desc_fun_lift x

/-- The function from the colimit module to the cone point of any other cocone. -/
def desc_fun (s : cocone F) : colimit_type F → s.X :=
  by 
    fapply Quot.lift
    ·
      exact desc_fun_lift F s
    ·
      intro x y r 
      induction r <;>
        try 
          dsimp
      ·
        rfl
      ·
        exact r_ih.symm
      ·
        exact Eq.trans r_ih_h r_ih_k
      ·
        simp 
      ·
        simp 
      ·
        simp 
      ·
        simp 
      ·
        simp 
      ·
        rw [r_ih]
      ·
        rw [r_ih]
      ·
        rw [r_ih]
      ·
        rw [r_ih]
      ·
        rw [zero_addₓ]
      ·
        rw [add_zeroₓ]
      ·
        rw [add_left_negₓ]
      ·
        rw [add_commₓ]
      ·
        rw [add_assocₓ]
      ·
        rw [one_smul]
      ·
        rw [mul_smul]
      ·
        rw [smul_add]
      ·
        rw [smul_zero]
      ·
        rw [add_smul]
      ·
        rw [zero_smul]

/-- The group homomorphism from the colimit module to the cone point of any other cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
  { toFun := desc_fun F s,
    map_smul' :=
      fun s x =>
        by 
          induction x <;> rfl,
    map_add' :=
      fun x y =>
        by 
          induction x <;> induction y <;> rfl }

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_cocone_is_colimit : is_colimit (colimit_cocone F) :=
  { desc := fun s => desc_morphism F s,
    uniq' :=
      fun s m w =>
        by 
          ext 
          induction x 
          induction x
          ·
            have w' := congr_funₓ (congr_argₓ (fun f : F.obj x_j ⟶ s.X => (f : F.obj x_j → s.X)) (w x_j)) x_x 
            erw [w']
            rfl
          ·
            simp 
          ·
            simp 
          ·
            simp 
          ·
            simp 
          rfl }

instance has_colimits_Module : has_colimits (ModuleCat R) :=
  { HasColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exactI
            { HasColimit :=
                fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_cocone_is_colimit F } } }

end ModuleCat.Colimits

