import Mathbin.Algebra.Category.CommRing.Basic 
import Mathbin.CategoryTheory.Limits.HasLimits 
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# The category of commutative rings has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `comm_ring` and `ring_hom`.
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

namespace CommRingₓₓ.Colimits

/-!
We build the colimit of a diagram in `CommRing` by constructing the
free commutative ring on the disjoint union of all the commutative rings in the diagram,
then taking the quotient by the commutative ring laws within each commutative ring,
and the identifications given by the morphisms in the diagram.
-/


variable{J : Type v}[small_category J](F : J ⥤ CommRingₓₓ.{v})

/--
An inductive type representing all commutative ring expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
  | of : ∀ (j : J) (x : F.obj j), prequotient
  | zero : prequotient
  | one : prequotient
  | neg : prequotient → prequotient
  | add : prequotient → prequotient → prequotient
  | mul : prequotient → prequotient → prequotient

instance  : Inhabited (prequotient F) :=
  ⟨prequotient.zero⟩

open Prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the commutative ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive relation : prequotient F → prequotient F → Prop
  | refl : ∀ x, relation x x
  | symm : ∀ x y (h : relation x y), relation y x
  | trans : ∀ x y z (h : relation x y) (k : relation y z), relation x z
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j), relation (of j' (F.map f x)) (of j x)
  | zero : ∀ j, relation (of j 0) zero
  | one : ∀ j, relation (of j 1) one
  | neg : ∀ j (x : F.obj j), relation (of j (-x)) (neg (of j x))
  | add : ∀ j (x y : F.obj j), relation (of j (x+y)) (add (of j x) (of j y))
  | mul : ∀ j (x y : F.obj j), relation (of j (x*y)) (mul (of j x) (of j y))
  | neg_1 : ∀ x x' (r : relation x x'), relation (neg x) (neg x')
  | add_1 : ∀ x x' y (r : relation x x'), relation (add x y) (add x' y)
  | add_2 : ∀ x y y' (r : relation y y'), relation (add x y) (add x y')
  | mul_1 : ∀ x x' y (r : relation x x'), relation (mul x y) (mul x' y)
  | mul_2 : ∀ x y y' (r : relation y y'), relation (mul x y) (mul x y')
  | zero_addₓ : ∀ x, relation (add zero x) x
  | add_zeroₓ : ∀ x, relation (add x zero) x
  | one_mulₓ : ∀ x, relation (mul one x) x
  | mul_oneₓ : ∀ x, relation (mul x one) x
  | add_left_negₓ : ∀ x, relation (add (neg x) x) zero
  | add_commₓ : ∀ x y, relation (add x y) (add y x)
  | mul_commₓ : ∀ x y, relation (mul x y) (mul y x)
  | add_assocₓ : ∀ x y z, relation (add (add x y) z) (add x (add y z))
  | mul_assocₓ : ∀ x y z, relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, relation (mul (add x y) z) (add (mul x z) (mul y z))

/--
The setoid corresponding to commutative expressions modulo monoid relations and identifications.
-/
def colimit_setoid : Setoidₓ (prequotient F) :=
  { R := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }

attribute [instance] colimit_setoid

-- error in Algebra.Category.CommRing.Colimits: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
/--
The underlying type of the colimit of a diagram in `CommRing`.
-/ @[derive #[expr inhabited]] def colimit_type : Type v :=
quotient (colimit_setoid F)

instance  : CommRingₓ (colimit_type F) :=
  { zero :=
      by 
        exact Quot.mk _ zero,
    one :=
      by 
        exact Quot.mk _ one,
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
    mul :=
      by 
        fapply @Quot.lift _ _ (colimit_type F → colimit_type F)
        ·
          intro x 
          fapply @Quot.lift
          ·
            intro y 
            exact Quot.mk _ (mul x y)
          ·
            intro y y' r 
            apply Quot.sound 
            exact relation.mul_2 _ _ _ r
        ·
          intro x x' r 
          funext y 
          induction y 
          dsimp 
          apply Quot.sound
          ·
            exact relation.mul_1 _ _ _ r
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
    one_mul :=
      fun x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.one_mul 
          rfl,
    mul_one :=
      fun x =>
        by 
          induction x 
          dsimp 
          apply Quot.sound 
          apply relation.mul_one 
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
    mul_comm :=
      fun x y =>
        by 
          induction x 
          induction y 
          dsimp 
          apply Quot.sound 
          apply relation.mul_comm 
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
          rfl,
    mul_assoc :=
      fun x y z =>
        by 
          induction x 
          induction y 
          induction z 
          dsimp 
          apply Quot.sound 
          apply relation.mul_assoc 
          rfl 
          rfl 
          rfl,
    left_distrib :=
      fun x y z =>
        by 
          induction x 
          induction y 
          induction z 
          dsimp 
          apply Quot.sound 
          apply relation.left_distrib 
          rfl 
          rfl 
          rfl,
    right_distrib :=
      fun x y z =>
        by 
          induction x 
          induction y 
          induction z 
          dsimp 
          apply Quot.sound 
          apply relation.right_distrib 
          rfl 
          rfl 
          rfl }

@[simp]
theorem quot_zero : Quot.mk Setoidₓ.R zero = (0 : colimit_type F) :=
  rfl

@[simp]
theorem quot_one : Quot.mk Setoidₓ.R one = (1 : colimit_type F) :=
  rfl

@[simp]
theorem quot_neg x : Quot.mk Setoidₓ.R (neg x) = (-Quot.mk Setoidₓ.R x : colimit_type F) :=
  rfl

@[simp]
theorem quot_add x y : Quot.mk Setoidₓ.R (add x y) = (Quot.mk Setoidₓ.R x+Quot.mk Setoidₓ.R y : colimit_type F) :=
  rfl

@[simp]
theorem quot_mul x y : Quot.mk Setoidₓ.R (mul x y) = (Quot.mk Setoidₓ.R x*Quot.mk Setoidₓ.R y : colimit_type F) :=
  rfl

/-- The bundled commutative ring giving the colimit of a diagram. -/
def colimit : CommRingₓₓ :=
  CommRingₓₓ.of (colimit_type F)

/-- The function from a given commutative ring in the diagram to the colimit commutative ring. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
  Quot.mk _ (of j x)

/-- The ring homomorphism from a given commutative ring in the diagram to the colimit commutative
ring. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
  { toFun := cocone_fun F j,
    map_one' :=
      by 
        apply Quot.sound <;> apply relation.one,
    map_mul' :=
      by 
        intros  <;> apply Quot.sound <;> apply relation.mul,
    map_zero' :=
      by 
        apply Quot.sound <;> apply relation.zero,
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

/-- The cocone over the proposed colimit commutative ring. -/
def colimit_cocone : cocone F :=
  { x := colimit F, ι := { app := cocone_morphism F } }

/-- The function from the free commutative ring on the diagram to the cone point of any other
cocone. -/
@[simp]
def desc_fun_lift (s : cocone F) : prequotient F → s.X
| of j x => (s.ι.app j) x
| zero => 0
| one => 1
| neg x => -desc_fun_lift x
| add x y => desc_fun_lift x+desc_fun_lift y
| mul x y => desc_fun_lift x*desc_fun_lift y

/-- The function from the colimit commutative ring to the cone point of any other cocone. -/
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
        rw [r_ih]
      ·
        rw [zero_addₓ]
      ·
        rw [add_zeroₓ]
      ·
        rw [one_mulₓ]
      ·
        rw [mul_oneₓ]
      ·
        rw [add_left_negₓ]
      ·
        rw [add_commₓ]
      ·
        rw [mul_commₓ]
      ·
        rw [add_assocₓ]
      ·
        rw [mul_assocₓ]
      ·
        rw [left_distrib]
      ·
        rw [right_distrib]

/-- The ring homomorphism from the colimit commutative ring to the cone point of any other
cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
  { toFun := desc_fun F s, map_one' := rfl, map_zero' := rfl,
    map_add' :=
      fun x y =>
        by 
          induction x <;> induction y <;> rfl,
    map_mul' :=
      fun x y =>
        by 
          induction x <;> induction y <;> rfl }

-- error in Algebra.Category.CommRing.Colimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Evidence that the proposed colimit is the colimit. -/ def colimit_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, desc_morphism F s,
  uniq' := λ s m w, begin
    ext [] [] [],
    induction [expr x] [] [] [],
    induction [expr x] [] [] [],
    { have [ident w'] [] [":=", expr congr_fun (congr_arg (λ
         f : «expr ⟶ »(F.obj x_j, s.X), (f : F.obj x_j → s.X)) (w x_j)) x_x],
      erw [expr w'] [],
      refl },
    { simp [] [] [] [] [] [] },
    { simp [] [] [] [] [] [] },
    { simp [] [] [] ["*"] [] [] },
    { simp [] [] [] ["*"] [] [] },
    { simp [] [] [] ["*"] [] [] },
    refl
  end }

instance has_colimits_CommRing : has_colimits CommRingₓₓ :=
  { HasColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { HasColimit :=
                fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_is_colimit F } } }

end CommRingₓₓ.Colimits

