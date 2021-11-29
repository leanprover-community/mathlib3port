import Mathbin.Algebra.Category.Mon.Basic 
import Mathbin.CategoryTheory.Limits.HasLimits 
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at the output of `#print monoid`:

  -- structure monoid : Type u → Type u
  -- fields:
  -- monoid.mul : Π {α : Type u} [c : monoid α], α → α → α
  -- monoid.mul_assoc : ∀ {α : Type u} [c : monoid α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  -- monoid.one : Π (α : Type u) [c : monoid α], α
  -- monoid.one_mul : ∀ {α : Type u} [c : monoid α] (a : α), 1 * a = a
  -- monoid.mul_one : ∀ {α : Type u} [c : monoid α] (a : α), a * 1 = a

and if we'd fed it the output of `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.
-/


universe v

open CategoryTheory

open CategoryTheory.Limits

namespace Mon.Colimits

/-!
We build the colimit of a diagram in `Mon` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [small_category J] (F : J ⥤ Mon.{v})

/--
An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
  | of : ∀ j : J x : F.obj j, prequotient
  | one : prequotient
  | mul : prequotient → prequotient → prequotient

instance : Inhabited (prequotient F) :=
  ⟨prequotient.one⟩

open Prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive relation : prequotient F → prequotient F → Prop
  | refl : ∀ x, relation x x
  | symm : ∀ x y h : relation x y, relation y x
  | trans : ∀ x y z h : relation x y k : relation y z, relation x z
  | map : ∀ j j' : J f : j ⟶ j' x : F.obj j, relation (of j' ((F.map f) x)) (of j x)
  | mul : ∀ j x y : F.obj j, relation (of j (x*y)) (mul (of j x) (of j y))
  | one : ∀ j, relation (of j 1) one
  | mul_1 : ∀ x x' y r : relation x x', relation (mul x y) (mul x' y)
  | mul_2 : ∀ x y y' r : relation y y', relation (mul x y) (mul x y')
  | mul_assocₓ : ∀ x y z, relation (mul (mul x y) z) (mul x (mul y z))
  | one_mulₓ : ∀ x, relation (mul one x) x
  | mul_oneₓ : ∀ x, relation (mul x one) x

/--
The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
def colimit_setoid : Setoidₓ (prequotient F) :=
  { R := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }

attribute [instance] colimit_setoid

-- error in Algebra.Category.Mon.Colimits: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
/--
The underlying type of the colimit of a diagram in `Mon`.
-/ @[derive #[expr inhabited]] def colimit_type : Type v :=
quotient (colimit_setoid F)

instance monoid_colimit_type : Monoidₓ (colimit_type F) :=
  { mul :=
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
    one :=
      by 
        exact Quot.mk _ one,
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
          rfl }

@[simp]
theorem quot_one : Quot.mk Setoidₓ.R one = (1 : colimit_type F) :=
  rfl

@[simp]
theorem quot_mul x y : Quot.mk Setoidₓ.R (mul x y) = (Quot.mk Setoidₓ.R x*Quot.mk Setoidₓ.R y : colimit_type F) :=
  rfl

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : Mon :=
  ⟨colimit_type F,
    by 
      infer_instance⟩

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
  Quot.mk _ (of j x)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
  { toFun := cocone_fun F j, map_one' := Quot.sound (relation.one _),
    map_mul' := fun x y => Quot.sound (relation.mul _ _ _) }

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

/-- The cocone over the proposed colimit monoid. -/
def colimit_cocone : cocone F :=
  { x := colimit F, ι := { app := cocone_morphism F } }

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp]
def desc_fun_lift (s : cocone F) : prequotient F → s.X
| of j x => (s.ι.app j) x
| one => 1
| mul x y => desc_fun_lift x*desc_fun_lift y

/-- The function from the colimit monoid to the cone point of any other cocone. -/
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
        rw [r_ih]
      ·
        rw [r_ih]
      ·
        rw [mul_assocₓ]
      ·
        rw [one_mulₓ]
      ·
        rw [mul_oneₓ]

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
  { toFun := desc_fun F s, map_one' := rfl,
    map_mul' :=
      fun x y =>
        by 
          induction x <;> induction y <;> rfl }

-- error in Algebra.Category.Mon.Colimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
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
    { simp [] [] [] ["*"] [] [] },
    { simp [] [] [] ["*"] [] [] },
    refl
  end }

instance has_colimits_Mon : has_colimits Mon :=
  { HasColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { HasColimit :=
                fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_is_colimit F } } }

end Mon.Colimits

