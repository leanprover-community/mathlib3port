import Mathbin.Data.Zmod.Basic 
import Mathbin.Data.Equiv.MulAdd 
import Mathbin.Tactic.Group

/-!
# Racks and Quandles

This file defines racks and quandles, algebraic structures for sets
that bijectively act on themselves with a self-distributivity
property.  If `R` is a rack and `act : R → (R ≃ R)` is the self-action,
then the self-distributivity is, equivalently, that
```
act (act x y) = act x * act y * (act x)⁻¹
```
where multiplication is composition in `R ≃ R` as a group.
Quandles are racks such that `act x x = x` for all `x`.

One example of a quandle (not yet in mathlib) is the action of a Lie
algebra on itself, defined by `act x y = Ad (exp x) y`.

Quandles and racks were independently developed by multiple
mathematicians.  David Joyce introduced quandles in his thesis
[Joyce1982] to define an algebraic invariant of knot and link
complements that is analogous to the fundamental group of the
exterior, and he showed that the quandle associated to an oriented
knot is invariant up to orientation-reversed mirror image.  Racks were
used by Fenn and Rourke for framed codimension-2 knots and
links.[FennRourke1992]

The name "rack" came from wordplay by Conway and Wraith for the "wrack
and ruin" of forgetting everything but the conjugation operation for a
group.

## Main definitions

* `shelf` is a type with a self-distributive action
* `rack` is a shelf whose action for each element is invertible
* `quandle` is a rack whose action for an element fixes that element
* `quandle.conj` defines a quandle of a group acting on itself by conjugation.
* `shelf_hom` is homomorphisms of shelves, racks, and quandles.
* `rack.envel_group` gives the universal group the rack maps to as a conjugation quandle.
* `rack.opp` gives the rack with the action replaced by its inverse.

## Main statements
* `rack.envel_group` is left adjoint to `quandle.conj` (`to_envel_group.map`).
  The universality statements are `to_envel_group.univ` and `to_envel_group.univ_uniq`.

## Notation

The following notation is localized in `quandles`:

* `x ◃ y` is `shelf.act x y`
* `x ◃⁻¹ y` is `rack.inv_act x y`
* `S →◃ S'` is `shelf_hom S S'`

Use `open_locale quandles` to use these.

## Todo

* If `g` is the Lie algebra of a Lie group `G`, then `(x ◃ y) = Ad (exp x) x` forms a quandle.
* If `X` is a symmetric space, then each point has a corresponding involution that acts on `X`,
  forming a quandle.
* Alexander quandle with `a ◃ b = t * b + (1 - t) * b`, with `a` and `b` elements
  of a module over `Z[t,t⁻¹]`.
* If `G` is a group, `H` a subgroup, and `z` in `H`, then there is a quandle `(G/H;z)` defined by
  `yH ◃ xH = yzy⁻¹xH`.  Every homogeneous quandle (i.e., a quandle `Q` whose automorphism group acts
  transitively on `Q` as a set) is isomorphic to such a quandle.
  There is a generalization to this arbitrary quandles in [Joyce's paper (Theorem 7.2)][Joyce1982].

## Tags

rack, quandle
-/


open Opposite

universe u v

/--
A *shelf* is a structure with a self-distributive binary operation.
The binary operation is regarded as a left action of the type on itself.
-/
class Shelf(α : Type u) where 
  act : α → α → α 
  self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z)

/--
The type of homomorphisms between shelves.
This is also the notion of rack and quandle homomorphisms.
-/
@[ext]
structure ShelfHom(S₁ : Type _)(S₂ : Type _)[Shelf S₁][Shelf S₂] where 
  toFun : S₁ → S₂ 
  map_act' : ∀ {x y : S₁}, to_fun (Shelf.act x y) = Shelf.act (to_fun x) (to_fun y)

/--
A *rack* is an automorphic set (a set with an action on itself by
bijections) that is self-distributive.  It is a shelf such that each
element's action is invertible.

The notations `x ◃ y` and `x ◃⁻¹ y` denote the action and the
inverse action, respectively, and they are right associative.
-/
class Rack(α : Type u) extends Shelf α where 
  invAct : α → α → α 
  left_inv : ∀ x, Function.LeftInverse (inv_act x) (act x)
  right_inv : ∀ x, Function.RightInverse (inv_act x) (act x)

localized [Quandles] infixr:65 " ◃ " => Shelf.act

localized [Quandles] infixr:65 " ◃⁻¹ " => Rack.invAct

localized [Quandles] infixr:25 " →◃ " => ShelfHom

open_locale Quandles

namespace Rack

variable{R : Type _}[Rack R]

theorem self_distrib {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ x ◃ z :=
  Shelf.self_distrib

/--
A rack acts on itself by equivalences.
-/
def act (x : R) : R ≃ R :=
  { toFun := Shelf.act x, invFun := inv_act x, left_inv := left_inv x, right_inv := right_inv x }

@[simp]
theorem act_apply (x y : R) : act x y = x ◃ y :=
  rfl

@[simp]
theorem act_symm_apply (x y : R) : (act x).symm y = x ◃⁻¹ y :=
  rfl

@[simp]
theorem inv_act_apply (x y : R) : (act x⁻¹) y = x ◃⁻¹ y :=
  rfl

@[simp]
theorem inv_act_act_eq (x y : R) : x ◃⁻¹ x ◃ y = y :=
  left_inv x y

@[simp]
theorem act_inv_act_eq (x y : R) : x ◃ x ◃⁻¹ y = y :=
  right_inv x y

theorem left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' :=
  by 
    split 
    apply (act x).Injective 
    rintro rfl 
    rfl

theorem left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' :=
  by 
    split 
    apply (act x).symm.Injective 
    rintro rfl 
    rfl

-- error in Algebra.Quandle: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem self_distrib_inv
{x y z : R} : «expr = »(«expr ◃⁻¹ »(x, «expr ◃⁻¹ »(y, z)), «expr ◃⁻¹ »(«expr ◃⁻¹ »(x, y), «expr ◃⁻¹ »(x, z))) :=
begin
  rw ["[", "<-", expr left_cancel «expr ◃⁻¹ »(x, y), ",", expr right_inv, ",", "<-", expr left_cancel x, ",", expr right_inv, ",", expr self_distrib, "]"] [],
  repeat { rw [expr right_inv] [] }
end

/--
The *adjoint action* of a rack on itself is `op'`, and the adjoint
action of `x ◃ y` is the conjugate of the action of `y` by the action
of `x`. It is another way to understand the self-distributivity axiom.

This is used in the natural rack homomorphism `to_conj` from `R` to
`conj (R ≃ R)` defined by `op'`.
-/
theorem ad_conj {R : Type _} [Rack R] (x y : R) : act (x ◃ y) = (act x*act y)*act x⁻¹ :=
  by 
    apply @mul_right_cancelₓ _ _ _ (act x)
    ext z 
    simp only [inv_mul_cancel_right]
    apply self_distrib.symm

/--
The opposite rack, swapping the roles of `◃` and `◃⁻¹`.
-/
instance opposite_rack : Rack («expr ᵒᵖ» R) :=
  { act := fun x y => op (inv_act (unop x) (unop y)),
    self_distrib :=
      fun x y z : «expr ᵒᵖ» R =>
        by 
          induction x using Opposite.rec 
          induction y using Opposite.rec 
          induction z using Opposite.rec 
          simp only [unop_op, op_inj_iff]
          exact self_distrib_inv,
    invAct := fun x y => op (Shelf.act (unop x) (unop y)),
    left_inv :=
      fun x y =>
        by 
          induction x using Opposite.rec 
          induction y using Opposite.rec 
          simp ,
    right_inv :=
      fun x y =>
        by 
          induction x using Opposite.rec 
          induction y using Opposite.rec 
          simp  }

@[simp]
theorem op_act_op_eq {x y : R} : op x ◃ op y = op (x ◃⁻¹ y) :=
  rfl

@[simp]
theorem op_inv_act_op_eq {x y : R} : op x ◃⁻¹ op y = op (x ◃ y) :=
  rfl

@[simp]
theorem self_act_act_eq {x y : R} : (x ◃ x) ◃ y = x ◃ y :=
  by 
    rw [←right_inv x y, ←self_distrib]

@[simp]
theorem self_inv_act_inv_act_eq {x y : R} : (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y :=
  by 
    have h := @self_act_act_eq _ _ (op x) (op y)
    simpa using h

@[simp]
theorem self_act_inv_act_eq {x y : R} : (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y :=
  by 
    rw [←left_cancel (x ◃ x)]
    rw [right_inv]
    rw [self_act_act_eq]
    rw [right_inv]

@[simp]
theorem self_inv_act_act_eq {x y : R} : (x ◃⁻¹ x) ◃ y = x ◃ y :=
  by 
    have h := @self_act_inv_act_eq _ _ (op x) (op y)
    simpa using h

theorem self_act_eq_iff_eq {x y : R} : x ◃ x = y ◃ y ↔ x = y :=
  by 
    split 
    swap 
    rintro rfl 
    rfl 
    intro h 
    trans (x ◃ x) ◃⁻¹ x ◃ x 
    rw [←left_cancel (x ◃ x), right_inv, self_act_act_eq]
    rw [h, ←left_cancel (y ◃ y), right_inv, self_act_act_eq]

theorem self_inv_act_eq_iff_eq {x y : R} : x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y :=
  by 
    have h := @self_act_eq_iff_eq _ _ (op x) (op y)
    simpa using h

/--
The map `x ↦ x ◃ x` is a bijection.  (This has applications for the
regular isotopy version of the Reidemeister I move for knot diagrams.)
-/
def self_apply_equiv (R : Type _) [Rack R] : R ≃ R :=
  { toFun := fun x => x ◃ x, invFun := fun x => x ◃⁻¹ x,
    left_inv :=
      fun x =>
        by 
          simp ,
    right_inv :=
      fun x =>
        by 
          simp  }

/--
An involutory rack is one for which `rack.op R x` is an involution for every x.
-/
def is_involutory (R : Type _) [Rack R] : Prop :=
  ∀ x : R, Function.Involutive (Shelf.act x)

theorem involutory_inv_act_eq_act {R : Type _} [Rack R] (h : is_involutory R) (x y : R) : x ◃⁻¹ y = x ◃ y :=
  by 
    rw [←left_cancel x, right_inv]
    exact ((h x).LeftInverse y).symm

/--
An abelian rack is one for which the mediality axiom holds.
-/
def is_abelian (R : Type _) [Rack R] : Prop :=
  ∀ x y z w : R, (x ◃ y) ◃ z ◃ w = (x ◃ z) ◃ y ◃ w

/--
Associative racks are uninteresting.
-/
theorem assoc_iff_id {R : Type _} [Rack R] {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z :=
  by 
    rw [self_distrib]
    rw [left_cancel]

end Rack

namespace ShelfHom

variable{S₁ : Type _}{S₂ : Type _}{S₃ : Type _}[Shelf S₁][Shelf S₂][Shelf S₃]

instance  : CoeFun (S₁ →◃ S₂) fun _ => S₁ → S₂ :=
  ⟨ShelfHom.toFun⟩

@[simp]
theorem to_fun_eq_coe (f : S₁ →◃ S₂) : f.to_fun = f :=
  rfl

@[simp]
theorem map_act (f : S₁ →◃ S₂) {x y : S₁} : f (x ◃ y) = f x ◃ f y :=
  map_act' f

/-- The identity homomorphism -/
def id (S : Type _) [Shelf S] : S →◃ S :=
  { toFun := id,
    map_act' :=
      by 
        simp  }

instance Inhabited (S : Type _) [Shelf S] : Inhabited (S →◃ S) :=
  ⟨id S⟩

/-- The composition of shelf homomorphisms -/
def comp (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) : S₁ →◃ S₃ :=
  { toFun := g.to_fun ∘ f.to_fun,
    map_act' :=
      by 
        simp  }

@[simp]
theorem comp_apply (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) (x : S₁) : (g.comp f) x = g (f x) :=
  rfl

end ShelfHom

/--
A quandle is a rack such that each automorphism fixes its corresponding element.
-/
class Quandle(α : Type _) extends Rack α where 
  fix : ∀ {x : α}, act x x = x

namespace Quandle

open Rack

variable{Q : Type _}[Quandle Q]

attribute [simp] fix

@[simp]
theorem fix_inv {x : Q} : x ◃⁻¹ x = x :=
  by 
    rw [←left_cancel x]
    simp 

instance opposite_quandle : Quandle («expr ᵒᵖ» Q) :=
  { fix :=
      fun x =>
        by 
          induction x using Opposite.rec 
          simp  }

/--
The conjugation quandle of a group.  Each element of the group acts by
the corresponding inner automorphism.
-/
@[nolint has_inhabited_instance]
def conj (G : Type _) :=
  G

instance conj.quandle (G : Type _) [Groupₓ G] : Quandle (conj G) :=
  { act := fun x => @MulAut.conj G _ x,
    self_distrib :=
      fun x y z =>
        by 
          dsimp only [MulEquiv.coe_to_equiv, MulAut.conj_apply, conj]
          group,
    invAct := fun x => (@MulAut.conj G _ x).symm,
    left_inv :=
      fun x y =>
        by 
          dsimp [act, conj]
          group,
    right_inv :=
      fun x y =>
        by 
          dsimp [act, conj]
          group,
    fix :=
      fun x =>
        by 
          simp  }

@[simp]
theorem conj_act_eq_conj {G : Type _} [Groupₓ G] (x y : conj G) : x ◃ y = (((x : G)*(y : G))*(x : G)⁻¹ : G) :=
  rfl

-- error in Algebra.Quandle: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem conj_swap
{G : Type*}
[group G]
(x y : conj G) : «expr ↔ »(«expr = »(«expr ◃ »(x, y), y), «expr = »(«expr ◃ »(y, x), x)) :=
begin
  dsimp [] [] [] [],
  split,
  repeat { intro [ident h],
    conv_rhs [] [] { rw [expr eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq h)] },
    simp [] [] [] [] [] [] }
end

/--
`conj` is functorial
-/
def conj.map {G : Type _} {H : Type _} [Groupₓ G] [Groupₓ H] (f : G →* H) : conj G →◃ conj H :=
  { toFun := f,
    map_act' :=
      by 
        simp  }

instance  {G : Type _} {H : Type _} [Groupₓ G] [Groupₓ H] : HasLift (G →* H) (conj G →◃ conj H) :=
  { lift := conj.map }

/--
The dihedral quandle. This is the conjugation quandle of the dihedral group restrict to flips.

Used for Fox n-colorings of knots.
-/
@[nolint has_inhabited_instance]
def dihedral (n : ℕ) :=
  Zmod n

/--
The operation for the dihedral quandle.  It does not need to be an equivalence
because it is an involution (see `dihedral_act.inv`).
-/
def dihedral_act (n : ℕ) (a : Zmod n) : Zmod n → Zmod n :=
  fun b => (2*a) - b

theorem dihedral_act.inv (n : ℕ) (a : Zmod n) : Function.Involutive (dihedral_act n a) :=
  by 
    intro b 
    dsimp [dihedral_act]
    ring

instance  (n : ℕ) : Quandle (dihedral n) :=
  { act := dihedral_act n,
    self_distrib :=
      fun x y z =>
        by 
          dsimp [Function.Involutive.toEquiv, dihedral_act]
          ring,
    invAct := dihedral_act n, left_inv := fun x => (dihedral_act.inv n x).LeftInverse,
    right_inv := fun x => (dihedral_act.inv n x).RightInverse,
    fix :=
      fun x =>
        by 
          dsimp [Function.Involutive.toEquiv, dihedral_act]
          ring }

end Quandle

namespace Rack

/--
This is the natural rack homomorphism to the conjugation quandle of the group `R ≃ R`
that acts on the rack.
-/
def to_conj (R : Type _) [Rack R] : R →◃ Quandle.Conj (R ≃ R) :=
  { toFun := act, map_act' := ad_conj }

section EnvelGroup

/-!
### Universal enveloping group of a rack

The universal enveloping group `envel_group R` of a rack `R` is the
universal group such that every rack homomorphism `R →◃ conj G` is
induced by a unique group homomorphism `envel_group R →* G`.
For quandles, Joyce called this group `AdConj R`.

The `envel_group` functor is left adjoint to the `conj` forgetful
functor, and the way we construct the enveloping group is via a
technique that should work for left adjoints of forgetful functors in
general.  It involves thinking a little about 2-categories, but the
payoff is that the map `envel_group R →* G` has a nice description.

Let's think of a group as being a one-object category.  The first step
is to define `pre_envel_group`, which gives formal expressions for all
the 1-morphisms and includes the unit element, elements of `R`,
multiplication, and inverses.  To introduce relations, the second step
is to define `pre_envel_group_rel'`, which gives formal expressions
for all 2-morphisms between the 1-morphisms.  The 2-morphisms include
associativity, multiplication by the unit, multiplication by inverses,
compatibility with multiplication and inverses (`congr_mul` and
`congr_inv`), the axioms for an equivalence relation, and,
importantly, the relationship between conjugation and the rack action
(see `rack.ad_conj`).

None of this forms a 2-category yet, for example due to lack of
associativity of `trans`.  The `pre_envel_group_rel` relation is a
`Prop`-valued version of `pre_envel_group_rel'`, and making it
`Prop`-valued essentially introduces enough 3-isomorphisms so that
every pair of compatible 2-morphisms is isomorphic.  Now, while
composition in `pre_envel_group` does not strictly satisfy the category
axioms, `pre_envel_group` and `pre_envel_group_rel'` do form a weak
2-category.

Since we just want a 1-category, the last step is to quotient
`pre_envel_group` by `pre_envel_group_rel'`, and the result is the
group `envel_group`.

For a homomorphism `f : R →◃ conj G`, how does
`envel_group.map f : envel_group R →* G` work?  Let's think of `G` as
being a 2-category with one object, a 1-morphism per element of `G`,
and a single 2-morphism called `eq.refl` for each 1-morphism.  We
define the map using a "higher `quotient.lift`" -- not only do we
evaluate elements of `pre_envel_group` as expressions in `G` (this is
`to_envel_group.map_aux`), but we evaluate elements of
`pre_envel_group'` as expressions of 2-morphisms of `G` (this is
`to_envel_group.map_aux.well_def`).  That is to say,
`to_envel_group.map_aux.well_def` recursively evaluates formal
expressions of 2-morphisms as equality proofs in `G`.  Now that all
morphisms are accounted for, the map descends to a homomorphism
`envel_group R →* G`.

Note: `Type`-valued relations are not common.  The fact it is
`Type`-valued is what makes `to_envel_group.map_aux.well_def` have
well-founded recursion.
-/


/--
Free generators of the enveloping group.
-/
inductive pre_envel_group (R : Type u) : Type u
  | Unit : pre_envel_group
  | incl (x : R) : pre_envel_group
  | mul (a b : pre_envel_group) : pre_envel_group
  | inv (a : pre_envel_group) : pre_envel_group

instance pre_envel_group.inhabited (R : Type u) : Inhabited (pre_envel_group R) :=
  ⟨pre_envel_group.unit⟩

open PreEnvelGroup

/--
Relations for the enveloping group. This is a type-valued relation because
`to_envel_group.map_aux.well_def` inducts on it to show `to_envel_group.map`
is well-defined.  The relation `pre_envel_group_rel` is the `Prop`-valued version,
which is used to define `envel_group` itself.
-/
inductive pre_envel_group_rel' (R : Type u) [Rack R] : pre_envel_group R → pre_envel_group R → Type u
  | refl {a : pre_envel_group R} : pre_envel_group_rel' a a
  | symm {a b : pre_envel_group R} (hab : pre_envel_group_rel' a b) : pre_envel_group_rel' b a
  | trans {a b c : pre_envel_group R} (hab : pre_envel_group_rel' a b) (hbc : pre_envel_group_rel' b c) :
  pre_envel_group_rel' a c
  | congr_mul {a b a' b' : pre_envel_group R} (ha : pre_envel_group_rel' a a') (hb : pre_envel_group_rel' b b') :
  pre_envel_group_rel' (mul a b) (mul a' b')
  | congr_inv {a a' : pre_envel_group R} (ha : pre_envel_group_rel' a a') : pre_envel_group_rel' (inv a) (inv a')
  | assoc (a b c : pre_envel_group R) : pre_envel_group_rel' (mul (mul a b) c) (mul a (mul b c))
  | one_mulₓ (a : pre_envel_group R) : pre_envel_group_rel' (mul Unit a) a
  | mul_oneₓ (a : pre_envel_group R) : pre_envel_group_rel' (mul a Unit) a
  | mul_left_invₓ (a : pre_envel_group R) : pre_envel_group_rel' (mul (inv a) a) Unit
  | act_incl (x y : R) : pre_envel_group_rel' (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))

instance pre_envel_group_rel'.inhabited (R : Type u) [Rack R] : Inhabited (pre_envel_group_rel' R Unit Unit) :=
  ⟨pre_envel_group_rel'.refl⟩

/--
The `pre_envel_group_rel` relation as a `Prop`.  Used as the relation for `pre_envel_group.setoid`.
-/
inductive pre_envel_group_rel (R : Type u) [Rack R] : pre_envel_group R → pre_envel_group R → Prop
  | Rel {a b : pre_envel_group R} (r : pre_envel_group_rel' R a b) : pre_envel_group_rel a b

/--
A quick way to convert a `pre_envel_group_rel'` to a `pre_envel_group_rel`.
-/
theorem pre_envel_group_rel'.rel {R : Type u} [Rack R] {a b : pre_envel_group R} :
  pre_envel_group_rel' R a b → pre_envel_group_rel R a b :=
  pre_envel_group_rel.rel

@[refl]
theorem pre_envel_group_rel.refl {R : Type u} [Rack R] {a : pre_envel_group R} : pre_envel_group_rel R a a :=
  pre_envel_group_rel.rel pre_envel_group_rel'.refl

@[symm]
theorem pre_envel_group_rel.symm {R : Type u} [Rack R] {a b : pre_envel_group R} :
  pre_envel_group_rel R a b → pre_envel_group_rel R b a
| ⟨r⟩ => r.symm.rel

@[trans]
theorem pre_envel_group_rel.trans {R : Type u} [Rack R] {a b c : pre_envel_group R} :
  pre_envel_group_rel R a b → pre_envel_group_rel R b c → pre_envel_group_rel R a c
| ⟨rab⟩, ⟨rbc⟩ => (rab.trans rbc).Rel

instance pre_envel_group.setoid (R : Type _) [Rack R] : Setoidₓ (pre_envel_group R) :=
  { R := pre_envel_group_rel R,
    iseqv :=
      by 
        split 
        apply pre_envel_group_rel.refl 
        split 
        apply pre_envel_group_rel.symm 
        apply pre_envel_group_rel.trans }

/--
The universal enveloping group for the rack R.
-/
def envel_group (R : Type _) [Rack R] :=
  Quotientₓ (pre_envel_group.setoid R)

instance  (R : Type _) [Rack R] : DivInvMonoidₓ (envel_group R) :=
  { mul :=
      fun a b =>
        Quotientₓ.liftOn₂ a b (fun a b => «expr⟦ ⟧» (pre_envel_group.mul a b))
          fun a b a' b' ⟨ha⟩ ⟨hb⟩ => Quotientₓ.sound (pre_envel_group_rel'.congr_mul ha hb).Rel,
    one := «expr⟦ ⟧» Unit,
    inv :=
      fun a =>
        Quotientₓ.liftOn a (fun a => «expr⟦ ⟧» (pre_envel_group.inv a))
          fun a a' ⟨ha⟩ => Quotientₓ.sound (pre_envel_group_rel'.congr_inv ha).Rel,
    mul_assoc :=
      fun a b c => Quotientₓ.induction_on₃ a b c fun a b c => Quotientₓ.sound (pre_envel_group_rel'.assoc a b c).Rel,
    one_mul := fun a => Quotientₓ.induction_on a fun a => Quotientₓ.sound (pre_envel_group_rel'.one_mul a).Rel,
    mul_one := fun a => Quotientₓ.induction_on a fun a => Quotientₓ.sound (pre_envel_group_rel'.mul_one a).Rel }

instance  (R : Type _) [Rack R] : Groupₓ (envel_group R) :=
  { envel_group.div_inv_monoid _ with
    mul_left_inv :=
      fun a => Quotientₓ.induction_on a fun a => Quotientₓ.sound (pre_envel_group_rel'.mul_left_inv a).Rel }

instance envel_group.inhabited (R : Type _) [Rack R] : Inhabited (envel_group R) :=
  ⟨1⟩

/--
The canonical homomorphism from a rack to its enveloping group.
Satisfies universal properties given by `to_envel_group.map` and `to_envel_group.univ`.
-/
def to_envel_group (R : Type _) [Rack R] : R →◃ Quandle.Conj (envel_group R) :=
  { toFun := fun x => «expr⟦ ⟧» (incl x),
    map_act' := fun x y => Quotientₓ.sound (pre_envel_group_rel'.act_incl x y).symm.Rel }

/--
The preliminary definition of the induced map from the enveloping group.
See `to_envel_group.map`.
-/
def to_envel_group.map_aux {R : Type _} [Rack R] {G : Type _} [Groupₓ G] (f : R →◃ Quandle.Conj G) :
  pre_envel_group R → G
| Unit => 1
| incl x => f x
| mul a b => to_envel_group.map_aux a*to_envel_group.map_aux b
| inv a => to_envel_group.map_aux a⁻¹

namespace ToEnvelGroup.MapAux

open PreEnvelGroupRel'

/--
Show that `to_envel_group.map_aux` sends equivalent expressions to equal terms.
-/
theorem well_def {R : Type _} [Rack R] {G : Type _} [Groupₓ G] (f : R →◃ Quandle.Conj G) :
  ∀ {a b : pre_envel_group R}, pre_envel_group_rel' R a b → to_envel_group.map_aux f a = to_envel_group.map_aux f b
| a, b, refl => rfl
| a, b, symm h => (well_def h).symm
| a, b, trans hac hcb => Eq.trans (well_def hac) (well_def hcb)
| _, _, congr_mul ha hb =>
  by 
    simp [to_envel_group.map_aux, well_def ha, well_def hb]
| _, _, congr_inv ha =>
  by 
    simp [to_envel_group.map_aux, well_def ha]
| _, _, assoc a b c =>
  by 
    apply mul_assocₓ
| _, _, one_mulₓ a =>
  by 
    simp [to_envel_group.map_aux]
| _, _, mul_oneₓ a =>
  by 
    simp [to_envel_group.map_aux]
| _, _, mul_left_invₓ a =>
  by 
    simp [to_envel_group.map_aux]
| _, _, act_incl x y =>
  by 
    simp [to_envel_group.map_aux]

end ToEnvelGroup.MapAux

/--
Given a map from a rack to a group, lift it to being a map from the enveloping group.
More precisely, the `envel_group` functor is left adjoint to `quandle.conj`.
-/
def to_envel_group.map {R : Type _} [Rack R] {G : Type _} [Groupₓ G] : (R →◃ Quandle.Conj G) ≃ (envel_group R →* G) :=
  { toFun :=
      fun f =>
        { toFun :=
            fun x =>
              Quotientₓ.liftOn x (to_envel_group.map_aux f) fun a b ⟨hab⟩ => to_envel_group.map_aux.well_def f hab,
          map_one' :=
            by 
              change Quotientₓ.liftOn («expr⟦ ⟧» Unit) (to_envel_group.map_aux f) _ = 1
              simp [to_envel_group.map_aux],
          map_mul' :=
            fun x y =>
              Quotientₓ.induction_on₂ x y
                fun x y =>
                  by 
                    change Quotientₓ.liftOn («expr⟦ ⟧» (mul x y)) (to_envel_group.map_aux f) _ = _ 
                    simp [to_envel_group.map_aux] },
    invFun := fun F => (Quandle.Conj.map F).comp (to_envel_group R),
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun F =>
        MonoidHom.ext$
          fun x =>
            Quotientₓ.induction_on x$
              fun x =>
                by 
                  induction x
                  ·
                    exact F.map_one.symm
                  ·
                    rfl
                  ·
                    have hm : «expr⟦ ⟧» (x_a.mul x_b) = @Mul.mul (envel_group R) _ («expr⟦ ⟧» x_a) («expr⟦ ⟧» x_b) :=
                      rfl 
                    rw [hm, F.map_mul, MonoidHom.map_mul, ←x_ih_a, ←x_ih_b]
                  ·
                    have hm : «expr⟦ ⟧» x_a.inv = @HasInv.inv (envel_group R) _ («expr⟦ ⟧» x_a) := rfl 
                    rw [hm, F.map_inv, MonoidHom.map_inv, x_ih] }

/--
Given a homomorphism from a rack to a group, it factors through the enveloping group.
-/
theorem to_envel_group.univ (R : Type _) [Rack R] (G : Type _) [Groupₓ G] (f : R →◃ Quandle.Conj G) :
  (Quandle.Conj.map (to_envel_group.map f)).comp (to_envel_group R) = f :=
  to_envel_group.map.symm_apply_apply f

/--
The homomorphism `to_envel_group.map f` is the unique map that fits into the commutative
triangle in `to_envel_group.univ`.
-/
theorem to_envel_group.univ_uniq (R : Type _) [Rack R] (G : Type _) [Groupₓ G] (f : R →◃ Quandle.Conj G)
  (g : envel_group R →* G) (h : f = (Quandle.Conj.map g).comp (to_envel_group R)) : g = to_envel_group.map f :=
  h.symm ▸ (to_envel_group.map.apply_symm_apply g).symm

/--
The induced group homomorphism from the enveloping group into bijections of the rack,
using `rack.to_conj`. Satisfies the property `envel_action_prop`.

This gives the rack `R` the structure of an augmented rack over `envel_group R`.
-/
def envel_action {R : Type _} [Rack R] : envel_group R →* R ≃ R :=
  to_envel_group.map (to_conj R)

@[simp]
theorem envel_action_prop {R : Type _} [Rack R] (x y : R) : envel_action (to_envel_group R x) y = x ◃ y :=
  rfl

end EnvelGroup

end Rack

