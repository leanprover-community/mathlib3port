import Mathbin.Algebra.Homology.Additive
import Mathbin.Tactic.Abel

/-!
# Chain homotopies

We define chain homotopies, and prove that homotopic chain maps induce the same map on homology.
-/


universe v u

open_locale Classical

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable {V : Type u} [category.{v} V] [preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

section

/--  The composition of `C.d i i' ≫ f i' i` if there is some `i'` coming after `i`,
and `0` otherwise. -/
def dNext (i : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X i ⟶ D.X i) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.next i with
      | none => 0
      | some ⟨i', w⟩ => C.d i i' ≫ f i' i)
    (by
      intro f g
      rcases c.next i with (_ | ⟨i', w⟩)
      exact (zero_addₓ _).symm
      exact preadditive.comp_add _ _ _ _ _ _)

/--  `f i' i` if `i'` comes after `i`, and 0 if there's no such `i'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def fromNext [has_zero_object V] (i : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X_next i ⟶ D.X i) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.next i with
      | none => 0
      | some ⟨i', w⟩ => (C.X_next_iso w).Hom ≫ f i' i)
    (by
      intro f g
      rcases c.next i with (_ | ⟨i', w⟩)
      exact (zero_addₓ _).symm
      exact preadditive.comp_add _ _ _ _ _ _)

theorem d_next_eq_d_from_from_next [has_zero_object V] (f : ∀ i j, C.X i ⟶ D.X j) (i : ι) :
    dNext i f = C.d_from i ≫ fromNext i f := by
  dsimp [dNext, fromNext]
  rcases c.next i with (⟨⟩ | ⟨⟨i', w⟩⟩) <;>
    ·
      dsimp [dNext, fromNext]
      simp

theorem d_next_eq (f : ∀ i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.rel i i') : dNext i f = C.d i i' ≫ f i' i := by
  dsimp [dNext]
  rw [c.next_eq_some w]
  rfl

@[simp]
theorem d_next_comp_left (f : C ⟶ D) (g : ∀ i j, D.X i ⟶ E.X j) (i : ι) :
    (dNext i fun i j => f.f i ≫ g i j) = f.f i ≫ dNext i g := by
  dsimp [dNext]
  rcases c.next i with (_ | ⟨i', w⟩)
  ·
    exact comp_zero.symm
  ·
    dsimp [dNext]
    simp

@[simp]
theorem d_next_comp_right (f : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι) :
    (dNext i fun i j => f i j ≫ g.f j) = dNext i f ≫ g.f i := by
  dsimp [dNext]
  rcases c.next i with (_ | ⟨i', w⟩)
  ·
    exact zero_comp.symm
  ·
    dsimp [dNext]
    simp

/--  The composition of `f j j' ≫ D.d j' j` if there is some `j'` coming before `j`,
and `0` otherwise. -/
def prevD (j : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X j) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.prev j with
      | none => 0
      | some ⟨j', w⟩ => f j j' ≫ D.d j' j)
    (by
      intro f g
      rcases c.prev j with (_ | ⟨j', w⟩)
      exact (zero_addₓ _).symm
      exact preadditive.add_comp _ _ _ _ _ _)

/--  `f j j'` if `j'` comes after `j`, and 0 if there's no such `j'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def toPrev [has_zero_object V] (j : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X_prev j) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.prev j with
      | none => 0
      | some ⟨j', w⟩ => f j j' ≫ (D.X_prev_iso w).inv)
    (by
      intro f g
      rcases c.prev j with (_ | ⟨j', w⟩)
      exact (zero_addₓ _).symm
      exact preadditive.add_comp _ _ _ _ _ _)

theorem prev_d_eq_to_prev_d_to [has_zero_object V] (f : ∀ i j, C.X i ⟶ D.X j) (j : ι) :
    prevD j f = toPrev j f ≫ D.d_to j := by
  dsimp [prevD, toPrev]
  rcases c.prev j with (⟨⟩ | ⟨⟨j', w⟩⟩) <;>
    ·
      dsimp [prevD, toPrev]
      simp

theorem prev_d_eq (f : ∀ i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.rel j' j) : prevD j f = f j j' ≫ D.d j' j := by
  dsimp [prevD]
  rw [c.prev_eq_some w]
  rfl

@[simp]
theorem prev_d_comp_left (f : C ⟶ D) (g : ∀ i j, D.X i ⟶ E.X j) (j : ι) :
    (prevD j fun i j => f.f i ≫ g i j) = f.f j ≫ prevD j g := by
  dsimp [prevD]
  rcases c.prev j with (_ | ⟨j', w⟩)
  ·
    exact comp_zero.symm
  ·
    dsimp [prevD, hom.prev]
    simp

@[simp]
theorem to_prev'_comp_right (f : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι) :
    (prevD j fun i j => f i j ≫ g.f j) = prevD j f ≫ g.f j := by
  dsimp [prevD]
  rcases c.prev j with (_ | ⟨j', w⟩)
  ·
    exact zero_comp.symm
  ·
    dsimp [prevD]
    simp

theorem d_next_nat (C D : ChainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.X i ⟶ D.X j) :
    dNext i f = C.d i (i - 1) ≫ f (i - 1) i := by
  cases i
  ·
    dsimp [dNext]
    rcases(ComplexShape.down ℕ).next 0 with (_ | ⟨j, hj⟩) <;> dsimp [dNext]
    ·
      rw [C.shape, zero_comp]
      dsimp
      decide
    ·
      dsimp  at hj
      exact (Nat.succ_ne_zero _ hj).elim
  rw [d_next_eq]
  dsimp
  rfl

theorem prev_d_nat (C D : CochainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.X i ⟶ D.X j) :
    prevD i f = f i (i - 1) ≫ D.d (i - 1) i := by
  cases i
  ·
    dsimp [prevD]
    rcases(ComplexShape.up ℕ).prev 0 with (_ | ⟨j, hj⟩) <;> dsimp [prevD]
    ·
      rw [D.shape, comp_zero]
      dsimp
      decide
    ·
      dsimp  at hj
      exact (Nat.succ_ne_zero _ hj).elim
  rw [prev_d_eq]
  dsimp
  rfl

/-- 
A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X j`
which are zero unless `c.rel j i`, satisfying the homotopy condition.
-/
@[ext, nolint has_inhabited_instance]
structure Homotopy (f g : C ⟶ D) where
  Hom : ∀ i j, C.X i ⟶ D.X j
  zero' : ∀ i j, ¬c.rel j i → hom i j = 0 := by
    run_tac
      obviously
  comm : ∀ i, f.f i = (dNext i hom+prevD i hom)+g.f i := by
    run_tac
      obviously'

variable {f g}

namespace Homotopy

restate_axiom Homotopy.zero'

/-- 
`f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equiv_sub_zero : Homotopy f g ≃ Homotopy (f - g) 0 :=
  { toFun := fun h =>
      { Hom := fun i j => h.hom i j, zero' := fun i j w => h.zero _ _ w,
        comm := fun i => by
          simp [h.comm] },
    invFun := fun h =>
      { Hom := fun i j => h.hom i j, zero' := fun i j w => h.zero _ _ w,
        comm := fun i => by
          simpa [sub_eq_iff_eq_add] using h.comm i },
    left_inv := by
      tidy,
    right_inv := by
      tidy }

/--  Equal chain maps are homotopic. -/
@[simps]
def of_eq (h : f = g) : Homotopy f g :=
  { Hom := 0, zero' := fun _ _ _ => rfl,
    comm := fun _ => by
      simp only [AddMonoidHom.map_zero, zero_addₓ, h] }

/--  Every chain map is homotopic to itself. -/
@[simps, refl]
def refl (f : C ⟶ D) : Homotopy f f :=
  of_eq (rfl : f = f)

/--  `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps, symm]
def symm {f g : C ⟶ D} (h : Homotopy f g) : Homotopy g f :=
  { Hom := -h.hom,
    zero' := fun i j w => by
      rw [Pi.neg_apply, Pi.neg_apply, h.zero i j w, neg_zero],
    comm := fun i => by
      rw [AddMonoidHom.map_neg, AddMonoidHom.map_neg, h.comm, ← neg_add, ← add_assocₓ, neg_add_selfₓ, zero_addₓ] }

/--  homotopy is a transitive relation. -/
@[simps, trans]
def trans {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g) : Homotopy e g :=
  { Hom := h.hom+k.hom,
    zero' := fun i j w => by
      rw [Pi.add_apply, Pi.add_apply, h.zero i j w, k.zero i j w, zero_addₓ],
    comm := fun i => by
      rw [AddMonoidHom.map_add, AddMonoidHom.map_add, h.comm, k.comm]
      abel }

/--  homotopy is closed under composition (on the right) -/
@[simps]
def comp_right {e f : C ⟶ D} (h : Homotopy e f) (g : D ⟶ E) : Homotopy (e ≫ g) (f ≫ g) :=
  { Hom := fun i j => h.hom i j ≫ g.f j,
    zero' := fun i j w => by
      rw [h.zero i j w, zero_comp],
    comm := fun i => by
      simp only [h.comm i, d_next_comp_right, preadditive.add_comp, to_prev'_comp_right, comp_f] }

/--  homotopy is closed under composition (on the left) -/
@[simps]
def comp_left {f g : D ⟶ E} (h : Homotopy f g) (e : C ⟶ D) : Homotopy (e ≫ f) (e ≫ g) :=
  { Hom := fun i j => e.f i ≫ h.hom i j,
    zero' := fun i j w => by
      rw [h.zero i j w, comp_zero],
    comm := fun i => by
      simp only [h.comm i, d_next_comp_left, preadditive.comp_add, prev_d_comp_left, comp_f] }

/--  homotopy is closed under composition -/
@[simps]
def comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃} (h₁ : Homotopy f₁ g₁)
    (h₂ : Homotopy f₂ g₂) : Homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.comp_right _).trans (h₂.comp_left _)

/--  a variant of `homotopy.comp_right` useful for dealing with homotopy equivalences. -/
@[simps]
def comp_right_id {f : C ⟶ C} (h : Homotopy f (𝟙 C)) (g : C ⟶ D) : Homotopy (f ≫ g) g :=
  (h.comp_right g).trans (of_eq $ category.id_comp _)

/--  a variant of `homotopy.comp_left` useful for dealing with homotopy equivalences. -/
@[simps]
def comp_left_id {f : D ⟶ D} (h : Homotopy f (𝟙 D)) (g : C ⟶ D) : Homotopy (g ≫ f) g :=
  (h.comp_left g).trans (of_eq $ category.comp_id _)

/-!
`homotopy.mk_inductive` allows us to build a homotopy inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.

To simplify the situation, we only construct homotopies of the form `homotopy e 0`.
`homotopy.equiv_sub_zero` can provide the general case.

Notice however, that this construction does not have particularly good definitional properties:
we have to insert `eq_to_hom` in several places.
Hopefully this is okay in most applications, where we only need to have the existence of some
homotopy.
-/


section MkInductive

variable {P Q : ChainComplex V ℕ}

@[simp]
theorem prev_d_chain_complex (f : ∀ i j, P.X i ⟶ Q.X j) (j : ℕ) : prevD j f = f j (j+1) ≫ Q.d _ _ := by
  dsimp [prevD]
  simp only [ChainComplex.prev]
  rfl

@[simp]
theorem d_next_succ_chain_complex (f : ∀ i j, P.X i ⟶ Q.X j) (i : ℕ) : dNext (i+1) f = P.d _ _ ≫ f i (i+1) := by
  dsimp [dNext]
  simp only [ChainComplex.next_nat_succ]
  rfl

@[simp]
theorem d_next_zero_chain_complex (f : ∀ i j, P.X i ⟶ Q.X j) : dNext 0 f = 0 := by
  dsimp [dNext]
  simp only [ChainComplex.next_nat_zero]
  rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
 "variable"
 [(Term.explicitBinder "(" [`e] [":" (Combinatorics.Quiver.«term_⟶_» `P " ⟶ " `Q)] [] ")")
  (Term.explicitBinder
   "("
   [`zero]
   [":" (Combinatorics.Quiver.«term_⟶_» (Term.app `P.X [(numLit "0")]) " ⟶ " (Term.app `Q.X [(numLit "1")]))]
   []
   ")")
  (Term.explicitBinder
   "("
   [`comm_zero]
   [":"
    («term_=_»
     (Term.app `e.f [(numLit "0")])
     "="
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `zero " ≫ " (Term.app `Q.d [(numLit "1") (numLit "0")])))]
   []
   ")")
  (Term.explicitBinder
   "("
   [`one]
   [":" (Combinatorics.Quiver.«term_⟶_» (Term.app `P.X [(numLit "1")]) " ⟶ " (Term.app `Q.X [(numLit "2")]))]
   []
   ")")
  (Term.explicitBinder
   "("
   [`comm_one]
   [":"
    («term_=_»
     (Term.app `e.f [(numLit "1")])
     "="
     (Init.Logic.«term_+_»
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `P.d [(numLit "1") (numLit "0")]) " ≫ " `zero)
      "+"
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `one " ≫ " (Term.app `Q.d [(numLit "2") (numLit "1")]))))]
   []
   ")")
  (Term.explicitBinder
   "("
   [`succ]
   [":"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])
      (Term.simpleBinder
       [`p]
       [(Term.typeSpec
         ":"
         (Init.Data.Sigma.Basic.«termΣ'_,_»
          "Σ'"
          (Lean.explicitBinders
           [(Lean.bracketedExplicitBinders
             "("
             [(Lean.binderIdent `f)]
             ":"
             (Combinatorics.Quiver.«term_⟶_»
              (Term.app `P.X [`n])
              " ⟶ "
              (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
             ")")
            (Lean.bracketedExplicitBinders
             "("
             [(Lean.binderIdent `f')]
             ":"
             (Combinatorics.Quiver.«term_⟶_»
              (Term.app `P.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
              " ⟶ "
              (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))
             ")")])
          ", "
          («term_=_»
           (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
           "="
           (Init.Logic.«term_+_»
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
             " ≫ "
             `f)
            "+"
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             `f'
             " ≫ "
             (Term.app
              `Q.d
              [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))))))])]
     ","
     (Init.Data.Sigma.Basic.«termΣ'_,_»
      "Σ'"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `f'')]
        [":"
         (Combinatorics.Quiver.«term_⟶_»
          (Term.app `P.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
          " ⟶ "
          (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "3"))]))]))
      ", "
      («term_=_»
       (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
       "="
       (Init.Logic.«term_+_»
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
         " ≫ "
         (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))
        "+"
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         `f''
         " ≫ "
         (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "3")) (Init.Logic.«term_+_» `n "+" (numLit "2"))]))))))]
   []
   ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.variable', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.variable', expected 'Lean.Parser.Command.variable.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])
    (Term.simpleBinder
     [`p]
     [(Term.typeSpec
       ":"
       (Init.Data.Sigma.Basic.«termΣ'_,_»
        "Σ'"
        (Lean.explicitBinders
         [(Lean.bracketedExplicitBinders
           "("
           [(Lean.binderIdent `f)]
           ":"
           (Combinatorics.Quiver.«term_⟶_»
            (Term.app `P.X [`n])
            " ⟶ "
            (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
           ")")
          (Lean.bracketedExplicitBinders
           "("
           [(Lean.binderIdent `f')]
           ":"
           (Combinatorics.Quiver.«term_⟶_»
            (Term.app `P.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
            " ⟶ "
            (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))
           ")")])
        ", "
        («term_=_»
         (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
         "="
         (Init.Logic.«term_+_»
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
           " ≫ "
           `f)
          "+"
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           `f'
           " ≫ "
           (Term.app
            `Q.d
            [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))))))])]
   ","
   (Init.Data.Sigma.Basic.«termΣ'_,_»
    "Σ'"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `f'')]
      [":"
       (Combinatorics.Quiver.«term_⟶_»
        (Term.app `P.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
        " ⟶ "
        (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "3"))]))]))
    ", "
    («term_=_»
     (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
     "="
     (Init.Logic.«term_+_»
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
       " ≫ "
       (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))
      "+"
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       `f''
       " ≫ "
       (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "3")) (Init.Logic.«term_+_» `n "+" (numLit "2"))]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ'_,_»
   "Σ'"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `f'')]
     [":"
      (Combinatorics.Quiver.«term_⟶_»
       (Term.app `P.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
       " ⟶ "
       (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "3"))]))]))
   ", "
   («term_=_»
    (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
    "="
    (Init.Logic.«term_+_»
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
      " ≫ "
      (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))
     "+"
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      `f''
      " ≫ "
      (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "3")) (Init.Logic.«term_+_» `n "+" (numLit "2"))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
   "="
   (Init.Logic.«term_+_»
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
     " ≫ "
     (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))
    "+"
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `f''
     " ≫ "
     (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "3")) (Init.Logic.«term_+_» `n "+" (numLit "2"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
    " ≫ "
    (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))
   "+"
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    `f''
    " ≫ "
    (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "3")) (Init.Logic.«term_+_» `n "+" (numLit "2"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `f''
   " ≫ "
   (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "3")) (Init.Logic.«term_+_» `n "+" (numLit "2"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "3")) (Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "3"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "3")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "3")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Q.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f''
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
   " ≫ "
   (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app
    `P.d
    [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
     (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")])
   " ≫ "
   (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `e.f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable
  ( e : P ⟶ Q )
    ( zero : P.X 0 ⟶ Q.X 1 )
    ( comm_zero : e.f 0 = zero ≫ Q.d 1 0 )
    ( one : P.X 1 ⟶ Q.X 2 )
    ( comm_one : e.f 1 = P.d 1 0 ≫ zero + one ≫ Q.d 2 1 )
    (
      succ
      :
        ∀
          n : ℕ
            p
              :
                Σ'
                  ( f : P.X n ⟶ Q.X n + 1 ) ( f' : P.X n + 1 ⟶ Q.X n + 2 )
                  ,
                  e.f n + 1 = P.d n + 1 n ≫ f + f' ≫ Q.d n + 2 n + 1
          ,
          Σ' f'' : P.X n + 2 ⟶ Q.X n + 3 , e.f n + 2 = P.d n + 2 n + 1 ≫ p . 2 . 1 + f'' ≫ Q.d n + 3 n + 2
      )

include comm_one comm_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nAn auxiliary construction for `mk_inductive`.\n\nHere we build by induction a family of diagrams,\nbut don't require at the type level that these successive diagrams actually agree.\nThey do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)\nin `mk_inductive`.\n\nAt this stage, we don't check the homotopy condition in degree 0,\nbecause it \"falls off the end\", and is easier to treat using `X_next` and `X_prev`,\nwhich we do in `mk_inductive_aux₂`.\n-/")]
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Mathlib.Tactic.Lint.nolint "nolint" [`unused_arguments]))]
    "]")]
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `mk_inductive_aux₁ [])
  (Command.optDeclSig
   []
   [(Term.typeSpec
     ":"
     (Term.forall
      "∀"
      [(Term.simpleBinder [`n] [])]
      ","
      (Init.Data.Sigma.Basic.«termΣ'_,_»
       "Σ'"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent `f)]
          ":"
          (Combinatorics.Quiver.«term_⟶_»
           (Term.app `P.X [`n])
           " ⟶ "
           (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
          ")")
         (Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent `f')]
          ":"
          (Combinatorics.Quiver.«term_⟶_»
           (Term.app `P.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
           " ⟶ "
           (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))
          ")")])
       ", "
       («term_=_»
        (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
        "="
        (Init.Logic.«term_+_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
          " ≫ "
          `f)
         "+"
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          `f'
          " ≫ "
          (Term.app
           `Q.d
           [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])))))))])
  (Command.declValEqns
   (Term.matchAltsWhereDecls
    (Term.matchAlts
     [(Term.matchAlt "|" [(numLit "0")] "=>" (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩"))
      (Term.matchAlt
       "|"
       [(numLit "1")]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [`one
         ","
         (Term.proj
          (Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")])
          "."
          (fieldIdx "1"))
         ","
         (Term.proj
          (Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")])
          "."
          (fieldIdx "2"))]
        "⟩"))
      (Term.matchAlt
       "|"
       [(Init.Logic.«term_+_» `n "+" (numLit "2"))]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Term.proj
          (Term.proj (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." (fieldIdx "2"))
          "."
          (fieldIdx "1"))
         ","
         (Term.proj
          (Term.app
           `succ
           [(Init.Logic.«term_+_» `n "+" (numLit "1"))
            (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
          "."
          (fieldIdx "1"))
         ","
         (Term.proj
          (Term.app
           `succ
           [(Init.Logic.«term_+_» `n "+" (numLit "1"))
            (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
          "."
          (fieldIdx "2"))]
        "⟩"))])
    []))
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAltsWhereDecls', expected 'Lean.Parser.Term.matchAltsWhereDecls.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.proj
     (Term.proj (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." (fieldIdx "2"))
     "."
     (fieldIdx "1"))
    ","
    (Term.proj
     (Term.app
      `succ
      [(Init.Logic.«term_+_» `n "+" (numLit "1"))
       (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
     "."
     (fieldIdx "1"))
    ","
    (Term.proj
     (Term.app
      `succ
      [(Init.Logic.«term_+_» `n "+" (numLit "1"))
       (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
     "."
     (fieldIdx "2"))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `succ
    [(Init.Logic.«term_+_» `n "+" (numLit "1"))
     (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
   "."
   (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `succ
   [(Init.Logic.«term_+_» `n "+" (numLit "1"))
    (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mk_inductive_aux₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `mk_inductive_aux₁ [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `succ
   [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
    (Term.paren
     "("
     [(Term.app `mk_inductive_aux₁ [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")]) []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `succ
    [(Init.Logic.«term_+_» `n "+" (numLit "1"))
     (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
   "."
   (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `succ
   [(Init.Logic.«term_+_» `n "+" (numLit "1"))
    (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mk_inductive_aux₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `mk_inductive_aux₁ [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `succ
   [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
    (Term.paren
     "("
     [(Term.app `mk_inductive_aux₁ [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")]) []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.proj (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." (fieldIdx "2"))
   "."
   (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `mk_inductive_aux₁ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mk_inductive_aux₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `mk_inductive_aux₁ [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`one
    ","
    (Term.proj
     (Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")])
     "."
     (fieldIdx "1"))
    ","
    (Term.proj
     (Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")])
     "."
     (fieldIdx "2"))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")])
   "."
   (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comm_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")])
   "."
   (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comm_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `succ [(numLit "0") (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`zero "," `one "," `comm_one] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comm_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`n] [])]
   ","
   (Init.Data.Sigma.Basic.«termΣ'_,_»
    "Σ'"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent `f)]
       ":"
       (Combinatorics.Quiver.«term_⟶_»
        (Term.app `P.X [`n])
        " ⟶ "
        (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
       ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent `f')]
       ":"
       (Combinatorics.Quiver.«term_⟶_»
        (Term.app `P.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
        " ⟶ "
        (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))
       ")")])
    ", "
    («term_=_»
     (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
     "="
     (Init.Logic.«term_+_»
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
       " ≫ "
       `f)
      "+"
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       `f'
       " ≫ "
       (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ'_,_»
   "Σ'"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `f)]
      ":"
      (Combinatorics.Quiver.«term_⟶_»
       (Term.app `P.X [`n])
       " ⟶ "
       (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
      ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `f')]
      ":"
      (Combinatorics.Quiver.«term_⟶_»
       (Term.app `P.X [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
       " ⟶ "
       (Term.app `Q.X [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))
      ")")])
   ", "
   («term_=_»
    (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
    "="
    (Init.Logic.«term_+_»
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
      " ≫ "
      `f)
     "+"
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      `f'
      " ≫ "
      (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
   "="
   (Init.Logic.«term_+_»
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
     " ≫ "
     `f)
    "+"
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `f'
     " ≫ "
     (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
    " ≫ "
    `f)
   "+"
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    `f'
    " ≫ "
    (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `f'
   " ≫ "
   (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Q.d [(Init.Logic.«term_+_» `n "+" (numLit "2")) (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Q.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
   " ≫ "
   `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `P.d [(Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P.d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `P.d [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")") `n])
   " ≫ "
   `f)
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `e.f [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `e.f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      An auxiliary construction for `mk_inductive`.
      
      Here we build by induction a family of diagrams,
      but don't require at the type level that these successive diagrams actually agree.
      They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
      in `mk_inductive`.
      
      At this stage, we don't check the homotopy condition in degree 0,
      because it "falls off the end", and is easier to treat using `X_next` and `X_prev`,
      which we do in `mk_inductive_aux₂`.
      -/
    @[ simp , nolint unused_arguments ]
  def
    mk_inductive_aux₁
    :
      ∀
        n
        ,
        Σ' ( f : P.X n ⟶ Q.X n + 1 ) ( f' : P.X n + 1 ⟶ Q.X n + 2 ) , e.f n + 1 = P.d n + 1 n ≫ f + f' ≫ Q.d n + 2 n + 1
    | 0 => ⟨ zero , one , comm_one ⟩
      | 1 => ⟨ one , succ 0 ⟨ zero , one , comm_one ⟩ . 1 , succ 0 ⟨ zero , one , comm_one ⟩ . 2 ⟩
      |
        n + 2
        =>
        ⟨
          mk_inductive_aux₁ n + 1 . 2 . 1
            ,
            succ n + 1 mk_inductive_aux₁ n + 1 . 1
            ,
            succ n + 1 mk_inductive_aux₁ n + 1 . 2
          ⟩

section

variable [has_zero_object V]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "\nAn auxiliary construction for `mk_inductive`.\n-/")]
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `mk_inductive_aux₂ [])
  (Command.optDeclSig
   []
   [(Term.typeSpec
     ":"
     (Term.forall
      "∀"
      [(Term.simpleBinder [`n] [])]
      ","
      (Init.Data.Sigma.Basic.«termΣ'_,_»
       "Σ'"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent `f)]
          ":"
          (Combinatorics.Quiver.«term_⟶_» (Term.app `P.X_next [`n]) " ⟶ " (Term.app `Q.X [`n]))
          ")")
         (Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent `f')]
          ":"
          (Combinatorics.Quiver.«term_⟶_» (Term.app `P.X [`n]) " ⟶ " (Term.app `Q.X_prev [`n]))
          ")")])
       ", "
       («term_=_»
        (Term.app `e.f [`n])
        "="
        (Init.Logic.«term_+_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `P.d_from [`n]) " ≫ " `f)
         "+"
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f' " ≫ " (Term.app `Q.d_to [`n])))))))])
  (Command.declValEqns
   (Term.matchAltsWhereDecls
    (Term.matchAlts
     [(Term.matchAlt
       "|"
       [(numLit "0")]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(numLit "0")
         ","
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          `zero
          " ≫ "
          (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv))
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `comm_zero]) [])])))]
        "⟩"))
      (Term.matchAlt
       "|"
       [(Init.Logic.«term_+_» `n "+" (numLit "1"))]
       "=>"
       (Term.let
        "let"
        (Term.letDecl
         (Term.letIdDecl `I [] [] ":=" (Term.app `mk_inductive_aux₁ [`e `zero `comm_zero `one `comm_one `succ `n])))
        []
        (Term.anonymousCtor
         "⟨"
         [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.proj (Term.app `P.X_next_iso [`rfl]) "." `Hom)
           " ≫ "
           (Term.proj `I "." (fieldIdx "1")))
          ","
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "1"))
           " ≫ "
           (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv))
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simpa
                "simpa"
                []
                []
                []
                []
                ["using" (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "2"))])
               [])])))]
         "⟩")))])
    []))
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAltsWhereDecls', expected 'Lean.Parser.Term.matchAltsWhereDecls.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl `I [] [] ":=" (Term.app `mk_inductive_aux₁ [`e `zero `comm_zero `one `comm_one `succ `n])))
   []
   (Term.anonymousCtor
    "⟨"
    [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.proj (Term.app `P.X_next_iso [`rfl]) "." `Hom)
      " ≫ "
      (Term.proj `I "." (fieldIdx "1")))
     ","
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "1"))
      " ≫ "
      (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv))
     ","
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "2"))])
          [])])))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.proj (Term.app `P.X_next_iso [`rfl]) "." `Hom)
     " ≫ "
     (Term.proj `I "." (fieldIdx "1")))
    ","
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "1"))
     " ≫ "
     (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv))
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "2"))])
         [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "2"))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `I "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "1"))
   " ≫ "
   (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Q.X_prev_iso [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Q.X_prev_iso
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Q.X_prev_iso [`rfl]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.proj (Term.proj `I "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `I "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.proj (Term.app `P.X_next_iso [`rfl]) "." `Hom)
   " ≫ "
   (Term.proj `I "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `I "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.proj (Term.app `P.X_next_iso [`rfl]) "." `Hom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `P.X_next_iso [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P.X_next_iso
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `P.X_next_iso [`rfl]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `mk_inductive_aux₁ [`e `zero `comm_zero `one `comm_one `succ `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `comm_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `comm_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mk_inductive_aux₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(numLit "0")
    ","
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     `zero
     " ≫ "
     (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv))
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `comm_zero]) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `comm_zero]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" `comm_zero])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comm_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   `zero
   " ≫ "
   (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `Q.X_prev_iso [`rfl]) "." `inv)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Q.X_prev_iso [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Q.X_prev_iso
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Q.X_prev_iso [`rfl]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`n] [])]
   ","
   (Init.Data.Sigma.Basic.«termΣ'_,_»
    "Σ'"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent `f)]
       ":"
       (Combinatorics.Quiver.«term_⟶_» (Term.app `P.X_next [`n]) " ⟶ " (Term.app `Q.X [`n]))
       ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent `f')]
       ":"
       (Combinatorics.Quiver.«term_⟶_» (Term.app `P.X [`n]) " ⟶ " (Term.app `Q.X_prev [`n]))
       ")")])
    ", "
    («term_=_»
     (Term.app `e.f [`n])
     "="
     (Init.Logic.«term_+_»
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `P.d_from [`n]) " ≫ " `f)
      "+"
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f' " ≫ " (Term.app `Q.d_to [`n]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ'_,_»
   "Σ'"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `f)]
      ":"
      (Combinatorics.Quiver.«term_⟶_» (Term.app `P.X_next [`n]) " ⟶ " (Term.app `Q.X [`n]))
      ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `f')]
      ":"
      (Combinatorics.Quiver.«term_⟶_» (Term.app `P.X [`n]) " ⟶ " (Term.app `Q.X_prev [`n]))
      ")")])
   ", "
   («term_=_»
    (Term.app `e.f [`n])
    "="
    (Init.Logic.«term_+_»
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `P.d_from [`n]) " ≫ " `f)
     "+"
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f' " ≫ " (Term.app `Q.d_to [`n])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app `e.f [`n])
   "="
   (Init.Logic.«term_+_»
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `P.d_from [`n]) " ≫ " `f)
    "+"
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f' " ≫ " (Term.app `Q.d_to [`n]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `P.d_from [`n]) " ≫ " `f)
   "+"
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f' " ≫ " (Term.app `Q.d_to [`n])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f' " ≫ " (Term.app `Q.d_to [`n]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Q.d_to [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Q.d_to
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `f'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `P.d_from [`n]) " ≫ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `P.d_from [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P.d_from
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `P.d_from [`n]) " ≫ " `f) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `e.f [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `e.f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      An auxiliary construction for `mk_inductive`.
      -/
    @[ simp ]
  def
    mk_inductive_aux₂
    : ∀ n , Σ' ( f : P.X_next n ⟶ Q.X n ) ( f' : P.X n ⟶ Q.X_prev n ) , e.f n = P.d_from n ≫ f + f' ≫ Q.d_to n
    | 0 => ⟨ 0 , zero ≫ Q.X_prev_iso rfl . inv , by simpa using comm_zero ⟩
      |
        n + 1
        =>
        let
          I := mk_inductive_aux₁ e zero comm_zero one comm_one succ n
          ⟨ P.X_next_iso rfl . Hom ≫ I . 1 , I . 2 . 1 ≫ Q.X_prev_iso rfl . inv , by simpa using I . 2 . 2 ⟩

theorem mk_inductive_aux₃ (i : ℕ) :
    (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.X_prev_iso rfl).Hom =
      (P.X_next_iso rfl).inv ≫ (mk_inductive_aux₂ e zero comm_zero one comm_one succ (i+1)).1 :=
  by
  rcases i with (_ | _ | i) <;>
    ·
      dsimp
      simp

/-- 
A constructor for a `homotopy e 0`, for `e` a chain map between `ℕ`-indexed chain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
def mk_inductive : Homotopy e 0 :=
  { Hom := fun i j =>
      if h : (i+1) = j then (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.X_prev_iso h).Hom else 0,
    zero' := fun i j w => by
      rwa [dif_neg],
    comm := fun i => by
      dsimp
      simp only [add_zeroₓ]
      convert (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.2
      ·
        rcases i with (_ | _ | _ | i)
        ·
          dsimp
          simp only [d_next_zero_chain_complex, d_from_eq_zero, limits.comp_zero]
        all_goals
          simp only [d_next_succ_chain_complex]
          dsimp
          simp only [category.comp_id, category.assoc, iso.inv_hom_id, d_from_comp_X_next_iso_assoc, dite_eq_ite,
            if_true, eq_self_iff_true]
      ·
        cases i
        all_goals
          simp only [prev_d_chain_complex]
          dsimp
          simp only [category.comp_id, category.assoc, iso.inv_hom_id, X_prev_iso_comp_d_to, dite_eq_ite, if_true,
            eq_self_iff_true] }

end

end MkInductive

end Homotopy

/-- 
A homotopy equivalence between two chain complexes consists of a chain map each way,
and homotopies from the compositions to the identity chain maps.

Note that this contains data;
arguably it might be more useful for many applications if we truncated it to a Prop.
-/
structure HomotopyEquiv (C D : HomologicalComplex V c) where
  Hom : C ⟶ D
  inv : D ⟶ C
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 C)
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 D)

namespace HomotopyEquiv

/--  Any complex is homotopy equivalent to itself. -/
@[refl]
def refl (C : HomologicalComplex V c) : HomotopyEquiv C C :=
  { Hom := 𝟙 C, inv := 𝟙 C,
    homotopyHomInvId := by
      simp ,
    homotopyInvHomId := by
      simp }

instance : Inhabited (HomotopyEquiv C C) :=
  ⟨refl C⟩

/--  Being homotopy equivalent is a symmetric relation. -/
@[symm]
def symm {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) : HomotopyEquiv D C :=
  { Hom := f.inv, inv := f.hom, homotopyHomInvId := f.homotopy_inv_hom_id, homotopyInvHomId := f.homotopy_hom_inv_id }

/--  Homotopy equivalence is a transitive relation. -/
@[trans]
def trans {C D E : HomologicalComplex V c} (f : HomotopyEquiv C D) (g : HomotopyEquiv D E) : HomotopyEquiv C E :=
  { Hom := f.hom ≫ g.hom, inv := g.inv ≫ f.inv,
    homotopyHomInvId := by
      simpa using ((g.homotopy_hom_inv_id.comp_right_id f.inv).compLeft f.hom).trans f.homotopy_hom_inv_id,
    homotopyInvHomId := by
      simpa using ((f.homotopy_inv_hom_id.comp_right_id g.hom).compLeft g.inv).trans g.homotopy_inv_hom_id }

end HomotopyEquiv

variable [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

variable [has_zero_object V]

/-- 
Homotopic maps induce the same map on homology.
-/
theorem homology_map_eq_of_homotopy (h : Homotopy f g) (i : ι) :
    (homologyFunctor V c i).map f = (homologyFunctor V c i).map g := by
  dsimp [homologyFunctor]
  apply eq_of_sub_eq_zero
  ext
  simp only [homology.π_map, comp_zero, preadditive.comp_sub]
  dsimp [kernel_subobject_map]
  simp_rw [h.comm i]
  simp only [zero_addₓ, zero_comp, d_next_eq_d_from_from_next, kernel_subobject_arrow_comp_assoc, preadditive.comp_add]
  rw [← preadditive.sub_comp]
  simp only [CategoryTheory.Subobject.factor_thru_add_sub_factor_thru_right]
  erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)]
  ·
    simp
  ·
    rw [prev_d_eq_to_prev_d_to, ← category.assoc]
    apply image_subobject_factors_comp_self

/--  Homotopy equivalent complexes have isomorphic homologies. -/
def homologyObjIsoOfHomotopyEquiv (f : HomotopyEquiv C D) (i : ι) :
    (homologyFunctor V c i).obj C ≅ (homologyFunctor V c i).obj D :=
  { Hom := (homologyFunctor V c i).map f.hom, inv := (homologyFunctor V c i).map f.inv,
    hom_inv_id' := by
      rw [← functor.map_comp, homology_map_eq_of_homotopy f.homotopy_hom_inv_id, CategoryTheory.Functor.map_id],
    inv_hom_id' := by
      rw [← functor.map_comp, homology_map_eq_of_homotopy f.homotopy_inv_hom_id, CategoryTheory.Functor.map_id] }

end

namespace CategoryTheory

variable {W : Type _} [category W] [preadditive W]

/--  An additive functor takes homotopies to homotopies. -/
@[simps]
def functor.map_homotopy (F : V ⥤ W) [F.additive] {f g : C ⟶ D} (h : Homotopy f g) :
    Homotopy ((F.map_homological_complex c).map f) ((F.map_homological_complex c).map g) :=
  { Hom := fun i j => F.map (h.hom i j),
    zero' := fun i j w => by
      rw [h.zero i j w, F.map_zero],
    comm := fun i => by
      have := h.comm i
      dsimp [dNext, prevD]  at *
      rcases c.next i with (_ | ⟨inext, wn⟩) <;>
        rcases c.prev i with (_ | ⟨iprev, wp⟩) <;>
          dsimp [dNext, prevD]  at * <;>
            ·
              intro h
              simp [h] }

/--  An additive functor preserves homotopy equivalences. -/
@[simps]
def functor.map_homotopy_equiv (F : V ⥤ W) [F.additive] (h : HomotopyEquiv C D) :
    HomotopyEquiv ((F.map_homological_complex c).obj C) ((F.map_homological_complex c).obj D) :=
  { Hom := (F.map_homological_complex c).map h.hom, inv := (F.map_homological_complex c).map h.inv,
    homotopyHomInvId := by
      rw [← (F.map_homological_complex c).map_comp, ← (F.map_homological_complex c).map_id]
      exact F.map_homotopy h.homotopy_hom_inv_id,
    homotopyInvHomId := by
      rw [← (F.map_homological_complex c).map_comp, ← (F.map_homological_complex c).map_id]
      exact F.map_homotopy h.homotopy_inv_hom_id }

end CategoryTheory

