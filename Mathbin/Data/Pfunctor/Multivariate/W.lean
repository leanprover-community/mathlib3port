/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.pfunctor.multivariate.W
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pfunctor.Multivariate.Basic

/-!
# The W construction as a multivariate polynomial functor.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

W types are well-founded tree-like structures. They are defined
as the least fixpoint of a polynomial functor.

## Main definitions

 * `W_mk`     - constructor
 * `W_dest    - destructor
 * `W_rec`    - recursor: basis for defining functions by structural recursion on `P.W α`
 * `W_rec_eq` - defining equation for `W_rec`
 * `W_ind`    - induction principle for `P.W α`

## Implementation notes

Three views of M-types:

 * `Wp`: polynomial functor
 * `W`: data type inductively defined by a triple:
     shape of the root, data in the root and children of the root
 * `W`: least fixed point of a polynomial functor

Specifically, we define the polynomial functor `Wp` as:

 * A := a tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   (specified inductively by `W_path`) from the root of `t` to any given node.

As a result `Wp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

## Reference

 * Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
   [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u v

namespace MvPFunctor

open TypeVec

open scoped MvFunctor

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

#print MvPFunctor.WPath /-
/-- A path from the root of a tree to one of its node -/
inductive WPath : P.getLast.W → Fin2 n → Type u
  |
  root (a : P.A) (f : P.getLast.B a → P.getLast.W) (i : Fin2 n) (c : P.drop.B a i) : W_path ⟨a, f⟩ i
  |
  child (a : P.A) (f : P.getLast.B a → P.getLast.W) (i : Fin2 n) (j : P.getLast.B a)
    (c : W_path (f j) i) : W_path ⟨a, f⟩ i
#align mvpfunctor.W_path MvPFunctor.WPath
-/

#print MvPFunctor.WPath.inhabited /-
instance WPath.inhabited (x : P.getLast.W) {i} [I : Inhabited (P.drop.B x.headI i)] :
    Inhabited (WPath P x i) :=
  ⟨match x, I with
    | ⟨a, f⟩, I => WPath.root a f i (@default _ I)⟩
#align mvpfunctor.W_path.inhabited MvPFunctor.WPath.inhabited
-/

#print MvPFunctor.wPathCasesOn /-
/-- Specialized destructor on `W_path` -/
def wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.getLast.B a → P.getLast.W} (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.getLast.B a, P.WPath (f j) ⟹ α) : P.WPath ⟨a, f⟩ ⟹ α :=
  by
  intro i x; cases x
  case root _ _ i c => exact g' i c
  case child _ _ i j c => exact g j i c
#align mvpfunctor.W_path_cases_on MvPFunctor.wPathCasesOn
-/

#print MvPFunctor.wPathDestLeft /-
/-- Specialized destructor on `W_path` -/
def wPathDestLeft {α : TypeVec n} {a : P.A} {f : P.getLast.B a → P.getLast.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.drop.B a ⟹ α := fun i c => h i (WPath.root a f i c)
#align mvpfunctor.W_path_dest_left MvPFunctor.wPathDestLeft
-/

#print MvPFunctor.wPathDestRight /-
/-- Specialized destructor on `W_path` -/
def wPathDestRight {α : TypeVec n} {a : P.A} {f : P.getLast.B a → P.getLast.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : ∀ j : P.getLast.B a, P.WPath (f j) ⟹ α := fun j i c =>
  h i (WPath.child a f i j c)
#align mvpfunctor.W_path_dest_right MvPFunctor.wPathDestRight
-/

#print MvPFunctor.wPathDestLeft_wPathCasesOn /-
theorem wPathDestLeft_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.getLast.B a → P.getLast.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.getLast.B a, P.WPath (f j) ⟹ α) :
    P.wPathDestLeft (P.wPathCasesOn g' g) = g' :=
  rfl
#align mvpfunctor.W_path_dest_left_W_path_cases_on MvPFunctor.wPathDestLeft_wPathCasesOn
-/

#print MvPFunctor.wPathDestRight_wPathCasesOn /-
theorem wPathDestRight_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.getLast.B a → P.getLast.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.getLast.B a, P.WPath (f j) ⟹ α) :
    P.wPathDestRight (P.wPathCasesOn g' g) = g :=
  rfl
#align mvpfunctor.W_path_dest_right_W_path_cases_on MvPFunctor.wPathDestRight_wPathCasesOn
-/

#print MvPFunctor.wPathCasesOn_eta /-
theorem wPathCasesOn_eta {α : TypeVec n} {a : P.A} {f : P.getLast.B a → P.getLast.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.wPathCasesOn (P.wPathDestLeft h) (P.wPathDestRight h) = h := by
  ext i x <;> cases x <;> rfl
#align mvpfunctor.W_path_cases_on_eta MvPFunctor.wPathCasesOn_eta
-/

#print MvPFunctor.comp_wPathCasesOn /-
theorem comp_wPathCasesOn {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.getLast.B a → P.getLast.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.getLast.B a, P.WPath (f j) ⟹ α) :
    h ⊚ P.wPathCasesOn g' g = P.wPathCasesOn (h ⊚ g') fun i => h ⊚ g i := by
  ext i x <;> cases x <;> rfl
#align mvpfunctor.comp_W_path_cases_on MvPFunctor.comp_wPathCasesOn
-/

#print MvPFunctor.wp /-
/-- Polynomial functor for the W-type of `P`. `A` is a data-less well-founded
tree whereas, for a given `a : A`, `B a` is a valid path in tree `a` so
that `Wp.obj α` is made of a tree and a function from its valid paths to
the values it contains  -/
def wp : MvPFunctor n where
  A := P.getLast.W
  B := P.WPath
#align mvpfunctor.Wp MvPFunctor.wp
-/

#print MvPFunctor.W /-
/-- W-type of `P` -/
@[nolint has_nonempty_instance]
def W (α : TypeVec n) : Type _ :=
  P.wp.Obj α
#align mvpfunctor.W MvPFunctor.W
-/

#print MvPFunctor.mvfunctorW /-
instance mvfunctorW : MvFunctor P.W := by delta MvPFunctor.W <;> infer_instance
#align mvpfunctor.mvfunctor_W MvPFunctor.mvfunctorW
-/

/-!
First, describe operations on `W` as a polynomial functor.
-/


#print MvPFunctor.wpMk /-
/-- Constructor for `Wp` -/
def wpMk {α : TypeVec n} (a : P.A) (f : P.getLast.B a → P.getLast.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.W α :=
  ⟨⟨a, f⟩, f'⟩
#align mvpfunctor.Wp_mk MvPFunctor.wpMk
-/

#print MvPFunctor.wpRec /-
/-- Recursor for `Wp` -/
def wpRec {α : TypeVec n} {C : Type _}
    (g :
      ∀ (a : P.A) (f : P.getLast.B a → P.getLast.W), P.WPath ⟨a, f⟩ ⟹ α → (P.getLast.B a → C) → C) :
    ∀ (x : P.getLast.W) (f' : P.WPath x ⟹ α), C
  | ⟨a, f⟩, f' => g a f f' fun i => Wp_rec (f i) (P.wPathDestRight f' i)
#align mvpfunctor.Wp_rec MvPFunctor.wpRec
-/

#print MvPFunctor.wpRec_eq /-
theorem wpRec_eq {α : TypeVec n} {C : Type _}
    (g :
      ∀ (a : P.A) (f : P.getLast.B a → P.getLast.W), P.WPath ⟨a, f⟩ ⟹ α → (P.getLast.B a → C) → C)
    (a : P.A) (f : P.getLast.B a → P.getLast.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.wpRec g ⟨a, f⟩ f' = g a f f' fun i => P.wpRec g (f i) (P.wPathDestRight f' i) :=
  rfl
#align mvpfunctor.Wp_rec_eq MvPFunctor.wpRec_eq
-/

#print MvPFunctor.wp_ind /-
-- Note: we could replace Prop by Type* and obtain a dependent recursor
theorem wp_ind {α : TypeVec n} {C : ∀ x : P.getLast.W, P.WPath x ⟹ α → Prop}
    (ih :
      ∀ (a : P.A) (f : P.getLast.B a → P.getLast.W) (f' : P.WPath ⟨a, f⟩ ⟹ α),
        (∀ i : P.getLast.B a, C (f i) (P.wPathDestRight f' i)) → C ⟨a, f⟩ f') :
    ∀ (x : P.getLast.W) (f' : P.WPath x ⟹ α), C x f'
  | ⟨a, f⟩, f' => ih a f f' fun i => Wp_ind _ _
#align mvpfunctor.Wp_ind MvPFunctor.wp_ind
-/

/-!
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
 -/


#print MvPFunctor.wMk /-
/-- Constructor for `W` -/
def wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.getLast.B a → P.W α) : P.W α :=
  let g : P.getLast.B a → P.getLast.W := fun i => (f i).fst
  let g' : P.WPath ⟨a, g⟩ ⟹ α := P.wPathCasesOn f' fun i => (f i).snd
  ⟨⟨a, g⟩, g'⟩
#align mvpfunctor.W_mk MvPFunctor.wMk
-/

#print MvPFunctor.wRec /-
/-- Recursor for `W` -/
def wRec {α : TypeVec n} {C : Type _}
    (g : ∀ a : P.A, P.drop.B a ⟹ α → (P.getLast.B a → P.W α) → (P.getLast.B a → C) → C) : P.W α → C
  | ⟨a, f'⟩ =>
    let g' (a : P.A) (f : P.getLast.B a → P.getLast.W) (h : P.WPath ⟨a, f⟩ ⟹ α)
      (h' : P.getLast.B a → C) : C :=
      g a (P.wPathDestLeft h) (fun i => ⟨f i, P.wPathDestRight h i⟩) h'
    P.wpRec g' a f'
#align mvpfunctor.W_rec MvPFunctor.wRec
-/

#print MvPFunctor.wRec_eq /-
/-- Defining equation for the recursor of `W` -/
theorem wRec_eq {α : TypeVec n} {C : Type _}
    (g : ∀ a : P.A, P.drop.B a ⟹ α → (P.getLast.B a → P.W α) → (P.getLast.B a → C) → C) (a : P.A)
    (f' : P.drop.B a ⟹ α) (f : P.getLast.B a → P.W α) :
    P.wRec g (P.wMk a f' f) = g a f' f fun i => P.wRec g (f i) :=
  by
  rw [W_mk, W_rec]; dsimp; rw [Wp_rec_eq]
  dsimp only [W_path_dest_left_W_path_cases_on, W_path_dest_right_W_path_cases_on]
  congr <;> ext1 i <;> cases f i <;> rfl
#align mvpfunctor.W_rec_eq MvPFunctor.wRec_eq
-/

#print MvPFunctor.w_ind /-
/-- Induction principle for `W` -/
theorem w_ind {α : TypeVec n} {C : P.W α → Prop}
    (ih :
      ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.getLast.B a → P.W α),
        (∀ i, C (f i)) → C (P.wMk a f' f)) :
    ∀ x, C x := by
  intro x; cases' x with a f
  apply @Wp_ind n P α fun a f => C ⟨a, f⟩; dsimp
  intro a f f' ih'
  dsimp [W_mk] at ih 
  let ih'' := ih a (P.W_path_dest_left f') fun i => ⟨f i, P.W_path_dest_right f' i⟩
  dsimp at ih'' ; rw [W_path_cases_on_eta] at ih'' 
  apply ih''
  apply ih'
#align mvpfunctor.W_ind MvPFunctor.w_ind
-/

#print MvPFunctor.w_cases /-
theorem w_cases {α : TypeVec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.getLast.B a → P.W α), C (P.wMk a f' f)) :
    ∀ x, C x :=
  P.w_ind fun a f' f ih' => ih a f' f
#align mvpfunctor.W_cases MvPFunctor.w_cases
-/

#print MvPFunctor.wMap /-
/-- W-types are functorial -/
def wMap {α β : TypeVec n} (g : α ⟹ β) : P.W α → P.W β := fun x => g <$$> x
#align mvpfunctor.W_map MvPFunctor.wMap
-/

#print MvPFunctor.wMk_eq /-
theorem wMk_eq {α : TypeVec n} (a : P.A) (f : P.getLast.B a → P.getLast.W) (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.getLast.B a, P.WPath (f j) ⟹ α) :
    (P.wMk a g' fun i => ⟨f i, g i⟩) = ⟨⟨a, f⟩, P.wPathCasesOn g' g⟩ :=
  rfl
#align mvpfunctor.W_mk_eq MvPFunctor.wMk_eq
-/

#print MvPFunctor.w_map_wMk /-
theorem w_map_wMk {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.getLast.B a → P.W α) : g <$$> P.wMk a f' f = P.wMk a (g ⊚ f') fun i => g <$$> f i :=
  by
  show _ = P.W_mk a (g ⊚ f') (MvFunctor.map g ∘ f)
  have : MvFunctor.map g ∘ f = fun i => ⟨(f i).fst, g ⊚ (f i).snd⟩ := by ext i : 1;
    dsimp [Function.comp]; cases f i; rfl
  rw [this]
  have : f = fun i => ⟨(f i).fst, (f i).snd⟩ := by ext1; cases f x; rfl
  rw [this]; dsimp
  rw [W_mk_eq, W_mk_eq]
  have h := MvPFunctor.map_eq P.Wp g
  rw [h, comp_W_path_cases_on]
#align mvpfunctor.W_map_W_mk MvPFunctor.w_map_wMk
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvPFunctor.objAppend1 /-
-- TODO: this technical theorem is used in one place in constructing the initial algebra.
-- Can it be avoided?
/-- Constructor of a value of `P.obj (α ::: β)` from components.
Useful to avoid complicated type annotation -/
@[reducible]
def objAppend1 {α : TypeVec n} {β : Type _} (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.getLast.B a → β) : P.Obj (α ::: β) :=
  ⟨a, splitFun f' f⟩
#align mvpfunctor.obj_append1 MvPFunctor.objAppend1
-/

#print MvPFunctor.map_objAppend1 /-
theorem map_objAppend1 {α γ : TypeVec n} (g : α ⟹ γ) (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.getLast.B a → P.W α) :
    appendFun g (P.wMap g) <$$> P.objAppend1 a f' f =
      P.objAppend1 a (g ⊚ f') fun x => P.wMap g (f x) :=
  by rw [obj_append1, obj_append1, map_eq, append_fun, ← split_fun_comp] <;> rfl
#align mvpfunctor.map_obj_append1 MvPFunctor.map_objAppend1
-/

/-!
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvPFunctor.wMk' /-
/-- Constructor for the W-type of `P` -/
def wMk' {α : TypeVec n} : P.Obj (α ::: P.W α) → P.W α
  | ⟨a, f⟩ => P.wMk a (dropFun f) (lastFun f)
#align mvpfunctor.W_mk' MvPFunctor.wMk'
-/

#print MvPFunctor.wDest' /-
/-- Destructor for the W-type of `P` -/
def wDest' {α : TypeVec.{u} n} : P.W α → P.Obj (α.append1 (P.W α)) :=
  P.wRec fun a f' f _ => ⟨a, splitFun f' f⟩
#align mvpfunctor.W_dest' MvPFunctor.wDest'
-/

#print MvPFunctor.wDest'_wMk /-
theorem wDest'_wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.getLast.B a → P.W α) :
    P.wDest' (P.wMk a f' f) = ⟨a, splitFun f' f⟩ := by rw [W_dest', W_rec_eq]
#align mvpfunctor.W_dest'_W_mk MvPFunctor.wDest'_wMk
-/

#print MvPFunctor.wDest'_wMk' /-
theorem wDest'_wMk' {α : TypeVec n} (x : P.Obj (α.append1 (P.W α))) : P.wDest' (P.wMk' x) = x := by
  cases' x with a f <;> rw [W_mk', W_dest'_W_mk, split_drop_fun_last_fun]
#align mvpfunctor.W_dest'_W_mk' MvPFunctor.wDest'_wMk'
-/

end MvPFunctor

