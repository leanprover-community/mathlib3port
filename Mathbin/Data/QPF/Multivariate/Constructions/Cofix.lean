/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Control.Functor.Multivariate
import Data.PFunctor.Multivariate.Basic
import Data.PFunctor.Multivariate.M
import Data.QPF.Multivariate.Basic

#align_import data.qpf.multivariate.constructions.cofix from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# The final co-algebra of a multivariate qpf is again a qpf.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For a `(n+1)`-ary QPF `F (α₀,..,αₙ)`, we take the least fixed point of `F` with
regards to its last argument `αₙ`. The result is a `n`-ary functor: `fix F (α₀,..,αₙ₋₁)`.
Making `fix F` into a functor allows us to take the fixed point, compose with other functors
and take a fixed point again.

## Main definitions

 * `cofix.mk`     - constructor
 * `cofix.dest`   - destructor
 * `cofix.corec`  - corecursor: useful for formulating infinite, productive computations
 * `cofix.bisim`  - bisimulation: proof technique to show the equality of possibly infinite values
                    of `cofix F α`

## Implementation notes

For `F` a QPF, we define `cofix F α` in terms of the M-type of the polynomial functor `P` of `F`.
We define the relation `Mcongr` and take its quotient as the definition of `cofix F α`.

`Mcongr` is taken as the weakest bisimulation on M-type. See
[avigad-carneiro-hudon2019] for more details.

## Reference

 * Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
   [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open scoped MvFunctor

namespace MvQPF

open TypeVec MvPFunctor

open MvFunctor (Liftp Liftr)

variable {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [MvFunctor F] [q : MvQPF F]

#print MvQPF.corecF /-
/-- `corecF` is used as a basis for defining the corecursor of `cofix F α`. `corecF`
uses corecursion to construct the M-type generated by `q.P` and uses function on `F`
as a corecursive step -/
def corecF {α : TypeVec n} {β : Type _} (g : β → F (α.append1 β)) : β → q.p.M α :=
  M.corec _ fun x => repr (g x)
#align mvqpf.corecF MvQPF.corecF
-/

#print MvQPF.corecF_eq /-
theorem corecF_eq {α : TypeVec n} {β : Type _} (g : β → F (α.append1 β)) (x : β) :
    M.dest q.p (corecF g x) = appendFun id (corecF g) <$$> repr (g x) := by
  rw [corecF, M.dest_corec]
#align mvqpf.corecF_eq MvQPF.corecF_eq
-/

#print MvQPF.IsPrecongr /-
/-- Characterization of desirable equivalence relations on M-types -/
def IsPrecongr {α : TypeVec n} (r : q.p.M α → q.p.M α → Prop) : Prop :=
  ∀ ⦃x y⦄,
    r x y →
      abs (appendFun id (Quot.mk r) <$$> M.dest q.p x) =
        abs (appendFun id (Quot.mk r) <$$> M.dest q.p y)
#align mvqpf.is_precongr MvQPF.IsPrecongr
-/

#print MvQPF.Mcongr /-
/-- Equivalence relation on M-types representing a value of type `cofix F` -/
def Mcongr {α : TypeVec n} (x y : q.p.M α) : Prop :=
  ∃ r, IsPrecongr r ∧ r x y
#align mvqpf.Mcongr MvQPF.Mcongr
-/

#print MvQPF.Cofix /-
/-- Greatest fixed point of functor F. The result is a functor with one fewer parameters
than the input. For `F a b c` a ternary functor, fix F is a binary functor such that

```lean
cofix F a b = F a b (cofix F a b)
```
-/
def Cofix (F : TypeVec (n + 1) → Type u) [MvFunctor F] [q : MvQPF F] (α : TypeVec n) :=
  Quot (@Mcongr _ F _ q α)
#align mvqpf.cofix MvQPF.Cofix
-/

instance {α : TypeVec n} [Inhabited q.p.A] [∀ i : Fin2 n, Inhabited (α i)] :
    Inhabited (Cofix F α) :=
  ⟨Quot.mk _ default⟩

#print MvQPF.mRepr /-
/-- maps every element of the W type to a canonical representative -/
def mRepr {α : TypeVec n} : q.p.M α → q.p.M α :=
  corecF (abs ∘ M.dest q.p)
#align mvqpf.Mrepr MvQPF.mRepr
-/

#print MvQPF.Cofix.map /-
/-- the map function for the functor `cofix F` -/
def Cofix.map {α β : TypeVec n} (g : α ⟹ β) : Cofix F α → Cofix F β :=
  Quot.lift (fun x : q.p.M α => Quot.mk Mcongr (g <$$> x))
    (by
      rintro aa₁ aa₂ ⟨r, pr, ra₁a₂⟩; apply Quot.sound
      let r' b₁ b₂ := ∃ a₁ a₂ : q.P.M α, r a₁ a₂ ∧ b₁ = g <$$> a₁ ∧ b₂ = g <$$> a₂
      use r'; constructor
      · show is_precongr r'
        rintro b₁ b₂ ⟨a₁, a₂, ra₁a₂, b₁eq, b₂eq⟩
        let u : Quot r → Quot r' :=
          Quot.lift (fun x : q.P.M α => Quot.mk r' (g <$$> x))
            (by intro a₁ a₂ ra₁a₂; apply Quot.sound; exact ⟨a₁, a₂, ra₁a₂, rfl, rfl⟩)
        have hu : (Quot.mk r' ∘ fun x : q.P.M α => g <$$> x) = u ∘ Quot.mk r := by ext x; rfl
        rw [b₁eq, b₂eq, M.dest_map, M.dest_map, ← q.P.comp_map, ← q.P.comp_map]
        rw [← append_fun_comp, id_comp, hu, hu, ← comp_id g, append_fun_comp]
        rw [q.P.comp_map, q.P.comp_map, abs_map, pr ra₁a₂, ← abs_map]
      show r' (g <$$> aa₁) (g <$$> aa₂); exact ⟨aa₁, aa₂, ra₁a₂, rfl, rfl⟩)
#align mvqpf.cofix.map MvQPF.Cofix.map
-/

#print MvQPF.Cofix.mvfunctor /-
instance Cofix.mvfunctor : MvFunctor (Cofix F) where map := @Cofix.map _ _ _ _
#align mvqpf.cofix.mvfunctor MvQPF.Cofix.mvfunctor
-/

#print MvQPF.Cofix.corec /-
/-- Corecursor for `cofix F` -/
def Cofix.corec {α : TypeVec n} {β : Type u} (g : β → F (α.append1 β)) : β → Cofix F α := fun x =>
  Quot.mk _ (corecF g x)
#align mvqpf.cofix.corec MvQPF.Cofix.corec
-/

#print MvQPF.Cofix.dest /-
/-- Destructor for `cofix F` -/
def Cofix.dest {α : TypeVec n} : Cofix F α → F (α.append1 (Cofix F α)) :=
  Quot.lift (fun x => appendFun id (Quot.mk Mcongr) <$$> abs (M.dest q.p x))
    (by
      rintro x y ⟨r, pr, rxy⟩; dsimp
      have : ∀ x y, r x y → Mcongr x y := by intro x y h; exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]; dsimp
      conv =>
        lhs
        rw [append_fun_comp_id, comp_map, ← abs_map, pr rxy, abs_map, ← comp_map, ←
          append_fun_comp_id])
#align mvqpf.cofix.dest MvQPF.Cofix.dest
-/

#print MvQPF.Cofix.abs /-
/-- Abstraction function for `cofix F α` -/
def Cofix.abs {α} : q.p.M α → Cofix F α :=
  Quot.mk _
#align mvqpf.cofix.abs MvQPF.Cofix.abs
-/

#print MvQPF.Cofix.repr /-
/-- Representation function for `cofix F α` -/
def Cofix.repr {α} : Cofix F α → q.p.M α :=
  M.corec _ <| repr ∘ Cofix.dest
#align mvqpf.cofix.repr MvQPF.Cofix.repr
-/

#print MvQPF.Cofix.corec'₁ /-
/-- Corecursor for `cofix F` -/
def Cofix.corec'₁ {α : TypeVec n} {β : Type u} (g : ∀ {X}, (β → X) → F (α.append1 X)) (x : β) :
    Cofix F α :=
  Cofix.corec (fun x => g id) x
#align mvqpf.cofix.corec'₁ MvQPF.Cofix.corec'₁
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvQPF.Cofix.corec' /-
/-- More flexible corecursor for `cofix F`. Allows the return of a fully formed
value instead of making a recursive call -/
def Cofix.corec' {α : TypeVec n} {β : Type u} (g : β → F (α.append1 (Sum (Cofix F α) β))) (x : β) :
    Cofix F α :=
  let f : (α ::: Cofix F α) ⟹ (α ::: Sum (Cofix F α) β) := id ::: Sum.inl
  Cofix.corec (Sum.elim (MvFunctor.map f ∘ Cofix.dest) g) (Sum.inr x : Sum (Cofix F α) β)
#align mvqpf.cofix.corec' MvQPF.Cofix.corec'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvQPF.Cofix.corec₁ /-
/-- Corecursor for `cofix F`. The shape allows recursive calls to
look like recursive calls. -/
def Cofix.corec₁ {α : TypeVec n} {β : Type u}
    (g : ∀ {X}, (Cofix F α → X) → (β → X) → β → F (α ::: X)) (x : β) : Cofix F α :=
  Cofix.corec' (fun x => g Sum.inl Sum.inr x) x
#align mvqpf.cofix.corec₁ MvQPF.Cofix.corec₁
-/

#print MvQPF.Cofix.dest_corec /-
theorem Cofix.dest_corec {α : TypeVec n} {β : Type u} (g : β → F (α.append1 β)) (x : β) :
    Cofix.dest (Cofix.corec g x) = appendFun id (Cofix.corec g) <$$> g x :=
  by
  conv =>
    lhs
    rw [cofix.dest, cofix.corec];
  dsimp
  rw [corecF_eq, abs_map, abs_repr, ← comp_map, ← append_fun_comp]; rfl
#align mvqpf.cofix.dest_corec MvQPF.Cofix.dest_corec
-/

#print MvQPF.Cofix.mk /-
/-- constructor for `cofix F` -/
def Cofix.mk {α : TypeVec n} : F (α.append1 <| Cofix F α) → Cofix F α :=
  Cofix.corec fun x => (appendFun id fun i : Cofix F α => Cofix.dest.{u} i) <$$> x
#align mvqpf.cofix.mk MvQPF.Cofix.mk
-/

/-!
## Bisimulation principles for `cofix F`

The following theorems are bisimulation principles. The general idea
is to use a bisimulation relation to prove the equality between
specific values of type `cofix F α`.

A bisimulation relation `R` for values `x y : cofix F α`:

 * holds for `x y`: `R x y`
 * for any values `x y` that satisfy `R`, their root has the same shape
   and their children can be paired in such a way that they satisfy `R`.

-/


private theorem cofix.bisim_aux {α : TypeVec n} (r : Cofix F α → Cofix F α → Prop) (h' : ∀ x, r x x)
    (h :
      ∀ x y,
        r x y →
          appendFun id (Quot.mk r) <$$> Cofix.dest x = appendFun id (Quot.mk r) <$$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  intro x; apply Quot.inductionOn x; clear x
  intro x y; apply Quot.inductionOn y; clear y
  intro y rxy
  apply Quot.sound
  let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  have : is_precongr r' := by
    intro a b r'ab
    have h₀ :
      append_fun id (Quot.mk r ∘ Quot.mk Mcongr) <$$> abs (M.dest q.P a) =
        append_fun id (Quot.mk r ∘ Quot.mk Mcongr) <$$> abs (M.dest q.P b) :=
      by rw [append_fun_comp_id, comp_map, comp_map] <;> exact h _ _ r'ab
    have h₁ : ∀ u v : q.P.M α, Mcongr u v → Quot.mk r' u = Quot.mk r' v := by intro u v cuv;
      apply Quot.sound; dsimp [r']; rw [Quot.sound cuv]; apply h'
    let f : Quot r → Quot r' :=
      Quot.lift (Quot.lift (Quot.mk r') h₁)
        (by
          intro c; apply Quot.inductionOn c; clear c
          intro c d; apply Quot.inductionOn d; clear d
          intro d rcd; apply Quot.sound; apply rcd)
    have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
    rw [← this, append_fun_comp_id, q.P.comp_map, q.P.comp_map, abs_map, abs_map, abs_map, abs_map,
      h₀]
  refine' ⟨r', this, rxy⟩

#print MvQPF.Cofix.bisim_rel /-
/-- Bisimulation principle using `map` and `quot.mk` to match and relate children of two trees. -/
theorem Cofix.bisim_rel {α : TypeVec n} (r : Cofix F α → Cofix F α → Prop)
    (h :
      ∀ x y,
        r x y →
          appendFun id (Quot.mk r) <$$> Cofix.dest x = appendFun id (Quot.mk r) <$$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply cofix.bisim_aux r'
  · intro x; left; rfl
  · intro x y r'xy
    cases r'xy; · rw [r'xy]
    have : ∀ x y, r x y → r' x y := fun x y h => Or.inr h
    rw [← Quot.factor_mk_eq _ _ this]; dsimp
    rw [append_fun_comp_id, append_fun_comp_id]
    rw [@comp_map _ _ _ q _ _ _ (append_fun id (Quot.mk r)),
      @comp_map _ _ _ q _ _ _ (append_fun id (Quot.mk r))]
    rw [h _ _ r'xy]
  right; exact rxy
#align mvqpf.cofix.bisim_rel MvQPF.Cofix.bisim_rel
-/

#print MvQPF.Cofix.bisim /-
/-- Bisimulation principle using `liftr` to match and relate children of two trees. -/
theorem Cofix.bisim {α : TypeVec n} (r : Cofix F α → Cofix F α → Prop)
    (h : ∀ x y, r x y → LiftR (RelLast α r) (Cofix.dest x) (Cofix.dest y)) : ∀ x y, r x y → x = y :=
  by
  apply cofix.bisim_rel
  intro x y rxy
  rcases(liftr_iff (rel_last α r) _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq, dyeq, ← abs_map, ← abs_map, MvPFunctor.map_eq, MvPFunctor.map_eq]
  rw [← split_drop_fun_last_fun f₀, ← split_drop_fun_last_fun f₁]
  rw [append_fun_comp_split_fun, append_fun_comp_split_fun]
  rw [id_comp, id_comp]
  congr 2 with (i j); cases' i with _ i <;> dsimp
  · apply Quot.sound; apply h' _ j
  · change f₀ _ j = f₁ _ j; apply h' _ j
#align mvqpf.cofix.bisim MvQPF.Cofix.bisim
-/

open MvFunctor

#print MvQPF.Cofix.bisim₂ /-
/-- Bisimulation principle using `liftr'` to match and relate children of two trees. -/
theorem Cofix.bisim₂ {α : TypeVec n} (r : Cofix F α → Cofix F α → Prop)
    (h : ∀ x y, r x y → LiftR' (RelLast' α r) (Cofix.dest x) (Cofix.dest y)) :
    ∀ x y, r x y → x = y :=
  Cofix.bisim _ <| by intros <;> rw [← liftr_last_rel_iff] <;> apply h <;> assumption
#align mvqpf.cofix.bisim₂ MvQPF.Cofix.bisim₂
-/

#print MvQPF.Cofix.bisim' /-
/-- Bisimulation principle the values `⟨a,f⟩` of the polynomial functor representing
`cofix F α` as well as an invariant `Q : β → Prop` and a state `β` generating the
left-hand side and right-hand side of the equality through functions `u v : β → cofix F α` -/
theorem Cofix.bisim' {α : TypeVec n} {β : Type _} (Q : β → Prop) (u v : β → Cofix F α)
    (h :
      ∀ x,
        Q x →
          ∃ a f' f₀ f₁,
            Cofix.dest (u x) = abs ⟨a, q.p.appendContents f' f₀⟩ ∧
              Cofix.dest (v x) = abs ⟨a, q.p.appendContents f' f₁⟩ ∧
                ∀ i, ∃ x', Q x' ∧ f₀ i = u x' ∧ f₁ i = v x') :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : Cofix F α => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ =>
      by
      rcases h x' Qx' with ⟨a, f', f₀, f₁, ux'eq, vx'eq, h'⟩
      rw [liftr_iff]
      refine'
        ⟨a, q.P.append_contents f' f₀, q.P.append_contents f' f₁, xeq.symm ▸ ux'eq,
          yeq.symm ▸ vx'eq, _⟩
      intro i; cases i
      · apply h'
      · intro j; apply Eq.refl)
    _ _ ⟨x, Qx, rfl, rfl⟩
#align mvqpf.cofix.bisim' MvQPF.Cofix.bisim'
-/

#print MvQPF.Cofix.mk_dest /-
theorem Cofix.mk_dest {α : TypeVec n} (x : Cofix F α) : Cofix.mk (Cofix.dest x) = x :=
  by
  apply cofix.bisim_rel (fun x y : cofix F α => x = cofix.mk (cofix.dest y)) _ _ _ rfl; dsimp
  intro x y h; rw [h]
  conv =>
    lhs
    congr
    skip
    rw [cofix.mk]
    rw [cofix.dest_corec]
  rw [← comp_map, ← append_fun_comp, id_comp]
  rw [← comp_map, ← append_fun_comp, id_comp, ← cofix.mk]
  congr 2 with u; apply Quot.sound; rfl
#align mvqpf.cofix.mk_dest MvQPF.Cofix.mk_dest
-/

#print MvQPF.Cofix.dest_mk /-
theorem Cofix.dest_mk {α : TypeVec n} (x : F (α.append1 <| Cofix F α)) :
    Cofix.dest (Cofix.mk x) = x :=
  by
  have : cofix.mk ∘ cofix.dest = @_root_.id (cofix F α) := funext cofix.mk_dest
  rw [cofix.mk, cofix.dest_corec, ← comp_map, ← cofix.mk, ← append_fun_comp, this, id_comp,
    append_fun_id_id, MvFunctor.id_map]
#align mvqpf.cofix.dest_mk MvQPF.Cofix.dest_mk
-/

#print MvQPF.Cofix.ext /-
theorem Cofix.ext {α : TypeVec n} (x y : Cofix F α) (h : x.dest = y.dest) : x = y := by
  rw [← cofix.mk_dest x, h, cofix.mk_dest]
#align mvqpf.cofix.ext MvQPF.Cofix.ext
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvQPF.Cofix.ext_mk /-
theorem Cofix.ext_mk {α : TypeVec n} (x y : F (α ::: Cofix F α)) (h : Cofix.mk x = Cofix.mk y) :
    x = y := by rw [← cofix.dest_mk x, h, cofix.dest_mk]
#align mvqpf.cofix.ext_mk MvQPF.Cofix.ext_mk
-/

/-!
`liftr_map`, `liftr_map_last` and `liftr_map_last'` are useful for reasoning about
the induction step in bisimulation proofs.
-/


section LiftrMap

#print MvQPF.liftR_map /-
theorem liftR_map {α β : TypeVec n} {F' : TypeVec n → Type u} [MvFunctor F'] [LawfulMvFunctor F']
    (R : β ⊗ β ⟹ repeat n Prop) (x : F' α) (f g : α ⟹ β) (h : α ⟹ Subtype_ R)
    (hh : subtypeVal _ ⊚ h = (f ⊗' g) ⊚ prod.diag) : LiftR' R (f <$$> x) (g <$$> x) :=
  by
  rw [liftr_def]
  exists h <$$> x
  rw [MvFunctor.map_map, comp_assoc, hh, ← comp_assoc, fst_prod_mk, comp_assoc, fst_diag]
  rw [MvFunctor.map_map, comp_assoc, hh, ← comp_assoc, snd_prod_mk, comp_assoc, snd_diag]
  dsimp [liftr']; constructor <;> rfl
#align mvqpf.liftr_map MvQPF.liftR_map
-/

open Function

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvQPF.liftR_map_last /-
theorem liftR_map_last [LawfulMvFunctor F] {α : TypeVec n} {ι ι'} (R : ι' → ι' → Prop)
    (x : F (α ::: ι)) (f g : ι → ι') (hh : ∀ x : ι, R (f x) (g x)) :
    LiftR' (RelLast' _ R) ((id ::: f) <$$> x) ((id ::: g) <$$> x) :=
  let h : ι → { x : ι' × ι' // uncurry R x } := fun x => ⟨(f x, g x), hh x⟩
  let b : (α ::: ι) ⟹ _ := @diagSub n α ::: h
  let c :
    (Subtype_ α.repeatEq ::: { x // uncurry R x }) ⟹
      ((fun i : Fin2 n => { x // ofRepeat (α.RelLast' R i.fs x) }) ::: Subtype (uncurry R)) :=
    ofSubtype _ ::: id
  have hh :
    subtypeVal _ ⊚ toSubtype _ ⊚ fromAppend1DropLast ⊚ c ⊚ b =
      ((id ::: f) ⊗' (id ::: g)) ⊚ prod.diag :=
    by
    dsimp [c, b]
    apply eq_of_drop_last_eq
    · dsimp
      simp only [prod_map_id, drop_fun_prod, drop_fun_append_fun, drop_fun_diag, id_comp,
        drop_fun_to_subtype]
      erw [to_subtype_of_subtype_assoc, id_comp]
      clear * -
      ext i x : 2; induction i
      rfl; apply i_ih
    simp only [h, last_fun_from_append1_drop_last, last_fun_to_subtype, last_fun_append_fun,
      last_fun_subtype_val, comp.left_id, last_fun_comp, last_fun_prod]
    dsimp; ext1; rfl
  liftR_map _ _ _ _ (toSubtype _ ⊚ fromAppend1DropLast ⊚ c ⊚ b) hh
#align mvqpf.liftr_map_last MvQPF.liftR_map_last
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvQPF.liftR_map_last' /-
theorem liftR_map_last' [LawfulMvFunctor F] {α : TypeVec n} {ι} (R : ι → ι → Prop) (x : F (α ::: ι))
    (f : ι → ι) (hh : ∀ x : ι, R (f x) x) : LiftR' (RelLast' _ R) ((id ::: f) <$$> x) x :=
  by
  have := liftr_map_last R x f id hh
  rwa [append_fun_id_id, MvFunctor.id_map] at this
#align mvqpf.liftr_map_last' MvQPF.liftR_map_last'
-/

end LiftrMap

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvQPF.Cofix.abs_repr /-
theorem Cofix.abs_repr {α} (x : Cofix F α) : Quot.mk _ (Cofix.repr x) = x :=
  by
  let R := fun x y : cofix F α => cofix.abs (cofix.repr y) = x
  refine' cofix.bisim₂ R _ _ _ rfl
  clear x; rintro x y h; dsimp [R] at h; subst h
  dsimp [cofix.dest, cofix.abs]
  induction y using Quot.ind
  simp only [cofix.repr, M.dest_corec, abs_map, abs_repr]
  conv =>
    congr
    skip
    rw [cofix.dest]
  dsimp; rw [MvFunctor.map_map, MvFunctor.map_map, ← append_fun_comp_id, ← append_fun_comp_id]
  let f : (α ::: (P F).M α) ⟹ subtype_ (α.rel_last' R) :=
    split_fun diag_sub fun x => ⟨(cofix.abs (cofix.abs x).repr, cofix.abs x), _⟩
  refine' liftr_map _ _ _ _ f _
  · simp only [← append_prod_append_fun, prod_map_id]
    apply eq_of_drop_last_eq
    · dsimp; simp only [drop_fun_diag]
      erw [subtype_val_diag_sub]
    ext1
    simp only [cofix.abs, Prod.mk.inj_iff, Prod_map, Function.comp_apply, last_fun_append_fun,
      last_fun_subtype_val, last_fun_comp, last_fun_split_fun]
    dsimp [drop_fun_rel_last, last_fun, prod.diag]
    constructor <;> rfl
  dsimp [rel_last', split_fun, Function.uncurry, R]
  rfl
#align mvqpf.cofix.abs_repr MvQPF.Cofix.abs_repr
-/

section Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
open Tactic

/-- tactic for proof by bisimulation -/
unsafe def mv_bisim (e : parse texpr) (ids : parse with_ident_list) : tactic Unit := do
  let e ← to_expr e
  let expr.pi n bi d b ←
    retrieve do
        generalize e
        target
  let q(@Eq $(t) $(l) $(r)) ← pure b
  let x ← mk_local_def `n d
  let v₀ ← mk_local_def `a t
  let v₁ ← mk_local_def `b t
  let x₀ ← mk_app `` Eq [v₀, l.instantiate_var x]
  let x₁ ← mk_app `` Eq [v₁, r.instantiate_var x]
  let xx ← mk_app `` And [x₀, x₁]
  let ex ← lambdas [x] xx
  let ex ← mk_app `` Exists [ex] >>= lambdas [v₀, v₁]
  let R ← pose `R none ex
  refine ``(Cofix.bisim₂ $(R) _ _ _ ⟨_, rfl, rfl⟩)
  let f (a b : Name) : Name := if a = `_ then b else a
  let ids := (ids ++ List.replicate 5 `_).zipWith f [`a, `b, `x, `Ha, `Hb]
  let (ids₀, w :: ids₁) ← pure <| List.splitAt 2 ids
  intro_lst ids₀
  let h ← intro1
  let [(_, [w, h], _)] ← cases_core h [w]
  cases h ids₁
  pure ()
#align mvqpf.mv_bisim mvqpf.mv_bisim

run_cmd
  add_interactive [`` mv_bisim]

end Tactic

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvQPF.corec_roll /-
theorem corec_roll {α : TypeVec n} {X Y} {x₀ : X} (f : X → Y) (g : Y → F (α ::: X)) :
    Cofix.corec (g ∘ f) x₀ = Cofix.corec (MvFunctor.map (id ::: f) ∘ g) (f x₀) :=
  by
  mv_bisim x₀
  rw [Ha, Hb, cofix.dest_corec, cofix.dest_corec]
  rw [MvFunctor.map_map, ← append_fun_comp_id]
  refine' liftr_map_last _ _ _ _ _
  intro a; refine' ⟨a, rfl, rfl⟩
#align mvqpf.corec_roll MvQPF.corec_roll
-/

#print MvQPF.Cofix.dest_corec' /-
theorem Cofix.dest_corec' {α : TypeVec n} {β : Type u} (g : β → F (α.append1 (Sum (Cofix F α) β)))
    (x : β) :
    Cofix.dest (Cofix.corec' g x) = appendFun id (Sum.elim id (Cofix.corec' g)) <$$> g x :=
  by
  rw [cofix.corec', cofix.dest_corec]; dsimp
  congr with (i | i) <;> rw [corec_roll] <;> dsimp [cofix.corec']
  · mv_bisim i
    rw [Ha, Hb, cofix.dest_corec]; dsimp [(· ∘ ·)]
    repeat' rw [MvFunctor.map_map, ← append_fun_comp_id]
    apply liftr_map_last'; dsimp [(· ∘ ·), R]; intros; exact ⟨_, rfl, rfl⟩
  · congr with y; erw [append_fun_id_id]; simp [MvFunctor.id_map]
#align mvqpf.cofix.dest_corec' MvQPF.Cofix.dest_corec'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MvQPF.Cofix.dest_corec₁ /-
theorem Cofix.dest_corec₁ {α : TypeVec n} {β : Type u}
    (g : ∀ {X}, (Cofix F α → X) → (β → X) → β → F (α.append1 X)) (x : β)
    (h :
      ∀ (X Y) (f : Cofix F α → X) (f' : β → X) (k : X → Y),
        g (k ∘ f) (k ∘ f') x = (id ::: k) <$$> g f f' x) :
    Cofix.dest (Cofix.corec₁ (@g) x) = g id (Cofix.corec₁ @g) x := by
  rw [cofix.corec₁, cofix.dest_corec', ← h] <;> rfl
#align mvqpf.cofix.dest_corec₁ MvQPF.Cofix.dest_corec₁
-/

#print MvQPF.mvqpfCofix /-
instance mvqpfCofix : MvQPF (Cofix F) where
  p := q.p.mp
  abs α := Quot.mk Mcongr
  repr α := Cofix.repr
  abs_repr α := Cofix.abs_repr
  abs_map α β g x := rfl
#align mvqpf.mvqpf_cofix MvQPF.mvqpfCofix
-/

end MvQPF
