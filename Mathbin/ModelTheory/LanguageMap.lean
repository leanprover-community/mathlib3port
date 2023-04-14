/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn

! This file was ported from Lean 3 source module model_theory.language_map
! leanprover-community/mathlib commit 9a48a083b390d9b84a71efbdc4e8dfa26a687104
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.Basic

/-!
# Language Maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions
* A `first_order.language.Lhom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
* A `first_order.language.Lequiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
* `first_order.language.with_constants` is defined so that if `M` is an `L.Structure` and
  `A : set M`, `L.with_constants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

open Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

#print FirstOrder.Language.LHom /-
/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure LHom where
  onFunction : ∀ ⦃n⦄, L.Functions n → L'.Functions n
  onRelation : ∀ ⦃n⦄, L.Relations n → L'.Relations n
#align first_order.language.Lhom FirstOrder.Language.LHom
-/

-- mathport name: «expr →ᴸ »
infixl:10 " →ᴸ " => LHom

-- \^L
variable {L L'}

namespace Lhom

#print FirstOrder.Language.LHom.mk₂ /-
/-- Defines a map between languages defined with `language.mk₂`. -/
protected def mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (φ₀ : c → L'.Constants)
    (φ₁ : f₁ → L'.Functions 1) (φ₂ : f₂ → L'.Functions 2) (φ₁' : r₁ → L'.Relations 1)
    (φ₂' : r₂ → L'.Relations 2) : Language.mk₂ c f₁ f₂ r₁ r₂ →ᴸ L' :=
  ⟨fun n =>
    Nat.casesOn n φ₀ fun n => Nat.casesOn n φ₁ fun n => Nat.casesOn n φ₂ fun _ => PEmpty.elim,
    fun n =>
    Nat.casesOn n PEmpty.elim fun n =>
      Nat.casesOn n φ₁' fun n => Nat.casesOn n φ₂' fun _ => PEmpty.elim⟩
#align first_order.language.Lhom.mk₂ FirstOrder.Language.LHom.mk₂
-/

variable (ϕ : L →ᴸ L')

#print FirstOrder.Language.LHom.reduct /-
/-- Pulls a structure back along a language map. -/
def reduct (M : Type _) [L'.Structure M] : L.Structure M
    where
  funMap n f xs := funMap (ϕ.onFunction f) xs
  rel_map n r xs := RelMap (ϕ.onRelation r) xs
#align first_order.language.Lhom.reduct FirstOrder.Language.LHom.reduct
-/

#print FirstOrder.Language.LHom.id /-
/-- The identity language homomorphism. -/
@[simps]
protected def id (L : Language) : L →ᴸ L :=
  ⟨fun n => id, fun n => id⟩
#align first_order.language.Lhom.id FirstOrder.Language.LHom.id
-/

instance : Inhabited (L →ᴸ L) :=
  ⟨LHom.id L⟩

#print FirstOrder.Language.LHom.sumInl /-
/-- The inclusion of the left factor into the sum of two languages. -/
@[simps]
protected def sumInl : L →ᴸ L.Sum L' :=
  ⟨fun n => Sum.inl, fun n => Sum.inl⟩
#align first_order.language.Lhom.sum_inl FirstOrder.Language.LHom.sumInl
-/

#print FirstOrder.Language.LHom.sumInr /-
/-- The inclusion of the right factor into the sum of two languages. -/
@[simps]
protected def sumInr : L' →ᴸ L.Sum L' :=
  ⟨fun n => Sum.inr, fun n => Sum.inr⟩
#align first_order.language.Lhom.sum_inr FirstOrder.Language.LHom.sumInr
-/

variable (L L')

#print FirstOrder.Language.LHom.ofIsEmpty /-
/-- The inclusion of an empty language into any other language. -/
@[simps]
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L →ᴸ L' :=
  ⟨fun n => (IsRelational.empty_functions n).elim, fun n => (IsAlgebraic.empty_relations n).elim⟩
#align first_order.language.Lhom.of_is_empty FirstOrder.Language.LHom.ofIsEmpty
-/

variable {L L'} {L'' : Language}

#print FirstOrder.Language.LHom.funext /-
@[ext]
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G :=
  by
  cases' F with Ff Fr
  cases' G with Gf Gr
  simp only [*]
  exact And.intro h_fun h_rel
#align first_order.language.Lhom.funext FirstOrder.Language.LHom.funext
-/

instance [L.IsAlgebraic] [L.IsRelational] : Unique (L →ᴸ L') :=
  ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

#print FirstOrder.Language.LHom.mk₂_funext /-
theorem mk₂_funext {c f₁ f₂ : Type u} {r₁ r₂ : Type v} {F G : Language.mk₂ c f₁ f₂ r₁ r₂ →ᴸ L'}
    (h0 : ∀ c : (Language.mk₂ c f₁ f₂ r₁ r₂).Constants, F.onFunction c = G.onFunction c)
    (h1 : ∀ f : (Language.mk₂ c f₁ f₂ r₁ r₂).Functions 1, F.onFunction f = G.onFunction f)
    (h2 : ∀ f : (Language.mk₂ c f₁ f₂ r₁ r₂).Functions 2, F.onFunction f = G.onFunction f)
    (h1' : ∀ r : (Language.mk₂ c f₁ f₂ r₁ r₂).Relations 1, F.onRelation r = G.onRelation r)
    (h2' : ∀ r : (Language.mk₂ c f₁ f₂ r₁ r₂).Relations 2, F.onRelation r = G.onRelation r) :
    F = G :=
  LHom.funext
    (funext fun n =>
      Nat.casesOn n (funext h0) fun n =>
        Nat.casesOn n (funext h1) fun n =>
          Nat.casesOn n (funext h2) fun n => funext fun f => PEmpty.elim f)
    (funext fun n =>
      Nat.casesOn n (funext fun r => PEmpty.elim r) fun n =>
        Nat.casesOn n (funext h1') fun n =>
          Nat.casesOn n (funext h2') fun n => funext fun r => PEmpty.elim r)
#align first_order.language.Lhom.mk₂_funext FirstOrder.Language.LHom.mk₂_funext
-/

#print FirstOrder.Language.LHom.comp /-
/-- The composition of two language homomorphisms. -/
@[simps]
def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩
#align first_order.language.Lhom.comp FirstOrder.Language.LHom.comp
-/

-- mathport name: Lhom.comp
local infixl:60 " ∘ " => LHom.comp

#print FirstOrder.Language.LHom.id_comp /-
@[simp]
theorem id_comp (F : L →ᴸ L') : LHom.id L' ∘ F = F :=
  by
  cases F
  rfl
#align first_order.language.Lhom.id_comp FirstOrder.Language.LHom.id_comp
-/

#print FirstOrder.Language.LHom.comp_id /-
@[simp]
theorem comp_id (F : L →ᴸ L') : F ∘ LHom.id L = F :=
  by
  cases F
  rfl
#align first_order.language.Lhom.comp_id FirstOrder.Language.LHom.comp_id
-/

/- warning: first_order.language.Lhom.comp_assoc -> FirstOrder.Language.LHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} {L'' : FirstOrder.Language.{u5, u6}} {L3 : FirstOrder.Language.{u7, u8}} (F : FirstOrder.Language.LHom.{u5, u6, u7, u8} L'' L3) (G : FirstOrder.Language.LHom.{u3, u4, u5, u6} L' L'') (H : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L'), Eq.{max (succ u1) (succ u7) (succ u2) (succ u8)} (FirstOrder.Language.LHom.{u1, u2, u7, u8} L L3) (FirstOrder.Language.LHom.comp.{u1, u2, u3, u4, u7, u8} L L' L3 (FirstOrder.Language.LHom.comp.{u3, u4, u5, u6, u7, u8} L' L'' L3 F G) H) (FirstOrder.Language.LHom.comp.{u1, u2, u5, u6, u7, u8} L L'' L3 F (FirstOrder.Language.LHom.comp.{u1, u2, u3, u4, u5, u6} L L' L'' G H))
but is expected to have type
  forall {L : FirstOrder.Language.{u5, u6}} {L' : FirstOrder.Language.{u7, u8}} {L'' : FirstOrder.Language.{u2, u1}} {L3 : FirstOrder.Language.{u4, u3}} (F : FirstOrder.Language.LHom.{u2, u1, u4, u3} L'' L3) (G : FirstOrder.Language.LHom.{u7, u8, u2, u1} L' L'') (H : FirstOrder.Language.LHom.{u5, u6, u7, u8} L L'), Eq.{max (max (max (succ u5) (succ u6)) (succ u3)) (succ u4)} (FirstOrder.Language.LHom.{u5, u6, u4, u3} L L3) (FirstOrder.Language.LHom.comp.{u5, u6, u7, u8, u4, u3} L L' L3 (FirstOrder.Language.LHom.comp.{u7, u8, u2, u1, u4, u3} L' L'' L3 F G) H) (FirstOrder.Language.LHom.comp.{u5, u6, u2, u1, u4, u3} L L'' L3 F (FirstOrder.Language.LHom.comp.{u5, u6, u7, u8, u2, u1} L L' L'' G H))
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.comp_assoc FirstOrder.Language.LHom.comp_assocₓ'. -/
theorem comp_assoc {L3 : Language} (F : L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') :
    F ∘ G ∘ H = F ∘ (G ∘ H) :=
  rfl
#align first_order.language.Lhom.comp_assoc FirstOrder.Language.LHom.comp_assoc

section SumElim

variable (ψ : L'' →ᴸ L')

#print FirstOrder.Language.LHom.sumElim /-
/-- A language map defined on two factors of a sum. -/
@[simps]
protected def sumElim : L.Sum L'' →ᴸ L'
    where
  onFunction n := Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation n := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f
#align first_order.language.Lhom.sum_elim FirstOrder.Language.LHom.sumElim
-/

/- warning: first_order.language.Lhom.sum_elim_comp_inl -> FirstOrder.Language.LHom.sumElim_comp_inl is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (ϕ : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L') {L'' : FirstOrder.Language.{u5, u6}} (ψ : FirstOrder.Language.LHom.{u5, u6, u3, u4} L'' L'), Eq.{max (succ u1) (succ u3) (succ u2) (succ u4)} (FirstOrder.Language.LHom.{u1, u2, u3, u4} L L') (FirstOrder.Language.LHom.comp.{u1, u2, max u1 u5, max u2 u6, u3, u4} L (FirstOrder.Language.sum.{u1, u2, u5, u6} L L'') L' (FirstOrder.Language.LHom.sumElim.{u1, u2, u3, u4, u5, u6} L L' ϕ L'' ψ) (FirstOrder.Language.LHom.sumInl.{u1, u2, u5, u6} L L'')) ϕ
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u5, u6}} (ϕ : FirstOrder.Language.LHom.{u3, u4, u5, u6} L L') {L'' : FirstOrder.Language.{u2, u1}} (ψ : FirstOrder.Language.LHom.{u2, u1, u5, u6} L'' L'), Eq.{max (max (max (succ u3) (succ u5)) (succ u4)) (succ u6)} (FirstOrder.Language.LHom.{u3, u4, u5, u6} L L') (FirstOrder.Language.LHom.comp.{u3, u4, max u3 u2, max u4 u1, u5, u6} L (FirstOrder.Language.sum.{u3, u4, u2, u1} L L'') L' (FirstOrder.Language.LHom.sumElim.{u3, u4, u5, u6, u2, u1} L L' ϕ L'' ψ) (FirstOrder.Language.LHom.sumInl.{u3, u4, u2, u1} L L'')) ϕ
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.sum_elim_comp_inl FirstOrder.Language.LHom.sumElim_comp_inlₓ'. -/
theorem sumElim_comp_inl (ψ : L'' →ᴸ L') : ϕ.sum_elim ψ ∘ LHom.sumInl = ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
#align first_order.language.Lhom.sum_elim_comp_inl FirstOrder.Language.LHom.sumElim_comp_inl

/- warning: first_order.language.Lhom.sum_elim_comp_inr -> FirstOrder.Language.LHom.sumElim_comp_inr is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (ϕ : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L') {L'' : FirstOrder.Language.{u5, u6}} (ψ : FirstOrder.Language.LHom.{u5, u6, u3, u4} L'' L'), Eq.{max (succ u5) (succ u3) (succ u6) (succ u4)} (FirstOrder.Language.LHom.{u5, u6, u3, u4} L'' L') (FirstOrder.Language.LHom.comp.{u5, u6, max u1 u5, max u2 u6, u3, u4} L'' (FirstOrder.Language.sum.{u1, u2, u5, u6} L L'') L' (FirstOrder.Language.LHom.sumElim.{u1, u2, u3, u4, u5, u6} L L' ϕ L'' ψ) (FirstOrder.Language.LHom.sumInr.{u1, u2, u5, u6} L L'')) ψ
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u5, u6}} (ϕ : FirstOrder.Language.LHom.{u3, u4, u5, u6} L L') {L'' : FirstOrder.Language.{u2, u1}} (ψ : FirstOrder.Language.LHom.{u2, u1, u5, u6} L'' L'), Eq.{max (max (max (succ u5) (succ u6)) (succ u1)) (succ u2)} (FirstOrder.Language.LHom.{u2, u1, u5, u6} L'' L') (FirstOrder.Language.LHom.comp.{u2, u1, max u3 u2, max u4 u1, u5, u6} L'' (FirstOrder.Language.sum.{u3, u4, u2, u1} L L'') L' (FirstOrder.Language.LHom.sumElim.{u3, u4, u5, u6, u2, u1} L L' ϕ L'' ψ) (FirstOrder.Language.LHom.sumInr.{u3, u4, u2, u1} L L'')) ψ
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.sum_elim_comp_inr FirstOrder.Language.LHom.sumElim_comp_inrₓ'. -/
theorem sumElim_comp_inr (ψ : L'' →ᴸ L') : ϕ.sum_elim ψ ∘ LHom.sumInr = ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
#align first_order.language.Lhom.sum_elim_comp_inr FirstOrder.Language.LHom.sumElim_comp_inr

#print FirstOrder.Language.LHom.sumElim_inl_inr /-
theorem sumElim_inl_inr : LHom.sumInl.sum_elim LHom.sumInr = LHom.id (L.Sum L') :=
  LHom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)
#align first_order.language.Lhom.sum_elim_inl_inr FirstOrder.Language.LHom.sumElim_inl_inr
-/

/- warning: first_order.language.Lhom.comp_sum_elim -> FirstOrder.Language.LHom.comp_sumElim is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (ϕ : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L') {L'' : FirstOrder.Language.{u5, u6}} (ψ : FirstOrder.Language.LHom.{u5, u6, u3, u4} L'' L') {L3 : FirstOrder.Language.{u7, u8}} (θ : FirstOrder.Language.LHom.{u3, u4, u7, u8} L' L3), Eq.{max (succ (max u1 u5)) (succ u7) (succ (max u2 u6)) (succ u8)} (FirstOrder.Language.LHom.{max u1 u5, max u2 u6, u7, u8} (FirstOrder.Language.sum.{u1, u2, u5, u6} L L'') L3) (FirstOrder.Language.LHom.comp.{max u1 u5, max u2 u6, u3, u4, u7, u8} (FirstOrder.Language.sum.{u1, u2, u5, u6} L L'') L' L3 θ (FirstOrder.Language.LHom.sumElim.{u1, u2, u3, u4, u5, u6} L L' ϕ L'' ψ)) (FirstOrder.Language.LHom.sumElim.{u1, u2, u7, u8, u5, u6} L L3 (FirstOrder.Language.LHom.comp.{u1, u2, u3, u4, u7, u8} L L' L3 θ ϕ) L'' (FirstOrder.Language.LHom.comp.{u5, u6, u3, u4, u7, u8} L'' L' L3 θ ψ))
but is expected to have type
  forall {L : FirstOrder.Language.{u5, u6}} {L' : FirstOrder.Language.{u7, u8}} (ϕ : FirstOrder.Language.LHom.{u5, u6, u7, u8} L L') {L'' : FirstOrder.Language.{u1, u2}} (ψ : FirstOrder.Language.LHom.{u1, u2, u7, u8} L'' L') {L3 : FirstOrder.Language.{u4, u3}} (θ : FirstOrder.Language.LHom.{u7, u8, u4, u3} L' L3), Eq.{max (max (max (max (max (succ u5) (succ u6)) (succ u2)) (succ u1)) (succ u3)) (succ u4)} (FirstOrder.Language.LHom.{max u5 u1, max u6 u2, u4, u3} (FirstOrder.Language.sum.{u5, u6, u1, u2} L L'') L3) (FirstOrder.Language.LHom.comp.{max u5 u1, max u6 u2, u7, u8, u4, u3} (FirstOrder.Language.sum.{u5, u6, u1, u2} L L'') L' L3 θ (FirstOrder.Language.LHom.sumElim.{u5, u6, u7, u8, u1, u2} L L' ϕ L'' ψ)) (FirstOrder.Language.LHom.sumElim.{u5, u6, u4, u3, u1, u2} L L3 (FirstOrder.Language.LHom.comp.{u5, u6, u7, u8, u4, u3} L L' L3 θ ϕ) L'' (FirstOrder.Language.LHom.comp.{u1, u2, u7, u8, u4, u3} L'' L' L3 θ ψ))
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.comp_sum_elim FirstOrder.Language.LHom.comp_sumElimₓ'. -/
theorem comp_sumElim {L3 : Language} (θ : L' →ᴸ L3) : θ ∘ ϕ.sum_elim ψ = (θ ∘ ϕ).sum_elim (θ ∘ ψ) :=
  LHom.funext (funext fun n => Sum.comp_elim _ _ _) (funext fun n => Sum.comp_elim _ _ _)
#align first_order.language.Lhom.comp_sum_elim FirstOrder.Language.LHom.comp_sumElim

end SumElim

section SumMap

variable {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂)

#print FirstOrder.Language.LHom.sumMap /-
/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
def sumMap : L.Sum L₁ →ᴸ L'.Sum L₂
    where
  onFunction n := Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation n := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f
#align first_order.language.Lhom.sum_map FirstOrder.Language.LHom.sumMap
-/

/- warning: first_order.language.Lhom.sum_map_comp_inl -> FirstOrder.Language.LHom.sumMap_comp_inl is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (ϕ : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L') {L₁ : FirstOrder.Language.{u5, u6}} {L₂ : FirstOrder.Language.{u7, u8}} (ψ : FirstOrder.Language.LHom.{u5, u6, u7, u8} L₁ L₂), Eq.{max (succ u1) (succ (max u3 u7)) (succ u2) (succ (max u4 u8))} (FirstOrder.Language.LHom.{u1, u2, max u3 u7, max u4 u8} L (FirstOrder.Language.sum.{u3, u4, u7, u8} L' L₂)) (FirstOrder.Language.LHom.comp.{u1, u2, max u1 u5, max u2 u6, max u3 u7, max u4 u8} L (FirstOrder.Language.sum.{u1, u2, u5, u6} L L₁) (FirstOrder.Language.sum.{u3, u4, u7, u8} L' L₂) (FirstOrder.Language.LHom.sumMap.{u1, u2, u3, u4, u5, u6, u7, u8} L L' ϕ L₁ L₂ ψ) (FirstOrder.Language.LHom.sumInl.{u1, u2, u5, u6} L L₁)) (FirstOrder.Language.LHom.comp.{u1, u2, u3, u4, max u3 u7, max u4 u8} L L' (FirstOrder.Language.sum.{u3, u4, u7, u8} L' L₂) (FirstOrder.Language.LHom.sumInl.{u3, u4, u7, u8} L' L₂) ϕ)
but is expected to have type
  forall {L : FirstOrder.Language.{u5, u6}} {L' : FirstOrder.Language.{u7, u8}} (ϕ : FirstOrder.Language.LHom.{u5, u6, u7, u8} L L') {L₁ : FirstOrder.Language.{u2, u1}} {L₂ : FirstOrder.Language.{u3, u4}} (ψ : FirstOrder.Language.LHom.{u2, u1, u3, u4} L₁ L₂), Eq.{max (max (max (max (max (succ u5) (succ u7)) (succ u6)) (succ u8)) (succ u4)) (succ u3)} (FirstOrder.Language.LHom.{u5, u6, max u7 u3, max u8 u4} L (FirstOrder.Language.sum.{u7, u8, u3, u4} L' L₂)) (FirstOrder.Language.LHom.comp.{u5, u6, max u5 u2, max u6 u1, max u7 u3, max u8 u4} L (FirstOrder.Language.sum.{u5, u6, u2, u1} L L₁) (FirstOrder.Language.sum.{u7, u8, u3, u4} L' L₂) (FirstOrder.Language.LHom.sumMap.{u5, u6, u7, u8, u2, u1, u3, u4} L L' ϕ L₁ L₂ ψ) (FirstOrder.Language.LHom.sumInl.{u5, u6, u2, u1} L L₁)) (FirstOrder.Language.LHom.comp.{u5, u6, u7, u8, max u3 u7, max u4 u8} L L' (FirstOrder.Language.sum.{u7, u8, u3, u4} L' L₂) (FirstOrder.Language.LHom.sumInl.{u7, u8, u3, u4} L' L₂) ϕ)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.sum_map_comp_inl FirstOrder.Language.LHom.sumMap_comp_inlₓ'. -/
@[simp]
theorem sumMap_comp_inl : ϕ.sum_map ψ ∘ LHom.sumInl = LHom.sumInl ∘ ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
#align first_order.language.Lhom.sum_map_comp_inl FirstOrder.Language.LHom.sumMap_comp_inl

/- warning: first_order.language.Lhom.sum_map_comp_inr -> FirstOrder.Language.LHom.sumMap_comp_inr is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (ϕ : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L') {L₁ : FirstOrder.Language.{u5, u6}} {L₂ : FirstOrder.Language.{u7, u8}} (ψ : FirstOrder.Language.LHom.{u5, u6, u7, u8} L₁ L₂), Eq.{max (succ u5) (succ (max u3 u7)) (succ u6) (succ (max u4 u8))} (FirstOrder.Language.LHom.{u5, u6, max u3 u7, max u4 u8} L₁ (FirstOrder.Language.sum.{u3, u4, u7, u8} L' L₂)) (FirstOrder.Language.LHom.comp.{u5, u6, max u1 u5, max u2 u6, max u3 u7, max u4 u8} L₁ (FirstOrder.Language.sum.{u1, u2, u5, u6} L L₁) (FirstOrder.Language.sum.{u3, u4, u7, u8} L' L₂) (FirstOrder.Language.LHom.sumMap.{u1, u2, u3, u4, u5, u6, u7, u8} L L' ϕ L₁ L₂ ψ) (FirstOrder.Language.LHom.sumInr.{u1, u2, u5, u6} L L₁)) (FirstOrder.Language.LHom.comp.{u5, u6, u7, u8, max u3 u7, max u4 u8} L₁ L₂ (FirstOrder.Language.sum.{u3, u4, u7, u8} L' L₂) (FirstOrder.Language.LHom.sumInr.{u3, u4, u7, u8} L' L₂) ψ)
but is expected to have type
  forall {L : FirstOrder.Language.{u5, u6}} {L' : FirstOrder.Language.{u7, u8}} (ϕ : FirstOrder.Language.LHom.{u5, u6, u7, u8} L L') {L₁ : FirstOrder.Language.{u3, u4}} {L₂ : FirstOrder.Language.{u1, u2}} (ψ : FirstOrder.Language.LHom.{u3, u4, u1, u2} L₁ L₂), Eq.{max (max (max (max (max (succ u7) (succ u8)) (succ u4)) (succ u3)) (succ u2)) (succ u1)} (FirstOrder.Language.LHom.{u3, u4, max u7 u1, max u8 u2} L₁ (FirstOrder.Language.sum.{u7, u8, u1, u2} L' L₂)) (FirstOrder.Language.LHom.comp.{u3, u4, max u5 u3, max u6 u4, max u7 u1, max u8 u2} L₁ (FirstOrder.Language.sum.{u5, u6, u3, u4} L L₁) (FirstOrder.Language.sum.{u7, u8, u1, u2} L' L₂) (FirstOrder.Language.LHom.sumMap.{u5, u6, u7, u8, u3, u4, u1, u2} L L' ϕ L₁ L₂ ψ) (FirstOrder.Language.LHom.sumInr.{u5, u6, u3, u4} L L₁)) (FirstOrder.Language.LHom.comp.{u3, u4, u1, u2, max u1 u7, max u2 u8} L₁ L₂ (FirstOrder.Language.sum.{u7, u8, u1, u2} L' L₂) (FirstOrder.Language.LHom.sumInr.{u7, u8, u1, u2} L' L₂) ψ)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.sum_map_comp_inr FirstOrder.Language.LHom.sumMap_comp_inrₓ'. -/
@[simp]
theorem sumMap_comp_inr : ϕ.sum_map ψ ∘ LHom.sumInr = LHom.sumInr ∘ ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
#align first_order.language.Lhom.sum_map_comp_inr FirstOrder.Language.LHom.sumMap_comp_inr

end SumMap

#print FirstOrder.Language.LHom.Injective /-
/-- A language homomorphism is injective when all the maps between symbol types are. -/
protected structure Injective : Prop where
  onFunction {n} : Function.Injective fun f : L.Functions n => onFunction ϕ f
  onRelation {n} : Function.Injective fun R : L.Relations n => onRelation ϕ R
#align first_order.language.Lhom.injective FirstOrder.Language.LHom.Injective
-/

#print FirstOrder.Language.LHom.defaultExpansion /-
/-- Pulls a `L`-structure along a language map `ϕ : L →ᴸ L'`, and then expands it
  to an `L'`-structure arbitrarily. -/
noncomputable def defaultExpansion (ϕ : L →ᴸ L')
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => onFunction ϕ f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => onRelation ϕ r)]
    (M : Type _) [Inhabited M] [L.Structure M] : L'.Structure M
    where
  funMap n f xs :=
    if h' : f ∈ Set.range fun f : L.Functions n => onFunction ϕ f then funMap h'.some xs
    else default
  rel_map n r xs :=
    if h' : r ∈ Set.range fun r : L.Relations n => onRelation ϕ r then RelMap h'.some xs
    else default
#align first_order.language.Lhom.default_expansion FirstOrder.Language.LHom.defaultExpansion
-/

#print FirstOrder.Language.LHom.IsExpansionOn /-
/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
class IsExpansionOn (M : Type _) [L.Structure M] [L'.Structure M] : Prop where
  map_onFunction : ∀ {n} (f : L.Functions n) (x : Fin n → M), funMap (ϕ.onFunction f) x = funMap f x
  map_onRelation : ∀ {n} (R : L.Relations n) (x : Fin n → M), RelMap (ϕ.onRelation R) x = RelMap R x
#align first_order.language.Lhom.is_expansion_on FirstOrder.Language.LHom.IsExpansionOn
-/

/- warning: first_order.language.Lhom.map_on_function -> FirstOrder.Language.LHom.map_onFunction is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (ϕ : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L') {M : Type.{u5}} [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u5} L M] [_inst_3 : FirstOrder.Language.Structure.{u3, u4, u5} L' M] [_inst_4 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u3, u4, u5} L L' ϕ M _inst_2 _inst_3] {n : Nat} (f : FirstOrder.Language.Functions.{u1, u2} L n) (x : (Fin n) -> M), Eq.{succ u5} M (FirstOrder.Language.Structure.funMap.{u3, u4, u5} L' M _inst_3 n (FirstOrder.Language.LHom.onFunction.{u1, u2, u3, u4} L L' ϕ n f) x) (FirstOrder.Language.Structure.funMap.{u1, u2, u5} L M _inst_2 n f x)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {L' : FirstOrder.Language.{u4, u5}} (ϕ : FirstOrder.Language.LHom.{u2, u3, u4, u5} L L') {M : Type.{u1}} [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L M] [_inst_3 : FirstOrder.Language.Structure.{u4, u5, u1} L' M] [_inst_4 : FirstOrder.Language.LHom.IsExpansionOn.{u2, u3, u4, u5, u1} L L' ϕ M _inst_2 _inst_3] {n : Nat} (f : FirstOrder.Language.Functions.{u2, u3} L n) (x : (Fin n) -> M), Eq.{succ u1} M (FirstOrder.Language.Structure.funMap.{u4, u5, u1} L' M _inst_3 n (FirstOrder.Language.LHom.onFunction.{u2, u3, u4, u5} L L' ϕ n f) x) (FirstOrder.Language.Structure.funMap.{u2, u3, u1} L M _inst_2 n f x)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.map_on_function FirstOrder.Language.LHom.map_onFunctionₓ'. -/
@[simp]
theorem map_onFunction {M : Type _} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (f : L.Functions n) (x : Fin n → M) : funMap (ϕ.onFunction f) x = funMap f x :=
  IsExpansionOn.map_onFunction f x
#align first_order.language.Lhom.map_on_function FirstOrder.Language.LHom.map_onFunction

/- warning: first_order.language.Lhom.map_on_relation -> FirstOrder.Language.LHom.map_onRelation is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (ϕ : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L') {M : Type.{u5}} [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u5} L M] [_inst_3 : FirstOrder.Language.Structure.{u3, u4, u5} L' M] [_inst_4 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u3, u4, u5} L L' ϕ M _inst_2 _inst_3] {n : Nat} (R : FirstOrder.Language.Relations.{u1, u2} L n) (x : (Fin n) -> M), Eq.{1} Prop (FirstOrder.Language.Structure.RelMap.{u3, u4, u5} L' M _inst_3 n (FirstOrder.Language.LHom.onRelation.{u1, u2, u3, u4} L L' ϕ n R) x) (FirstOrder.Language.Structure.RelMap.{u1, u2, u5} L M _inst_2 n R x)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {L' : FirstOrder.Language.{u4, u5}} (ϕ : FirstOrder.Language.LHom.{u2, u3, u4, u5} L L') {M : Type.{u1}} [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L M] [_inst_3 : FirstOrder.Language.Structure.{u4, u5, u1} L' M] [_inst_4 : FirstOrder.Language.LHom.IsExpansionOn.{u2, u3, u4, u5, u1} L L' ϕ M _inst_2 _inst_3] {n : Nat} (R : FirstOrder.Language.Relations.{u2, u3} L n) (x : (Fin n) -> M), Eq.{1} Prop (FirstOrder.Language.Structure.rel_map.{u4, u5, u1} L' M _inst_3 n (FirstOrder.Language.LHom.onRelation.{u2, u3, u4, u5} L L' ϕ n R) x) (FirstOrder.Language.Structure.rel_map.{u2, u3, u1} L M _inst_2 n R x)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.map_on_relation FirstOrder.Language.LHom.map_onRelationₓ'. -/
@[simp]
theorem map_onRelation {M : Type _} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (R : L.Relations n) (x : Fin n → M) : RelMap (ϕ.onRelation R) x = RelMap R x :=
  IsExpansionOn.map_onRelation R x
#align first_order.language.Lhom.map_on_relation FirstOrder.Language.LHom.map_onRelation

#print FirstOrder.Language.LHom.id_isExpansionOn /-
instance id_isExpansionOn (M : Type _) [L.Structure M] : IsExpansionOn (LHom.id L) M :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
#align first_order.language.Lhom.id_is_expansion_on FirstOrder.Language.LHom.id_isExpansionOn
-/

#print FirstOrder.Language.LHom.ofIsEmpty_isExpansionOn /-
instance ofIsEmpty_isExpansionOn (M : Type _) [L.Structure M] [L'.Structure M] [L.IsAlgebraic]
    [L.IsRelational] : IsExpansionOn (LHom.ofIsEmpty L L') M :=
  ⟨fun n => (IsRelational.empty_functions n).elim, fun n => (IsAlgebraic.empty_relations n).elim⟩
#align first_order.language.Lhom.of_is_empty_is_expansion_on FirstOrder.Language.LHom.ofIsEmpty_isExpansionOn
-/

#print FirstOrder.Language.LHom.sumElim_isExpansionOn /-
instance sumElim_isExpansionOn {L'' : Language} (ψ : L'' →ᴸ L') (M : Type _) [L.Structure M]
    [L'.Structure M] [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sum_elim ψ).IsExpansionOn M :=
  ⟨fun _ f _ => Sum.casesOn f (by simp) (by simp), fun _ R _ => Sum.casesOn R (by simp) (by simp)⟩
#align first_order.language.Lhom.sum_elim_is_expansion_on FirstOrder.Language.LHom.sumElim_isExpansionOn
-/

#print FirstOrder.Language.LHom.sumMap_isExpansionOn /-
instance sumMap_isExpansionOn {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂) (M : Type _) [L.Structure M]
    [L'.Structure M] [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sum_map ψ).IsExpansionOn M :=
  ⟨fun _ f _ => Sum.casesOn f (by simp) (by simp), fun _ R _ => Sum.casesOn R (by simp) (by simp)⟩
#align first_order.language.Lhom.sum_map_is_expansion_on FirstOrder.Language.LHom.sumMap_isExpansionOn
-/

#print FirstOrder.Language.LHom.sumInl_isExpansionOn /-
instance sumInl_isExpansionOn (M : Type _) [L.Structure M] [L'.Structure M] :
    (LHom.sumInl : L →ᴸ L.Sum L').IsExpansionOn M :=
  ⟨fun _ f _ => rfl, fun _ R _ => rfl⟩
#align first_order.language.Lhom.sum_inl_is_expansion_on FirstOrder.Language.LHom.sumInl_isExpansionOn
-/

#print FirstOrder.Language.LHom.sumInr_isExpansionOn /-
instance sumInr_isExpansionOn (M : Type _) [L.Structure M] [L'.Structure M] :
    (LHom.sumInr : L' →ᴸ L.Sum L').IsExpansionOn M :=
  ⟨fun _ f _ => rfl, fun _ R _ => rfl⟩
#align first_order.language.Lhom.sum_inr_is_expansion_on FirstOrder.Language.LHom.sumInr_isExpansionOn
-/

#print FirstOrder.Language.LHom.funMap_sumInl /-
@[simp]
theorem funMap_sumInl [(L.Sum L').Structure M] [(LHom.sumInl : L →ᴸ L.Sum L').IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L.Sum L') M _ n (Sum.inl f) x = funMap f x :=
  (LHom.sumInl : L →ᴸ L.Sum L').map_onFunction f x
#align first_order.language.Lhom.fun_map_sum_inl FirstOrder.Language.LHom.funMap_sumInl
-/

#print FirstOrder.Language.LHom.funMap_sumInr /-
@[simp]
theorem funMap_sumInr [(L'.Sum L).Structure M] [(LHom.sumInr : L →ᴸ L'.Sum L).IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L'.Sum L) M _ n (Sum.inr f) x = funMap f x :=
  (LHom.sumInr : L →ᴸ L'.Sum L).map_onFunction f x
#align first_order.language.Lhom.fun_map_sum_inr FirstOrder.Language.LHom.funMap_sumInr
-/

#print FirstOrder.Language.LHom.sumInl_injective /-
theorem sumInl_injective : (LHom.sumInl : L →ᴸ L.Sum L').Injective :=
  ⟨fun n => Sum.inl_injective, fun n => Sum.inl_injective⟩
#align first_order.language.Lhom.sum_inl_injective FirstOrder.Language.LHom.sumInl_injective
-/

#print FirstOrder.Language.LHom.sumInr_injective /-
theorem sumInr_injective : (LHom.sumInr : L' →ᴸ L.Sum L').Injective :=
  ⟨fun n => Sum.inr_injective, fun n => Sum.inr_injective⟩
#align first_order.language.Lhom.sum_inr_injective FirstOrder.Language.LHom.sumInr_injective
-/

#print FirstOrder.Language.LHom.isExpansionOn_reduct /-
instance (priority := 100) isExpansionOn_reduct (ϕ : L →ᴸ L') (M : Type _) [L'.Structure M] :
    @IsExpansionOn L L' ϕ M (ϕ.reduct M) _ :=
  letI := ϕ.reduct M
  ⟨fun _ f _ => rfl, fun _ R _ => rfl⟩
#align first_order.language.Lhom.is_expansion_on_reduct FirstOrder.Language.LHom.isExpansionOn_reduct
-/

/- warning: first_order.language.Lhom.injective.is_expansion_on_default -> FirstOrder.Language.LHom.Injective.isExpansionOn_default is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} {ϕ : FirstOrder.Language.LHom.{u1, u2, u3, u4} L L'} [_inst_2 : forall (n : Nat) (f : FirstOrder.Language.Functions.{u3, u4} L' n), Decidable (Membership.Mem.{u3, u3} (FirstOrder.Language.Functions.{u3, u4} L' n) (Set.{u3} (FirstOrder.Language.Functions.{u3, u4} L' n)) (Set.hasMem.{u3} (FirstOrder.Language.Functions.{u3, u4} L' n)) f (Set.range.{u3, succ u1} (FirstOrder.Language.Functions.{u3, u4} L' n) (FirstOrder.Language.Functions.{u1, u2} L n) (fun (f : FirstOrder.Language.Functions.{u1, u2} L n) => FirstOrder.Language.LHom.onFunction.{u1, u2, u3, u4} L L' ϕ n f)))] [_inst_3 : forall (n : Nat) (r : FirstOrder.Language.Relations.{u3, u4} L' n), Decidable (Membership.Mem.{u4, u4} (FirstOrder.Language.Relations.{u3, u4} L' n) (Set.{u4} (FirstOrder.Language.Relations.{u3, u4} L' n)) (Set.hasMem.{u4} (FirstOrder.Language.Relations.{u3, u4} L' n)) r (Set.range.{u4, succ u2} (FirstOrder.Language.Relations.{u3, u4} L' n) (FirstOrder.Language.Relations.{u1, u2} L n) (fun (r : FirstOrder.Language.Relations.{u1, u2} L n) => FirstOrder.Language.LHom.onRelation.{u1, u2, u3, u4} L L' ϕ n r)))], (FirstOrder.Language.LHom.Injective.{u1, u2, u3, u4} L L' ϕ) -> (forall (M : Type.{u5}) [_inst_4 : Inhabited.{succ u5} M] [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u5} L M], FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u3, u4, u5} L L' ϕ M _inst_5 (FirstOrder.Language.LHom.defaultExpansion.{u1, u2, u3, u4, u5} L L' ϕ (fun (n : Nat) (f : FirstOrder.Language.Functions.{u3, u4} L' n) => _inst_2 n f) (fun (n : Nat) (r : FirstOrder.Language.Relations.{u3, u4} L' n) => _inst_3 n r) M _inst_4 _inst_5))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {L' : FirstOrder.Language.{u4, u5}} {ϕ : FirstOrder.Language.LHom.{u2, u3, u4, u5} L L'} [_inst_2 : forall (n : Nat) (f : FirstOrder.Language.Functions.{u4, u5} L' n), Decidable (Membership.mem.{u4, u4} (FirstOrder.Language.Functions.{u4, u5} L' n) (Set.{u4} (FirstOrder.Language.Functions.{u4, u5} L' n)) (Set.instMembershipSet.{u4} (FirstOrder.Language.Functions.{u4, u5} L' n)) f (Set.range.{u4, succ u2} (FirstOrder.Language.Functions.{u4, u5} L' n) (FirstOrder.Language.Functions.{u2, u3} L n) (fun (f : FirstOrder.Language.Functions.{u2, u3} L n) => FirstOrder.Language.LHom.onFunction.{u2, u3, u4, u5} L L' ϕ n f)))] [_inst_3 : forall (n : Nat) (r : FirstOrder.Language.Relations.{u4, u5} L' n), Decidable (Membership.mem.{u5, u5} (FirstOrder.Language.Relations.{u4, u5} L' n) (Set.{u5} (FirstOrder.Language.Relations.{u4, u5} L' n)) (Set.instMembershipSet.{u5} (FirstOrder.Language.Relations.{u4, u5} L' n)) r (Set.range.{u5, succ u3} (FirstOrder.Language.Relations.{u4, u5} L' n) (FirstOrder.Language.Relations.{u2, u3} L n) (fun (r : FirstOrder.Language.Relations.{u2, u3} L n) => FirstOrder.Language.LHom.onRelation.{u2, u3, u4, u5} L L' ϕ n r)))], (FirstOrder.Language.LHom.Injective.{u2, u3, u4, u5} L L' ϕ) -> (forall (M : Type.{u1}) [_inst_4 : Inhabited.{succ u1} M] [_inst_5 : FirstOrder.Language.Structure.{u2, u3, u1} L M], FirstOrder.Language.LHom.IsExpansionOn.{u2, u3, u4, u5, u1} L L' ϕ M _inst_5 (FirstOrder.Language.LHom.defaultExpansion.{u2, u3, u4, u5, u1} L L' ϕ (fun (n : Nat) (f : FirstOrder.Language.Functions.{u4, u5} L' n) => _inst_2 n f) (fun (n : Nat) (r : FirstOrder.Language.Relations.{u4, u5} L' n) => _inst_3 n r) M _inst_4 _inst_5))
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.injective.is_expansion_on_default FirstOrder.Language.LHom.Injective.isExpansionOn_defaultₓ'. -/
theorem Injective.isExpansionOn_default {ϕ : L →ᴸ L'}
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => onFunction ϕ f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => onRelation ϕ r)]
    (h : ϕ.Injective) (M : Type _) [Inhabited M] [L.Structure M] :
    @IsExpansionOn L L' ϕ M _ (ϕ.defaultExpansion M) :=
  by
  letI := ϕ.default_expansion M
  refine' ⟨fun n f xs => _, fun n r xs => _⟩
  · have hf : ϕ.on_function f ∈ Set.range fun f : L.functions n => ϕ.on_function f := ⟨f, rfl⟩
    refine' (dif_pos hf).trans _
    rw [h.on_function hf.some_spec]
  · have hr : ϕ.on_relation r ∈ Set.range fun r : L.relations n => ϕ.on_relation r := ⟨r, rfl⟩
    refine' (dif_pos hr).trans _
    rw [h.on_relation hr.some_spec]
#align first_order.language.Lhom.injective.is_expansion_on_default FirstOrder.Language.LHom.Injective.isExpansionOn_default

end Lhom

/-- A language equivalence maps the symbols of one language to symbols of another bijectively. -/
structure Lequiv (L L' : Language) where
  toLhom : L →ᴸ L'
  invLhom : L' →ᴸ L
  left_inv : inv_Lhom.comp to_Lhom = LHom.id L
  right_inv : to_Lhom.comp inv_Lhom = LHom.id L'
#align first_order.language.Lequiv FirstOrder.Language.Lequiv

-- mathport name: «expr ≃ᴸ »
infixl:10 " ≃ᴸ " => Lequiv

-- \^L
namespace Lequiv

variable (L)

/-- The identity equivalence from a first-order language to itself. -/
@[simps]
protected def refl : L ≃ᴸ L :=
  ⟨LHom.id L, LHom.id L, LHom.id_comp _, LHom.id_comp _⟩
#align first_order.language.Lequiv.refl FirstOrder.Language.Lequiv.refl

variable {L}

instance : Inhabited (L ≃ᴸ L) :=
  ⟨Lequiv.refl L⟩

variable {L'' : Language} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps]
protected def symm : L' ≃ᴸ L :=
  ⟨e.invLhom, e.toLhom, e.right_inv, e.left_inv⟩
#align first_order.language.Lequiv.symm FirstOrder.Language.Lequiv.symm

/-- The composition of equivalences of first-order languages. -/
@[simps, trans]
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLhom.comp e.toLhom, e.invLhom.comp e'.invLhom, by
    rw [Lhom.comp_assoc, ← Lhom.comp_assoc e'.inv_Lhom, e'.left_inv, Lhom.id_comp, e.left_inv], by
    rw [Lhom.comp_assoc, ← Lhom.comp_assoc e.to_Lhom, e.right_inv, Lhom.id_comp, e'.right_inv]⟩
#align first_order.language.Lequiv.trans FirstOrder.Language.Lequiv.trans

end Lequiv

section ConstantsOn

variable (α : Type u')

#print FirstOrder.Language.constantsOn /-
/-- A language with constants indexed by a type. -/
@[simp]
def constantsOn : Language.{u', 0} :=
  Language.mk₂ α PEmpty PEmpty PEmpty PEmpty
#align first_order.language.constants_on FirstOrder.Language.constantsOn
-/

variable {α}

#print FirstOrder.Language.constantsOn_constants /-
theorem constantsOn_constants : (constantsOn α).Constants = α :=
  rfl
#align first_order.language.constants_on_constants FirstOrder.Language.constantsOn_constants
-/

#print FirstOrder.Language.isAlgebraic_constantsOn /-
instance isAlgebraic_constantsOn : IsAlgebraic (constantsOn α) :=
  Language.isAlgebraic_mk₂
#align first_order.language.is_algebraic_constants_on FirstOrder.Language.isAlgebraic_constantsOn
-/

#print FirstOrder.Language.isRelational_constantsOn /-
instance isRelational_constantsOn [ie : IsEmpty α] : IsRelational (constantsOn α) :=
  Language.isRelational_mk₂
#align first_order.language.is_relational_constants_on FirstOrder.Language.isRelational_constantsOn
-/

#print FirstOrder.Language.isEmpty_functions_constantsOn_succ /-
instance isEmpty_functions_constantsOn_succ {n : ℕ} : IsEmpty ((constantsOn α).Functions (n + 1)) :=
  Nat.casesOn n PEmpty.isEmpty fun n => Nat.casesOn n PEmpty.isEmpty fun _ => PEmpty.isEmpty
#align first_order.language.is_empty_functions_constants_on_succ FirstOrder.Language.isEmpty_functions_constantsOn_succ
-/

#print FirstOrder.Language.card_constantsOn /-
theorem card_constantsOn : (constantsOn α).card = (#α) := by simp
#align first_order.language.card_constants_on FirstOrder.Language.card_constantsOn
-/

#print FirstOrder.Language.constantsOn.structure /-
/-- Gives a `constants_on α` structure to a type by assigning each constant a value. -/
def constantsOn.structure (f : α → M) : (constantsOn α).Structure M :=
  Structure.mk₂ f PEmpty.elim PEmpty.elim PEmpty.elim PEmpty.elim
#align first_order.language.constants_on.Structure FirstOrder.Language.constantsOn.structure
-/

variable {β : Type v'}

#print FirstOrder.Language.LHom.constantsOnMap /-
/-- A map between index types induces a map between constant languages. -/
def LHom.constantsOnMap (f : α → β) : constantsOn α →ᴸ constantsOn β :=
  LHom.mk₂ f PEmpty.elim PEmpty.elim PEmpty.elim PEmpty.elim
#align first_order.language.Lhom.constants_on_map FirstOrder.Language.LHom.constantsOnMap
-/

#print FirstOrder.Language.constantsOnMap_isExpansionOn /-
theorem constantsOnMap_isExpansionOn {f : α → β} {fα : α → M} {fβ : β → M} (h : fβ ∘ f = fα) :
    @LHom.IsExpansionOn _ _ (LHom.constantsOnMap f) M (constantsOn.structure fα)
      (constantsOn.structure fβ) :=
  by
  letI := constants_on.Structure fα
  letI := constants_on.Structure fβ
  exact
    ⟨fun n => Nat.casesOn n (fun F x => (congr_fun h F : _)) fun n F => isEmptyElim F, fun _ R =>
      isEmptyElim R⟩
#align first_order.language.constants_on_map_is_expansion_on FirstOrder.Language.constantsOnMap_isExpansionOn
-/

end ConstantsOn

section WithConstants

variable (L)

section

variable (α : Type w')

#print FirstOrder.Language.withConstants /-
/-- Extends a language with a constant for each element of a parameter set in `M`. -/
def withConstants : Language.{max u w', v} :=
  L.Sum (constantsOn α)
#align first_order.language.with_constants FirstOrder.Language.withConstants
-/

-- mathport name: language.with_constants
scoped[FirstOrder] notation:95 L "[[" α "]]" => L.withConstants α

/- warning: first_order.language.card_with_constants -> FirstOrder.Language.card_withConstants is a dubious translation:
lean 3 declaration is
  forall (L : FirstOrder.Language.{u1, u2}) (α : Type.{u3}), Eq.{succ (succ (max (max u1 u3) u2))} Cardinal.{max (max u1 u3) u2} (FirstOrder.Language.card.{max u1 u3, u2} (FirstOrder.Language.withConstants.{u1, u2, u3} L α)) (HAdd.hAdd.{succ (max (max u1 u3) u2), succ (max (max u1 u3) u2), succ (max (max u1 u3) u2)} Cardinal.{max (max u1 u3) u2} Cardinal.{max (max u1 u3) u2} Cardinal.{max (max u1 u3) u2} (instHAdd.{succ (max (max u1 u3) u2)} Cardinal.{max (max u1 u3) u2} Cardinal.hasAdd.{max (max u1 u3) u2}) (Cardinal.lift.{u3, max u1 u2} (FirstOrder.Language.card.{u1, u2} L)) (Cardinal.lift.{max u1 u2, u3} (Cardinal.mk.{u3} α)))
but is expected to have type
  forall (L : FirstOrder.Language.{u1, u2}) (α : Type.{u3}), Eq.{max (max (succ (succ u1)) (succ (succ u2))) (succ (succ u3))} Cardinal.{max (max u1 u3) u2} (FirstOrder.Language.card.{max u1 u3, u2} (FirstOrder.Language.withConstants.{u1, u2, u3} L α)) (HAdd.hAdd.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} Cardinal.{max (max u1 u2) u3} Cardinal.{max u3 u1 u2} Cardinal.{max (max u1 u2) u3} (instHAdd.{max (max (succ u1) (succ u2)) (succ u3)} Cardinal.{max (max u1 u2) u3} Cardinal.instAddCardinal.{max (max u1 u2) u3}) (Cardinal.lift.{u3, max u1 u2} (FirstOrder.Language.card.{u1, u2} L)) (Cardinal.lift.{max u1 u2, u3} (Cardinal.mk.{u3} α)))
Case conversion may be inaccurate. Consider using '#align first_order.language.card_with_constants FirstOrder.Language.card_withConstantsₓ'. -/
@[simp]
theorem card_withConstants :
    L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} (#α) := by
  rw [with_constants, card_sum, card_constants_on]
#align first_order.language.card_with_constants FirstOrder.Language.card_withConstants

#print FirstOrder.Language.lhomWithConstants /-
/-- The language map adding constants.  -/
@[simps]
def lhomWithConstants : L →ᴸ L[[α]] :=
  LHom.sumInl
#align first_order.language.Lhom_with_constants FirstOrder.Language.lhomWithConstants
-/

#print FirstOrder.Language.lhomWithConstants_injective /-
theorem lhomWithConstants_injective : (L.lhomWithConstants α).Injective :=
  LHom.sumInl_injective
#align first_order.language.Lhom_with_constants_injective FirstOrder.Language.lhomWithConstants_injective
-/

variable {α}

#print FirstOrder.Language.con /-
/-- The constant symbol indexed by a particular element. -/
protected def con (a : α) : L[[α]].Constants :=
  Sum.inr a
#align first_order.language.con FirstOrder.Language.con
-/

variable {L} (α)

#print FirstOrder.Language.LHom.addConstants /-
/-- Adds constants to a language map.  -/
def LHom.addConstants {L' : Language} (φ : L →ᴸ L') : L[[α]] →ᴸ L'[[α]] :=
  φ.sum_map (LHom.id _)
#align first_order.language.Lhom.add_constants FirstOrder.Language.LHom.addConstants
-/

#print FirstOrder.Language.paramsStructure /-
instance paramsStructure (A : Set α) : (constantsOn A).Structure α :=
  constantsOn.structure coe
#align first_order.language.params_Structure FirstOrder.Language.paramsStructure
-/

variable (L) (α)

/-- The language map removing an empty constant set.  -/
@[simps]
def Lequiv.addEmptyConstants [ie : IsEmpty α] : L ≃ᴸ L[[α]]
    where
  toLhom := lhomWithConstants L α
  invLhom := LHom.sumElim (LHom.id L) (LHom.ofIsEmpty (constantsOn α) L)
  left_inv := by rw [Lhom_with_constants, Lhom.sum_elim_comp_inl]
  right_inv := by
    simp only [Lhom.comp_sum_elim, Lhom_with_constants, Lhom.comp_id]
    exact trans (congr rfl (Subsingleton.elim _ _)) Lhom.sum_elim_inl_inr
#align first_order.language.Lequiv.add_empty_constants FirstOrder.Language.Lequiv.addEmptyConstants

variable {α} {β : Type _}

#print FirstOrder.Language.withConstants_funMap_sum_inl /-
@[simp]
theorem withConstants_funMap_sum_inl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {f : L.Functions n} {x : Fin n → M} : @funMap (L[[α]]) M _ n (Sum.inl f) x = funMap f x :=
  (lhomWithConstants L α).map_onFunction f x
#align first_order.language.with_constants_fun_map_sum_inl FirstOrder.Language.withConstants_funMap_sum_inl
-/

#print FirstOrder.Language.withConstants_relMap_sum_inl /-
@[simp]
theorem withConstants_relMap_sum_inl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {R : L.Relations n} {x : Fin n → M} : @RelMap (L[[α]]) M _ n (Sum.inl R) x = RelMap R x :=
  (lhomWithConstants L α).map_onRelation R x
#align first_order.language.with_constants_rel_map_sum_inl FirstOrder.Language.withConstants_relMap_sum_inl
-/

#print FirstOrder.Language.lhomWithConstantsMap /-
/-- The language map extending the constant set.  -/
def lhomWithConstantsMap (f : α → β) : L[[α]] →ᴸ L[[β]] :=
  LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)
#align first_order.language.Lhom_with_constants_map FirstOrder.Language.lhomWithConstantsMap
-/

/- warning: first_order.language.Lhom.map_constants_comp_sum_inl -> FirstOrder.Language.LHom.map_constants_comp_sumInl is a dubious translation:
lean 3 declaration is
  forall (L : FirstOrder.Language.{u1, u2}) {α : Type.{u3}} {β : Type.{u4}} {f : α -> β}, Eq.{max (succ u1) (succ (max u1 u4)) (succ u2)} (FirstOrder.Language.LHom.{u1, u2, max u1 u4, u2} L (FirstOrder.Language.withConstants.{u1, u2, u4} L β)) (FirstOrder.Language.LHom.comp.{u1, u2, max u1 u3, u2, max u1 u4, u2} L (FirstOrder.Language.withConstants.{u1, u2, u3} L α) (FirstOrder.Language.withConstants.{u1, u2, u4} L β) (FirstOrder.Language.lhomWithConstantsMap.{u1, u2, u3, u4} L α β f) (FirstOrder.Language.LHom.sumInl.{u1, u2, u3, 0} L (FirstOrder.Language.constantsOn.{u3} α))) (FirstOrder.Language.lhomWithConstants.{u1, u2, u4} L β)
but is expected to have type
  forall (L : FirstOrder.Language.{u2, u3}) {α : Type.{u4}} {β : Type.{u1}} {f : α -> β}, Eq.{max (max (succ u2) (succ u3)) (succ u1)} (FirstOrder.Language.LHom.{u2, u3, max u2 u1, u3} L (FirstOrder.Language.withConstants.{u2, u3, u1} L β)) (FirstOrder.Language.LHom.comp.{u2, u3, max u2 u4, u3, max u2 u1, u3} L (FirstOrder.Language.withConstants.{u2, u3, u4} L α) (FirstOrder.Language.withConstants.{u2, u3, u1} L β) (FirstOrder.Language.lhomWithConstantsMap.{u2, u3, u4, u1} L α β f) (FirstOrder.Language.LHom.sumInl.{u2, u3, u4, 0} L (FirstOrder.Language.constantsOn.{u4} α))) (FirstOrder.Language.lhomWithConstants.{u2, u3, u1} L β)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.map_constants_comp_sum_inl FirstOrder.Language.LHom.map_constants_comp_sumInlₓ'. -/
@[simp]
theorem LHom.map_constants_comp_sumInl {f : α → β} :
    (L.lhomWithConstantsMap f).comp LHom.sumInl = L.lhomWithConstants β := by ext (n f R) <;> rfl
#align first_order.language.Lhom.map_constants_comp_sum_inl FirstOrder.Language.LHom.map_constants_comp_sumInl

end

open FirstOrder

#print FirstOrder.Language.constantsOnSelfStructure /-
instance constantsOnSelfStructure : (constantsOn M).Structure M :=
  constantsOn.structure id
#align first_order.language.constants_on_self_Structure FirstOrder.Language.constantsOnSelfStructure
-/

#print FirstOrder.Language.withConstantsSelfStructure /-
instance withConstantsSelfStructure : L[[M]].Structure M :=
  Language.sumStructure _ _ M
#align first_order.language.with_constants_self_Structure FirstOrder.Language.withConstantsSelfStructure
-/

#print FirstOrder.Language.withConstants_self_expansion /-
instance withConstants_self_expansion : (lhomWithConstants L M).IsExpansionOn M :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
#align first_order.language.with_constants_self_expansion FirstOrder.Language.withConstants_self_expansion
-/

variable (α : Type _) [(constantsOn α).Structure M]

#print FirstOrder.Language.withConstantsStructure /-
instance withConstantsStructure : L[[α]].Structure M :=
  Language.sumStructure _ _ _
#align first_order.language.with_constants_Structure FirstOrder.Language.withConstantsStructure
-/

#print FirstOrder.Language.withConstants_expansion /-
instance withConstants_expansion : (L.lhomWithConstants α).IsExpansionOn M :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
#align first_order.language.with_constants_expansion FirstOrder.Language.withConstants_expansion
-/

#print FirstOrder.Language.addEmptyConstants_is_expansion_on' /-
instance addEmptyConstants_is_expansion_on' :
    (Lequiv.addEmptyConstants L (∅ : Set M)).toLhom.IsExpansionOn M :=
  L.withConstants_expansion _
#align first_order.language.add_empty_constants_is_expansion_on' FirstOrder.Language.addEmptyConstants_is_expansion_on'
-/

#print FirstOrder.Language.addEmptyConstants_symm_isExpansionOn /-
instance addEmptyConstants_symm_isExpansionOn :
    (Lequiv.addEmptyConstants L (∅ : Set M)).symm.toLhom.IsExpansionOn M :=
  LHom.sumElim_isExpansionOn _ _ _
#align first_order.language.add_empty_constants_symm_is_expansion_on FirstOrder.Language.addEmptyConstants_symm_isExpansionOn
-/

#print FirstOrder.Language.addConstants_expansion /-
instance addConstants_expansion {L' : Language} [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    (φ.addConstants α).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ M
#align first_order.language.add_constants_expansion FirstOrder.Language.addConstants_expansion
-/

/- warning: first_order.language.with_constants_fun_map_sum_inr -> FirstOrder.Language.withConstants_funMap_sum_inr is a dubious translation:
lean 3 declaration is
  forall (L : FirstOrder.Language.{u1, u2}) {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] (α : Type.{u4}) [_inst_2 : FirstOrder.Language.Structure.{u4, 0, u3} (FirstOrder.Language.constantsOn.{u4} α) M] {a : α} {x : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> M}, Eq.{succ u3} M (FirstOrder.Language.Structure.funMap.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M (FirstOrder.Language.withConstantsStructure.{u1, u2, u3, u4} L M _inst_1 α _inst_2) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Sum.inr.{u1, u4} (FirstOrder.Language.Functions.{u1, u2} L (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (FirstOrder.Language.Functions.{u4, 0} (FirstOrder.Language.constantsOn.{u4} α) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a) x) ((fun (a : Type.{max u1 u4}) (b : Type.{u3}) [self : HasLiftT.{succ (max u1 u4), succ u3} a b] => self.0) (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (HasLiftT.mk.{succ (max u1 u4), succ u3} (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (CoeTCₓ.coe.{succ (max u1 u4), succ u3} (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (FirstOrder.Language.hasCoeT.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M (FirstOrder.Language.withConstantsStructure.{u1, u2, u3, u4} L M _inst_1 α _inst_2)))) (FirstOrder.Language.con.{u1, u2, u4} L α a))
but is expected to have type
  forall (L : FirstOrder.Language.{u2, u3}) {M : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] (α : Type.{u1}) [_inst_2 : FirstOrder.Language.Structure.{u1, 0, u4} (FirstOrder.Language.constantsOn.{u1} α) M] {a : α} {x : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> M}, Eq.{succ u4} M (FirstOrder.Language.Structure.funMap.{max u1 u2, u3, u4} (FirstOrder.Language.withConstants.{u2, u3, u1} L α) M (FirstOrder.Language.withConstantsStructure.{u2, u3, u4, u1} L M _inst_1 α _inst_2) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Sum.inr.{u2, u1} (FirstOrder.Language.Functions.{u2, u3} L (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (FirstOrder.Language.Functions.{u1, 0} (FirstOrder.Language.constantsOn.{u1} α) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a) x) (FirstOrder.Language.constantMap.{max u2 u1, u3, u4} (FirstOrder.Language.withConstants.{u2, u3, u1} L α) M (FirstOrder.Language.withConstantsStructure.{u2, u3, u4, u1} L M _inst_1 α _inst_2) (FirstOrder.Language.con.{u2, u3, u1} L α a))
Case conversion may be inaccurate. Consider using '#align first_order.language.with_constants_fun_map_sum_inr FirstOrder.Language.withConstants_funMap_sum_inrₓ'. -/
@[simp]
theorem withConstants_funMap_sum_inr {a : α} {x : Fin 0 → M} :
    @funMap (L[[α]]) M _ 0 (Sum.inr a : L[[α]].Functions 0) x = L.con a :=
  by
  rw [Unique.eq_default x]
  exact (Lhom.sum_inr : constants_on α →ᴸ L.sum _).map_onFunction _ _
#align first_order.language.with_constants_fun_map_sum_inr FirstOrder.Language.withConstants_funMap_sum_inr

variable {α} (A : Set M)

/- warning: first_order.language.coe_con -> FirstOrder.Language.coe_con is a dubious translation:
lean 3 declaration is
  forall (L : FirstOrder.Language.{u1, u2}) {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] (A : Set.{u3} M) {a : coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A}, Eq.{succ u3} M ((fun (a : Type.{max u1 u3}) (b : Type.{u3}) [self : HasLiftT.{succ (max u1 u3), succ u3} a b] => self.0) (FirstOrder.Language.Constants.{max u1 u3, u2} (FirstOrder.Language.withConstants.{u1, u2, u3} L (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A))) M (HasLiftT.mk.{succ (max u1 u3), succ u3} (FirstOrder.Language.Constants.{max u1 u3, u2} (FirstOrder.Language.withConstants.{u1, u2, u3} L (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A))) M (CoeTCₓ.coe.{succ (max u1 u3), succ u3} (FirstOrder.Language.Constants.{max u1 u3, u2} (FirstOrder.Language.withConstants.{u1, u2, u3} L (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A))) M (FirstOrder.Language.hasCoeT.{max u1 u3, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u3} L (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A)) M (FirstOrder.Language.withConstantsStructure.{u1, u2, u3, u3} L M _inst_1 (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A) (FirstOrder.Language.paramsStructure.{u3} M A))))) (FirstOrder.Language.con.{u1, u2, u3} L (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A) a)) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A) M (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A) M (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A) M (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} M) Type.{u3} (Set.hasCoeToSort.{u3} M) A) M (coeSubtype.{succ u3} M (fun (x : M) => Membership.Mem.{u3, u3} M (Set.{u3} M) (Set.hasMem.{u3} M) x A))))) a)
but is expected to have type
  forall (L : FirstOrder.Language.{u1, u2}) {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] (A : Set.{u3} M) {a : Set.Elem.{u3} M A}, Eq.{succ u3} M (FirstOrder.Language.constantMap.{max u1 u3, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u3} L (Set.Elem.{u3} M A)) M (FirstOrder.Language.withConstantsStructure.{u1, u2, u3, u3} L M _inst_1 (Set.Elem.{u3} M A) (FirstOrder.Language.paramsStructure.{u3} M A)) (FirstOrder.Language.con.{u1, u2, u3} L (Set.Elem.{u3} M A) a)) (Subtype.val.{succ u3} M (fun (x : M) => Membership.mem.{u3, u3} M (Set.{u3} M) (Set.instMembershipSet.{u3} M) x A) a)
Case conversion may be inaccurate. Consider using '#align first_order.language.coe_con FirstOrder.Language.coe_conₓ'. -/
@[simp]
theorem coe_con {a : A} : (L.con a : M) = a :=
  rfl
#align first_order.language.coe_con FirstOrder.Language.coe_con

variable {A} {B : Set M} (h : A ⊆ B)

#print FirstOrder.Language.constantsOnMap_inclusion_isExpansionOn /-
instance constantsOnMap_inclusion_isExpansionOn :
    (LHom.constantsOnMap (Set.inclusion h)).IsExpansionOn M :=
  constantsOnMap_isExpansionOn rfl
#align first_order.language.constants_on_map_inclusion_is_expansion_on FirstOrder.Language.constantsOnMap_inclusion_isExpansionOn
-/

#print FirstOrder.Language.map_constants_inclusion_isExpansionOn /-
instance map_constants_inclusion_isExpansionOn :
    (L.lhomWithConstantsMap (Set.inclusion h)).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ _
#align first_order.language.map_constants_inclusion_is_expansion_on FirstOrder.Language.map_constants_inclusion_isExpansionOn
-/

end WithConstants

end Language

end FirstOrder

