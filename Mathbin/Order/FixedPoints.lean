/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module order.fixed_points
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Dynamics.FixedPoints.Basic
import Mathbin.Order.Hom.Order

/-!
# Fixed point construction on complete lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file sets up the basic theory of fixed points of a monotone function in a complete lattice.

## Main definitions

* `order_hom.lfp`: The least fixed point of a bundled monotone function.
* `order_hom.gfp`: The greatest fixed point of a bundled monotone function.
* `order_hom.prev_fixed`: The greatest fixed point of a bundled monotone function smaller than or
  equal to a given element.
* `order_hom.next_fixed`: The least fixed point of a bundled monotone function greater than or
  equal to a given element.
* `fixed_points.complete_lattice`: The Knaster-Tarski theorem: fixed points of a monotone
  self-map of a complete lattice form themselves a complete lattice.

## Tags

fixed point, complete lattice, monotone function
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function (fixedPoints IsFixedPt)

namespace OrderHom

section Basic

variable [CompleteLattice α] (f : α →o α)

#print OrderHom.lfp /-
/-- Least fixed point of a monotone function -/
def lfp : (α →o α) →o α where
  toFun f := sInf { a | f a ≤ a }
  monotone' f g hle := sInf_le_sInf fun a ha => (hle a).trans ha
#align order_hom.lfp OrderHom.lfp
-/

#print OrderHom.gfp /-
/-- Greatest fixed point of a monotone function -/
def gfp : (α →o α) →o α where
  toFun f := sSup { a | a ≤ f a }
  monotone' f g hle := sSup_le_sSup fun a ha => le_trans ha (hle a)
#align order_hom.gfp OrderHom.gfp
-/

theorem lfp_le {a : α} (h : f a ≤ a) : lfp f ≤ a :=
  sInf_le h
#align order_hom.lfp_le OrderHom.lfp_le

theorem lfp_le_fixed {a : α} (h : f a = a) : lfp f ≤ a :=
  f.lfp_le h.le
#align order_hom.lfp_le_fixed OrderHom.lfp_le_fixed

theorem le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ lfp f :=
  le_sInf h
#align order_hom.le_lfp OrderHom.le_lfp

theorem map_le_lfp {a : α} (ha : a ≤ f.lfp) : f a ≤ f.lfp :=
  f.le_lfp fun b hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb
#align order_hom.map_le_lfp OrderHom.map_le_lfp

#print OrderHom.map_lfp /-
@[simp]
theorem map_lfp : f (lfp f) = lfp f :=
  have h : f (lfp f) ≤ lfp f := f.map_le_lfp le_rfl
  h.antisymm <| f.lfp_le <| f.mono h
#align order_hom.map_lfp OrderHom.map_lfp
-/

#print OrderHom.isFixedPt_lfp /-
theorem isFixedPt_lfp : IsFixedPt f f.lfp :=
  f.map_lfp
#align order_hom.is_fixed_pt_lfp OrderHom.isFixedPt_lfp
-/

theorem lfp_le_map {a : α} (ha : lfp f ≤ a) : lfp f ≤ f a :=
  calc
    lfp f = f (lfp f) := f.map_lfp.symm
    _ ≤ f a := f.mono ha
    
#align order_hom.lfp_le_map OrderHom.lfp_le_map

theorem isLeast_lfp_le : IsLeast { a | f a ≤ a } (lfp f) :=
  ⟨f.map_lfp.le, fun a => f.lfp_le⟩
#align order_hom.is_least_lfp_le OrderHom.isLeast_lfp_le

/- warning: order_hom.is_least_lfp clashes with order_hom.is_least_lfp_le -> OrderHom.isLeast_lfp_le
Case conversion may be inaccurate. Consider using '#align order_hom.is_least_lfp OrderHom.isLeast_lfp_leₓ'. -/
theorem isLeast_lfp_le : IsLeast (fixedPoints f) (lfp f) :=
  ⟨f.isFixedPt_lfp, fun a => f.lfp_le_fixed⟩
#align order_hom.is_least_lfp OrderHom.isLeast_lfp_le

theorem lfp_induction {p : α → Prop} (step : ∀ a, p a → a ≤ lfp f → p (f a))
    (hSup : ∀ s, (∀ a ∈ s, p a) → p (sSup s)) : p (lfp f) :=
  by
  set s := { a | a ≤ lfp f ∧ p a }
  specialize hSup s fun a => And.right
  suffices : Sup s = lfp f; exact this ▸ hSup
  have h : Sup s ≤ lfp f := sSup_le fun b => And.left
  have hmem : f (Sup s) ∈ s := ⟨f.map_le_lfp h, step _ hSup h⟩
  exact h.antisymm (f.lfp_le <| le_sSup hmem)
#align order_hom.lfp_induction OrderHom.lfp_induction

theorem le_gfp {a : α} (h : a ≤ f a) : a ≤ gfp f :=
  le_sSup h
#align order_hom.le_gfp OrderHom.le_gfp

theorem gfp_le {a : α} (h : ∀ b, b ≤ f b → b ≤ a) : gfp f ≤ a :=
  sSup_le h
#align order_hom.gfp_le OrderHom.gfp_le

#print OrderHom.isFixedPt_gfp /-
theorem isFixedPt_gfp : IsFixedPt f (gfp f) :=
  f.dual.isFixedPt_lfp
#align order_hom.is_fixed_pt_gfp OrderHom.isFixedPt_gfp
-/

#print OrderHom.map_gfp /-
@[simp]
theorem map_gfp : f (gfp f) = gfp f :=
  f.dual.map_lfp
#align order_hom.map_gfp OrderHom.map_gfp
-/

theorem map_le_gfp {a : α} (ha : a ≤ gfp f) : f a ≤ gfp f :=
  f.dual.lfp_le_map ha
#align order_hom.map_le_gfp OrderHom.map_le_gfp

theorem gfp_le_map {a : α} (ha : gfp f ≤ a) : gfp f ≤ f a :=
  f.dual.map_le_lfp ha
#align order_hom.gfp_le_map OrderHom.gfp_le_map

theorem isGreatest_gfp_le : IsGreatest { a | a ≤ f a } (gfp f) :=
  f.dual.isLeast_lfp_le
#align order_hom.is_greatest_gfp_le OrderHom.isGreatest_gfp_le

#print OrderHom.isGreatest_gfp /-
theorem isGreatest_gfp : IsGreatest (fixedPoints f) (gfp f) :=
  f.dual.isLeast_lfp_le
#align order_hom.is_greatest_gfp OrderHom.isGreatest_gfp
-/

theorem gfp_induction {p : α → Prop} (step : ∀ a, p a → gfp f ≤ a → p (f a))
    (hInf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : p (gfp f) :=
  f.dual.lfp_induction step hInf
#align order_hom.gfp_induction OrderHom.gfp_induction

end Basic

section Eqn

variable [CompleteLattice α] [CompleteLattice β] (f : β →o α) (g : α →o β)

#print OrderHom.map_lfp_comp /-
-- Rolling rule
theorem map_lfp_comp : f (lfp (g.comp f)) = lfp (f.comp g) :=
  le_antisymm ((f.comp g).map_lfp ▸ f.mono (lfp_le_fixed _ <| congr_arg g (f.comp g).map_lfp)) <|
    lfp_le _ (congr_arg f (g.comp f).map_lfp).le
#align order_hom.map_lfp_comp OrderHom.map_lfp_comp
-/

#print OrderHom.map_gfp_comp /-
theorem map_gfp_comp : f (g.comp f).gfp = (f.comp g).gfp :=
  f.dual.map_lfp_comp g.dual
#align order_hom.map_gfp_comp OrderHom.map_gfp_comp
-/

#print OrderHom.lfp_lfp /-
-- Diagonal rule
theorem lfp_lfp (h : α →o α →o α) : lfp (lfp.comp h) = lfp h.onDiag :=
  by
  let a := lfp (lfp.comp h)
  refine' (lfp_le _ _).antisymm (lfp_le _ (Eq.le _))
  · exact lfp_le _ h.on_diag.map_lfp.le
  have ha : (lfp ∘ h) a = a := (lfp.comp h).map_lfp
  calc
    h a a = h a (lfp (h a)) := congr_arg (h a) ha.symm
    _ = lfp (h a) := (h a).map_lfp
    _ = a := ha
    
#align order_hom.lfp_lfp OrderHom.lfp_lfp
-/

#print OrderHom.gfp_gfp /-
theorem gfp_gfp (h : α →o α →o α) : gfp (gfp.comp h) = gfp h.onDiag :=
  @lfp_lfp αᵒᵈ _ <| (OrderHom.dualIso αᵒᵈ αᵒᵈ).symm.toOrderEmbedding.toOrderHom.comp h.dual
#align order_hom.gfp_gfp OrderHom.gfp_gfp
-/

end Eqn

section PrevNext

variable [CompleteLattice α] (f : α →o α)

theorem gfp_const_inf_le (x : α) : gfp (const α x ⊓ f) ≤ x :=
  gfp_le _ fun b hb => hb.trans inf_le_left
#align order_hom.gfp_const_inf_le OrderHom.gfp_const_inf_le

/-- Previous fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `f x ≤ x`, then `f.prev_fixed x hx` is the greatest fixed point of `f`
that is less than or equal to `x`. -/
def prevFixed (x : α) (hx : f x ≤ x) : fixedPoints f :=
  ⟨gfp (const α x ⊓ f),
    calc
      f (gfp (const α x ⊓ f)) = x ⊓ f (gfp (const α x ⊓ f)) :=
        Eq.symm <| inf_of_le_right <| (f.mono <| f.gfp_const_inf_le x).trans hx
      _ = gfp (const α x ⊓ f) := (const α x ⊓ f).map_gfp
      ⟩
#align order_hom.prev_fixed OrderHom.prevFixed

/-- Next fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `x ≤ f x`, then `f.next_fixed x hx` is the least fixed point of `f`
that is greater than or equal to `x`. -/
def nextFixed (x : α) (hx : x ≤ f x) : fixedPoints f :=
  { f.dual.prevFixed x hx with val := (const α x ⊔ f).lfp }
#align order_hom.next_fixed OrderHom.nextFixed

theorem prevFixed_le {x : α} (hx : f x ≤ x) : ↑(f.prevFixed x hx) ≤ x :=
  f.gfp_const_inf_le x
#align order_hom.prev_fixed_le OrderHom.prevFixed_le

theorem le_nextFixed {x : α} (hx : x ≤ f x) : x ≤ f.nextFixed x hx :=
  f.dual.prevFixed_le hx
#align order_hom.le_next_fixed OrderHom.le_nextFixed

theorem nextFixed_le {x : α} (hx : x ≤ f x) {y : fixedPoints f} (h : x ≤ y) :
    f.nextFixed x hx ≤ y :=
  Subtype.coe_le_coe.1 <| lfp_le _ <| sup_le h y.2.le
#align order_hom.next_fixed_le OrderHom.nextFixed_le

@[simp]
theorem nextFixed_le_iff {x : α} (hx : x ≤ f x) {y : fixedPoints f} :
    f.nextFixed x hx ≤ y ↔ x ≤ y :=
  ⟨fun h => (f.le_nextFixed hx).trans h, f.nextFixed_le hx⟩
#align order_hom.next_fixed_le_iff OrderHom.nextFixed_le_iff

@[simp]
theorem le_prevFixed_iff {x : α} (hx : f x ≤ x) {y : fixedPoints f} :
    y ≤ f.prevFixed x hx ↔ ↑y ≤ x :=
  f.dual.nextFixed_le_iff hx
#align order_hom.le_prev_fixed_iff OrderHom.le_prevFixed_iff

theorem le_prevFixed {x : α} (hx : f x ≤ x) {y : fixedPoints f} (h : ↑y ≤ x) :
    y ≤ f.prevFixed x hx :=
  (f.le_prevFixed_iff hx).2 h
#align order_hom.le_prev_fixed OrderHom.le_prevFixed

theorem le_map_sup_fixedPoints (x y : fixedPoints f) : (x ⊔ y : α) ≤ f (x ⊔ y) :=
  calc
    (x ⊔ y : α) = f x ⊔ f y := congr_arg₂ (· ⊔ ·) x.2.symm y.2.symm
    _ ≤ f (x ⊔ y) := f.mono.le_map_sup x y
    
#align order_hom.le_map_sup_fixed_points OrderHom.le_map_sup_fixedPoints

theorem map_inf_fixedPoints_le (x y : fixedPoints f) : f (x ⊓ y) ≤ x ⊓ y :=
  f.dual.le_map_sup_fixedPoints x y
#align order_hom.map_inf_fixed_points_le OrderHom.map_inf_fixedPoints_le

theorem le_map_sSup_subset_fixedPoints (A : Set α) (hA : A ⊆ fixedPoints f) : sSup A ≤ f (sSup A) :=
  sSup_le fun x hx => hA hx ▸ (f.mono <| le_sSup hx)
#align order_hom.le_map_Sup_subset_fixed_points OrderHom.le_map_sSup_subset_fixedPoints

theorem map_sInf_subset_fixedPoints_le (A : Set α) (hA : A ⊆ fixedPoints f) : f (sInf A) ≤ sInf A :=
  le_sInf fun x hx => hA hx ▸ (f.mono <| sInf_le hx)
#align order_hom.map_Inf_subset_fixed_points_le OrderHom.map_sInf_subset_fixedPoints_le

end PrevNext

end OrderHom

namespace FixedPoints

open OrderHom

variable [CompleteLattice α] (f : α →o α)

instance : SemilatticeSup (fixedPoints f) :=
  {
    Subtype.partialOrder
      _ with
    sup := fun x y => f.nextFixed (x ⊔ y) (f.le_map_sup_fixedPoints x y)
    le_sup_left := fun x y => Subtype.coe_le_coe.1 <| le_sup_left.trans (f.le_nextFixed _)
    le_sup_right := fun x y => Subtype.coe_le_coe.1 <| le_sup_right.trans (f.le_nextFixed _)
    sup_le := fun x y z hxz hyz => f.nextFixed_le _ <| sup_le hxz hyz }

instance : SemilatticeInf (fixedPoints f) :=
  { Subtype.partialOrder _, OrderDual.semilatticeInf (fixedPoints f.dual) with
    inf := fun x y => f.prevFixed (x ⊓ y) (f.map_inf_fixedPoints_le x y) }

instance : CompleteSemilatticeSup (fixedPoints f) :=
  {
    Subtype.partialOrder
      _ with
    sSup := fun s =>
      f.nextFixed (sSup (coe '' s))
        (f.le_map_sSup_subset_fixedPoints (coe '' s) fun z ⟨x, hx⟩ => hx.2 ▸ x.2)
    le_sup := fun s x hx =>
      Subtype.coe_le_coe.1 <| le_trans (le_sSup <| Set.mem_image_of_mem _ hx) (f.le_nextFixed _)
    sup_le := fun s x hx => f.nextFixed_le _ <| sSup_le <| Set.ball_image_iff.2 hx }

instance : CompleteSemilatticeInf (fixedPoints f) :=
  {
    Subtype.partialOrder
      _ with
    sInf := fun s =>
      f.prevFixed (sInf (coe '' s))
        (f.map_sInf_subset_fixedPoints_le (coe '' s) fun z ⟨x, hx⟩ => hx.2 ▸ x.2)
    le_inf := fun s x hx => f.le_prevFixed _ <| le_sInf <| Set.ball_image_iff.2 hx
    inf_le := fun s x hx =>
      Subtype.coe_le_coe.1 <| le_trans (f.prevFixed_le _) (sInf_le <| Set.mem_image_of_mem _ hx) }

/-- **Knaster-Tarski Theorem**: The fixed points of `f` form a complete lattice. -/
instance : CompleteLattice (fixedPoints f) :=
  { Subtype.partialOrder _, FixedPoints.semilatticeSup f, FixedPoints.semilatticeInf f,
    FixedPoints.completeSemilatticeSup f,
    FixedPoints.completeSemilatticeInf
      f with
    top := ⟨f.gfp, f.isFixedPt_gfp⟩
    bot := ⟨f.lfp, f.isFixedPt_lfp⟩
    le_top := fun x => f.le_gfp x.2.ge
    bot_le := fun x => f.lfp_le x.2.le }

end FixedPoints

