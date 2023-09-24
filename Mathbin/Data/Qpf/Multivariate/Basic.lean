/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Data.Pfunctor.Multivariate.Basic

#align_import data.qpf.multivariate.basic from "leanprover-community/mathlib"@"23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6"

/-!
# Multivariate quotients of polynomial functors.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive list_shape (a b : Type)
| nil : list_shape
| cons : a -> b -> list_shape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def list (a : Type) := fix list_shape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def multiset (a : Type) := qpf.quot list.perm list a -- not the actual notion
```

And `multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive tree (a : Type)
| node : a -> multiset tree -> tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive tree' (a : Type)
| node : a -> multiset tree' -> tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

 * constructions
   * fix
   * cofix
   * quot
   * comp
   * sigma / pi
   * prj
   * const

each proves that some operations on functors preserves the QPF structure

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open scoped MvFunctor

#print MvQPF /-
/-- Multivariate quotients of polynomial functors.
-/
class MvQPF {n : ℕ} (F : TypeVec.{u} n → Type _) [MvFunctor F] where
  p : MvPFunctor.{u} n
  abs : ∀ {α}, P.Obj α → F α
  repr : ∀ {α}, F α → P.Obj α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α ⟹ β) (p : P.Obj α), abs (f <$$> p) = f <$$> abs p
#align mvqpf MvQPF
-/

namespace MvQPF

variable {n : ℕ} {F : TypeVec.{u} n → Type _} [MvFunctor F] [q : MvQPF F]

open MvFunctor (Liftp Liftr)

/-!
### Show that every mvqpf is a lawful mvfunctor.
-/


#print MvQPF.id_map /-
protected theorem id_map {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x := by rw [← abs_repr x];
  cases' repr x with a f; rw [← abs_map]; rfl
#align mvqpf.id_map MvQPF.id_map
-/

#print MvQPF.comp_map /-
@[simp]
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
    (g ⊚ f) <$$> x = g <$$> f <$$> x := by rw [← abs_repr x]; cases' repr x with a f;
  rw [← abs_map, ← abs_map, ← abs_map]; rfl
#align mvqpf.comp_map MvQPF.comp_map
-/

#print MvQPF.lawfulMvFunctor /-
instance (priority := 100) lawfulMvFunctor : LawfulMvFunctor F
    where
  id_map := @MvQPF.id_map n F _ _
  comp_map := @comp_map n F _ _
#align mvqpf.is_lawful_mvfunctor MvQPF.lawfulMvFunctor
-/

#print MvQPF.liftP_iff /-
-- Lifting predicates and relations
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : F α) :
    LiftP p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
  by
  constructor
  · rintro ⟨y, hy⟩; cases' h : repr y with a f
    use a, fun i j => (f i j).val; constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]; rfl
    intro i j; apply (f i j).property
  rintro ⟨a, f, h₀, h₁⟩; dsimp at *
  use abs ⟨a, fun i j => ⟨f i j, h₁ i j⟩⟩
  rw [← abs_map, h₀]; rfl
#align mvqpf.liftp_iff MvQPF.liftP_iff
-/

#print MvQPF.liftR_iff /-
theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : F α) :
    LiftR r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
  by
  constructor
  · rintro ⟨u, xeq, yeq⟩; cases' h : repr u with a f
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor; · rw [← xeq, ← abs_repr u, h, ← abs_map]; rfl
    constructor; · rw [← yeq, ← abs_repr u, h, ← abs_map]; rfl
    intro i j; exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩
  dsimp; constructor
  · rw [xeq, ← abs_map]; rfl
  rw [yeq, ← abs_map]; rfl
#align mvqpf.liftr_iff MvQPF.liftR_iff
-/

open Set

open MvFunctor

#print MvQPF.mem_supp /-
theorem mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) :
    u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ :=
  by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : liftp (fun i u => u ∈ f i '' univ) x :=
      by
      rw [liftp_iff]; refine' ⟨a, f, haf.symm, _⟩
      intro i u; exact mem_image_of_mem _ (mem_univ _)
    exact h this
  intro h p; rw [liftp_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  rw [← hi]; apply h'
#align mvqpf.mem_supp MvQPF.mem_supp
-/

#print MvQPF.supp_eq /-
theorem supp_eq {α : TypeVec n} {i} (x : F α) :
    supp x i = {u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ} := by ext <;> apply mem_supp
#align mvqpf.supp_eq MvQPF.supp_eq
-/

#print MvQPF.has_good_supp_iff /-
theorem has_good_supp_iff {α : TypeVec n} (x : F α) :
    (∀ p, LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ i a' f', abs ⟨a', f'⟩ = x → f i '' univ ⊆ f' i '' univ :=
  by
  constructor
  · intro h
    have : liftp (supp x) x := by rw [h]; introv ; exact id
    rw [liftp_iff] at this ; rcases this with ⟨a, f, xeq, h'⟩
    refine' ⟨a, f, xeq.symm, _⟩
    intro a' f' h''
    rintro hu u ⟨j, h₂, hfi⟩
    have hh : u ∈ supp x a' := by rw [← hfi] <;> apply h'
    refine' (mem_supp x _ u).mp hh _ _ hu
  rintro ⟨a, f, xeq, h⟩ p; rw [liftp_iff]; constructor
  · rintro ⟨a', f', xeq', h'⟩ i u usuppx
    rcases(mem_supp x _ u).mp (@usuppx) a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    rw [← f'ieq]; apply h'
  intro h'
  refine' ⟨a, f, xeq.symm, _⟩; intro j y
  apply h'; rw [mem_supp]
  intro a' f' xeq'
  apply h _ a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)
#align mvqpf.has_good_supp_iff MvQPF.has_good_supp_iff
-/

variable (q)

#print MvQPF.IsUniform /-
/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : TypeVec n⦄ (a a' : q.p.A) (f : q.p.B a ⟹ α) (f' : q.p.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ
#align mvqpf.is_uniform MvQPF.IsUniform
-/

#print MvQPF.LiftPPreservation /-
/-- does `abs` preserve `liftp`? -/
def LiftPPreservation : Prop :=
  ∀ ⦃α : TypeVec n⦄ (p : ∀ ⦃i⦄, α i → Prop) (x : q.p.Obj α), LiftP p (abs x) ↔ LiftP p x
#align mvqpf.liftp_preservation MvQPF.LiftPPreservation
-/

#print MvQPF.SuppPreservation /-
/-- does `abs` preserve `supp`? -/
def SuppPreservation : Prop :=
  ∀ ⦃α⦄ (x : q.p.Obj α), supp (abs x) = supp x
#align mvqpf.supp_preservation MvQPF.SuppPreservation
-/

variable (q)

#print MvQPF.supp_eq_of_isUniform /-
theorem supp_eq_of_isUniform (h : q.IsUniform) {α : TypeVec n} (a : q.p.A) (f : q.p.B a ⟹ α) :
    ∀ i, supp (abs ⟨a, f⟩) i = f i '' univ := by
  intro; ext u; rw [mem_supp]; constructor
  · intro h'; apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'
#align mvqpf.supp_eq_of_is_uniform MvQPF.supp_eq_of_isUniform
-/

#print MvQPF.liftP_iff_of_isUniform /-
theorem liftP_iff_of_isUniform (h : q.IsUniform) {α : TypeVec n} (x : F α) (p : ∀ i, α i → Prop) :
    LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u :=
  by
  rw [liftp_iff, ← abs_repr x]
  cases' repr x with a f; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_is_uniform h, h _ _ _ _ abseq]
    rintro b ⟨i, _, hi⟩; rw [← hi]; apply hf
  intro h'
  refine' ⟨a, f, rfl, fun _ i => h' _ _ _⟩
  rw [supp_eq_of_is_uniform h]
  exact ⟨i, mem_univ i, rfl⟩
#align mvqpf.liftp_iff_of_is_uniform MvQPF.liftP_iff_of_isUniform
-/

#print MvQPF.supp_map /-
theorem supp_map (h : q.IsUniform) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i) :
    supp (g <$$> x) i = g i '' supp x i :=
  by
  rw [← abs_repr x]; cases' repr x with a f; rw [← abs_map, MvPFunctor.map_eq]
  rw [supp_eq_of_is_uniform h, supp_eq_of_is_uniform h, ← image_comp]
  rfl
#align mvqpf.supp_map MvQPF.supp_map
-/

#print MvQPF.suppPreservation_iff_isUniform /-
theorem suppPreservation_iff_isUniform : q.SuppPreservation ↔ q.IsUniform :=
  by
  constructor
  · intro h α a a' f f' h' i
    rw [← MvPFunctor.supp_eq, ← MvPFunctor.supp_eq, ← h, h', h]
  · rintro h α ⟨a, f⟩; ext; rwa [supp_eq_of_is_uniform, MvPFunctor.supp_eq]
#align mvqpf.supp_preservation_iff_uniform MvQPF.suppPreservation_iff_isUniform
-/

#print MvQPF.suppPreservation_iff_liftpPreservation /-
theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftPPreservation :=
  by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h; rw [supp_preservation_iff_uniform] at h' 
    dsimp only [supp_preservation, supp] at h 
    simp only [liftp_iff_of_is_uniform, supp_eq_of_is_uniform, MvPFunctor.liftP_iff', h',
      image_univ, mem_range, exists_imp]
    constructor <;> intros <;> subst_vars <;> solve_by_elim
  · rintro α ⟨a, f⟩
    simp only [liftp_preservation] at h 
    ext; simp [supp, h]
#align mvqpf.supp_preservation_iff_liftp_preservation MvQPF.suppPreservation_iff_liftpPreservation
-/

#print MvQPF.liftpPreservation_iff_uniform /-
theorem liftpPreservation_iff_uniform : q.LiftPPreservation ↔ q.IsUniform := by
  rw [← supp_preservation_iff_liftp_preservation, supp_preservation_iff_uniform]
#align mvqpf.liftp_preservation_iff_uniform MvQPF.liftpPreservation_iff_uniform
-/

end MvQPF

