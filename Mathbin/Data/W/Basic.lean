/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathbin.Logic.Equiv.List

#align_import data.W.basic from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# W types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given `α : Type` and `β : α → Type`, the W type determined by this data, `W_type β`, is the
inductively defined type of trees where the nodes are labeled by elements of `α` and the children of
a node labeled `a` are indexed by elements of `β a`.

This file is currently a stub, awaiting a full development of the theory. Currently, the main result
is that if `α` is an encodable fintype and `β a` is encodable for every `a : α`, then `W_type β` is
encodable. This can be used to show the encodability of other inductive types, such as those that
are commonly used to formalize syntax, e.g. terms and expressions in a given language. The strategy
is illustrated in the example found in the file `prop_encodable` in the `archive/examples` folder of
mathlib.

## Implementation details

While the name `W_type` is somewhat verbose, it is preferable to putting a single character
identifier `W` in the root namespace.
-/


#print WType /-
/--
Given `β : α → Type*`, `W_type β` is the type of finitely branching trees where nodes are labeled by
elements of `α` and the children of a node labeled `a` are indexed by elements of `β a`.
-/
inductive WType {α : Type _} (β : α → Type _)
  | mk (a : α) (f : β a → WType) : WType
#align W_type WType
-/

instance : Inhabited (WType fun _ : Unit => Empty) :=
  ⟨WType.mk Unit.unit Empty.elim⟩

namespace WType

variable {α : Type _} {β : α → Type _}

#print WType.toSigma /-
/-- The canonical map to the corresponding sigma type, returning the label of a node as an
  element `a` of `α`, and the children of the node as a function `β a → W_type β`. -/
def toSigma : WType β → Σ a : α, β a → WType β
  | ⟨a, f⟩ => ⟨a, f⟩
#align W_type.to_sigma WType.toSigma
-/

#print WType.ofSigma /-
/-- The canonical map from the sigma type into a `W_type`. Given a node `a : α`, and
  its children as a function `β a → W_type β`, return the corresponding tree. -/
def ofSigma : (Σ a : α, β a → WType β) → WType β
  | ⟨a, f⟩ => WType.mk a f
#align W_type.of_sigma WType.ofSigma
-/

#print WType.ofSigma_toSigma /-
@[simp]
theorem ofSigma_toSigma : ∀ w : WType β, ofSigma (toSigma w) = w
  | ⟨a, f⟩ => rfl
#align W_type.of_sigma_to_sigma WType.ofSigma_toSigma
-/

#print WType.toSigma_ofSigma /-
@[simp]
theorem toSigma_ofSigma : ∀ s : Σ a : α, β a → WType β, toSigma (ofSigma s) = s
  | ⟨a, f⟩ => rfl
#align W_type.to_sigma_of_sigma WType.toSigma_ofSigma
-/

variable (β)

#print WType.equivSigma /-
/-- The canonical bijection with the sigma type, showing that `W_type` is a fixed point of
  the polynomial functor `X ↦ Σ a : α, β a → X`. -/
@[simps]
def equivSigma : WType β ≃ Σ a : α, β a → WType β
    where
  toFun := toSigma
  invFun := ofSigma
  left_inv := ofSigma_toSigma
  right_inv := toSigma_ofSigma
#align W_type.equiv_sigma WType.equivSigma
-/

variable {β}

#print WType.elim /-
/-- The canonical map from `W_type β` into any type `γ` given a map `(Σ a : α, β a → γ) → γ`. -/
def elim (γ : Type _) (fγ : (Σ a : α, β a → γ) → γ) : WType β → γ
  | ⟨a, f⟩ => fγ ⟨a, fun b => elim (f b)⟩
#align W_type.elim WType.elim
-/

#print WType.elim_injective /-
theorem elim_injective (γ : Type _) (fγ : (Σ a : α, β a → γ) → γ)
    (fγ_injective : Function.Injective fγ) : Function.Injective (elim γ fγ)
  | ⟨a₁, f₁⟩, ⟨a₂, f₂⟩, h =>
    by
    obtain ⟨rfl, h⟩ := Sigma.mk.inj (fγ_injective h)
    congr with x
    exact elim_injective (congr_fun (eq_of_hEq h) x : _)
#align W_type.elim_injective WType.elim_injective
-/

instance [hα : IsEmpty α] : IsEmpty (WType β) :=
  ⟨fun w => WType.recOn w (IsEmpty.elim hα)⟩

#print WType.infinite_of_nonempty_of_isEmpty /-
theorem infinite_of_nonempty_of_isEmpty (a b : α) [ha : Nonempty (β a)] [he : IsEmpty (β b)] :
    Infinite (WType β) :=
  ⟨by
    intro hf
    have hba : b ≠ a := fun h => ha.elim (IsEmpty.elim' (show IsEmpty (β a) from h ▸ he))
    refine'
      not_injective_infinite_finite
        (fun n : ℕ =>
          show WType β from Nat.recOn n ⟨b, IsEmpty.elim' he⟩ fun n ih => ⟨a, fun _ => ih⟩)
        _
    intro n m h
    induction' n with n ih generalizing m h
    · cases' m with m <;> simp_all
    · cases' m with m
      · simp_all
      · refine' congr_arg Nat.succ (ih _)
        simp_all [Function.funext_iff]⟩
#align W_type.infinite_of_nonempty_of_is_empty WType.infinite_of_nonempty_of_isEmpty
-/

variable [∀ a : α, Fintype (β a)]

#print WType.depth /-
/-- The depth of a finitely branching tree. -/
def depth : WType β → ℕ
  | ⟨a, f⟩ => (Finset.sup Finset.univ fun n => depth (f n)) + 1
#align W_type.depth WType.depth
-/

#print WType.depth_pos /-
theorem depth_pos (t : WType β) : 0 < t.depth := by cases t; apply Nat.succ_pos
#align W_type.depth_pos WType.depth_pos
-/

#print WType.depth_lt_depth_mk /-
theorem depth_lt_depth_mk (a : α) (f : β a → WType β) (i : β a) : depth (f i) < depth ⟨a, f⟩ :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
#align W_type.depth_lt_depth_mk WType.depth_lt_depth_mk
-/

/-
Show that W types are encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable.

We define an auxiliary type `W_type' β n` of trees of depth at most `n`, and then we show by
induction on `n` that these are all encodable. These auxiliary constructions are not interesting in
and of themselves, so we mark them as `private`.
-/
@[reducible]
private def W_type' {α : Type _} (β : α → Type _) [∀ a : α, Fintype (β a)]
    [∀ a : α, Encodable (β a)] (n : ℕ) :=
  { t : WType β // t.depth ≤ n }

variable [∀ a : α, Encodable (β a)]

private def encodable_zero : Encodable (WType' β 0) :=
  let f : WType' β 0 → Empty := fun ⟨x, h⟩ => False.elim <| not_lt_of_ge h (WType.depth_pos _)
  let finv : Empty → WType' β 0 := by intro x; cases x
  have : ∀ x, finv (f x) = x := fun ⟨x, h⟩ => False.elim <| not_lt_of_ge h (WType.depth_pos _)
  Encodable.ofLeftInverse f finv this

private def f (n : ℕ) : WType' β (n + 1) → Σ a : α, β a → WType' β n
  | ⟨t, h⟩ => by
    cases' t with a f
    have h₀ : ∀ i : β a, WType.depth (f i) ≤ n := fun i =>
      Nat.le_of_lt_succ (lt_of_lt_of_le (WType.depth_lt_depth_mk a f i) h)
    exact ⟨a, fun i : β a => ⟨f i, h₀ i⟩⟩

private def finv (n : ℕ) : (Σ a : α, β a → WType' β n) → WType' β (n + 1)
  | ⟨a, f⟩ =>
    let f' := fun i : β a => (f i).val
    have : WType.depth ⟨a, f'⟩ ≤ n + 1 := add_le_add_right (Finset.sup_le fun b h => (f b).2) 1
    ⟨⟨a, f'⟩, this⟩

variable [Encodable α]

private def encodable_succ (n : Nat) (h : Encodable (WType' β n)) : Encodable (WType' β (n + 1)) :=
  Encodable.ofLeftInverse (f n) (finv n) (by rintro ⟨⟨_, _⟩, _⟩; rfl)

/-- `W_type` is encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable. -/
instance : Encodable (WType β) :=
  by
  haveI h' : ∀ n, Encodable (W_type' β n) := fun n => Nat.recOn n encodable_zero encodable_succ
  let f : WType β → Σ n, W_type' β n := fun t => ⟨t.depth, ⟨t, le_rfl⟩⟩
  let finv : (Σ n, W_type' β n) → WType β := fun p => p.2.1
  have : ∀ t, finv (f t) = t := fun t => rfl
  exact Encodable.ofLeftInverse f finv this

end WType

