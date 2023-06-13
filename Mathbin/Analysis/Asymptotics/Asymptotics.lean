/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.asymptotics.asymptotics
! leanprover-community/mathlib commit 9a48a083b390d9b84a71efbdc4e8dfa26a687104
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.InfiniteSum
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Topology.Algebra.Order.LiminfLimsup
import Mathbin.Topology.LocalHomeomorph

/-!
# Asymptotics

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce these relations:

* `is_O_with c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =o[l] g` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

The relation `is_O_with c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `is_O` and `is_o`. Usually proofs outside of this file should use `is_O`
instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `f =O[l] g ↔ (λ x, ‖f x‖) =O[l] (λ x, ‖g x‖)`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `f =o[l] g ↔ tendsto (λ x, f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/


open Filter Set

open scoped Topology BigOperators Classical Filter NNReal

namespace Asymptotics

variable {α : Type _} {β : Type _} {E : Type _} {F : Type _} {G : Type _} {E' : Type _}
  {F' : Type _} {G' : Type _} {E'' : Type _} {F'' : Type _} {G'' : Type _} {R : Type _}
  {R' : Type _} {𝕜 : Type _} {𝕜' : Type _}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']

variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}

variable {f' : α → E'} {g' : α → F'} {k' : α → G'}

variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}

variable {l l' : Filter α}

section Defs

/-! ### Definitions -/


#print Asymptotics.IsBigOWith /-
/-- This version of the Landau notation `is_O_with C l f g` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by `C * ‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `is_O` instead of this relation. -/
irreducible_def IsBigOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
#align asymptotics.is_O_with Asymptotics.IsBigOWith
-/

#print Asymptotics.isBigOWith_iff /-
/-- Definition of `is_O_with`. We record it in a lemma as `is_O_with` is irreducible. -/
theorem isBigOWith_iff : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rw [is_O_with]
#align asymptotics.is_O_with_iff Asymptotics.isBigOWith_iff
-/

alias is_O_with_iff ↔ is_O_with.bound is_O_with.of_bound
#align asymptotics.is_O_with.bound Asymptotics.IsBigOWith.bound
#align asymptotics.is_O_with.of_bound Asymptotics.IsBigOWith.of_bound

#print Asymptotics.IsBigO /-
/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsBigO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, IsBigOWith c l f g
#align asymptotics.is_O Asymptotics.IsBigO
-/

notation:100 f " =O[" l "] " g:100 => IsBigO l f g

#print Asymptotics.isBigO_iff_isBigOWith /-
/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as `is_O` is
irreducible. -/
theorem isBigO_iff_isBigOWith : f =O[l] g ↔ ∃ c : ℝ, IsBigOWith c l f g := by rw [is_O]
#align asymptotics.is_O_iff_is_O_with Asymptotics.isBigO_iff_isBigOWith
-/

#print Asymptotics.isBigO_iff /-
/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem isBigO_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [is_O, is_O_with]
#align asymptotics.is_O_iff Asymptotics.isBigO_iff
-/

#print Asymptotics.IsBigO.of_bound /-
theorem IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  isBigO_iff.2 ⟨c, h⟩
#align asymptotics.is_O.of_bound Asymptotics.IsBigO.of_bound
-/

#print Asymptotics.IsBigO.of_bound' /-
theorem IsBigO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  IsBigO.of_bound 1 <| by simp_rw [one_mul]; exact h
#align asymptotics.is_O.of_bound' Asymptotics.IsBigO.of_bound'
-/

#print Asymptotics.IsBigO.bound /-
theorem IsBigO.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigO_iff.1
#align asymptotics.is_O.bound Asymptotics.IsBigO.bound
-/

#print Asymptotics.IsLittleO /-
/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g
#align asymptotics.is_o Asymptotics.IsLittleO
-/

notation:100 f " =o[" l "] " g:100 => IsLittleO l f g

#print Asymptotics.isLittleO_iff_forall_isBigOWith /-
/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem isLittleO_iff_forall_isBigOWith : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g := by
  rw [is_o]
#align asymptotics.is_o_iff_forall_is_O_with Asymptotics.isLittleO_iff_forall_isBigOWith
-/

alias is_o_iff_forall_is_O_with ↔ is_o.forall_is_O_with is_o.of_is_O_with
#align asymptotics.is_o.forall_is_O_with Asymptotics.IsLittleO.forall_isBigOWith
#align asymptotics.is_o.of_is_O_with Asymptotics.IsLittleO.of_isBigOWith

#print Asymptotics.isLittleO_iff /-
/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [is_o, is_O_with]
#align asymptotics.is_o_iff Asymptotics.isLittleO_iff
-/

alias is_o_iff ↔ is_o.bound is_o.of_bound
#align asymptotics.is_o.bound Asymptotics.IsLittleO.bound
#align asymptotics.is_o.of_bound Asymptotics.IsLittleO.of_bound

#print Asymptotics.IsLittleO.def /-
theorem IsLittleO.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isLittleO_iff.1 h hc
#align asymptotics.is_o.def Asymptotics.IsLittleO.def
-/

#print Asymptotics.IsLittleO.def' /-
theorem IsLittleO.def' (h : f =o[l] g) (hc : 0 < c) : IsBigOWith c l f g :=
  isBigOWith_iff.2 <| isLittleO_iff.1 h hc
#align asymptotics.is_o.def' Asymptotics.IsLittleO.def'
-/

end Defs

/-! ### Conversions -/


#print Asymptotics.IsBigOWith.isBigO /-
theorem IsBigOWith.isBigO (h : IsBigOWith c l f g) : f =O[l] g := by rw [is_O] <;> exact ⟨c, h⟩
#align asymptotics.is_O_with.is_O Asymptotics.IsBigOWith.isBigO
-/

#print Asymptotics.IsLittleO.isBigOWith /-
theorem IsLittleO.isBigOWith (hgf : f =o[l] g) : IsBigOWith 1 l f g :=
  hgf.def' zero_lt_one
#align asymptotics.is_o.is_O_with Asymptotics.IsLittleO.isBigOWith
-/

#print Asymptotics.IsLittleO.isBigO /-
theorem IsLittleO.isBigO (hgf : f =o[l] g) : f =O[l] g :=
  hgf.IsBigOWith.IsBigO
#align asymptotics.is_o.is_O Asymptotics.IsLittleO.isBigO
-/

#print Asymptotics.IsBigO.isBigOWith /-
theorem IsBigO.isBigOWith : f =O[l] g → ∃ c : ℝ, IsBigOWith c l f g :=
  isBigO_iff_isBigOWith.1
#align asymptotics.is_O.is_O_with Asymptotics.IsBigO.isBigOWith
-/

#print Asymptotics.IsBigOWith.weaken /-
theorem IsBigOWith.weaken (h : IsBigOWith c l f g') (hc : c ≤ c') : IsBigOWith c' l f g' :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ ≤ c * ‖g' x‖ := hx
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
#align asymptotics.is_O_with.weaken Asymptotics.IsBigOWith.weaken
-/

#print Asymptotics.IsBigOWith.exists_pos /-
theorem IsBigOWith.exists_pos (h : IsBigOWith c l f g') :
    ∃ (c' : _) (H : 0 < c'), IsBigOWith c' l f g' :=
  ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken <| le_max_left c 1⟩
#align asymptotics.is_O_with.exists_pos Asymptotics.IsBigOWith.exists_pos
-/

#print Asymptotics.IsBigO.exists_pos /-
theorem IsBigO.exists_pos (h : f =O[l] g') : ∃ (c : _) (H : 0 < c), IsBigOWith c l f g' :=
  let ⟨c, hc⟩ := h.IsBigOWith
  hc.exists_pos
#align asymptotics.is_O.exists_pos Asymptotics.IsBigO.exists_pos
-/

#print Asymptotics.IsBigOWith.exists_nonneg /-
theorem IsBigOWith.exists_nonneg (h : IsBigOWith c l f g') :
    ∃ (c' : _) (H : 0 ≤ c'), IsBigOWith c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩
#align asymptotics.is_O_with.exists_nonneg Asymptotics.IsBigOWith.exists_nonneg
-/

#print Asymptotics.IsBigO.exists_nonneg /-
theorem IsBigO.exists_nonneg (h : f =O[l] g') : ∃ (c : _) (H : 0 ≤ c), IsBigOWith c l f g' :=
  let ⟨c, hc⟩ := h.IsBigOWith
  hc.exists_nonneg
#align asymptotics.is_O.exists_nonneg Asymptotics.IsBigO.exists_nonneg
-/

#print Asymptotics.isBigO_iff_eventually_isBigOWith /-
/-- `f = O(g)` if and only if `is_O_with c f g` for all sufficiently large `c`. -/
theorem isBigO_iff_eventually_isBigOWith : f =O[l] g' ↔ ∀ᶠ c in atTop, IsBigOWith c l f g' :=
  isBigO_iff_isBigOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩
#align asymptotics.is_O_iff_eventually_is_O_with Asymptotics.isBigO_iff_eventually_isBigOWith
-/

#print Asymptotics.isBigO_iff_eventually /-
/-- `f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently large `c`. -/
theorem isBigO_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in atTop, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g' x‖ :=
  isBigO_iff_eventually_isBigOWith.trans <| by simp only [is_O_with]
#align asymptotics.is_O_iff_eventually Asymptotics.isBigO_iff_eventually
-/

#print Asymptotics.IsBigO.exists_mem_basis /-
theorem IsBigO.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : f =O[l] g')
    (hb : l.HasBasis p s) :
    ∃ (c : ℝ) (hc : 0 < c) (i : ι) (hi : p i), ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖ :=
  flip Exists₂.imp h.exists_pos fun c hc h => by
    simpa only [is_O_with_iff, hb.eventually_iff, exists_prop] using h
#align asymptotics.is_O.exists_mem_basis Asymptotics.IsBigO.exists_mem_basis
-/

#print Asymptotics.isBigOWith_inv /-
theorem isBigOWith_inv (hc : 0 < c) : IsBigOWith c⁻¹ l f g ↔ ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  simp only [is_O_with, ← div_eq_inv_mul, le_div_iff' hc]
#align asymptotics.is_O_with_inv Asymptotics.isBigOWith_inv
-/

#print Asymptotics.isLittleO_iff_nat_mul_le_aux /-
-- We prove this lemma with strange assumptions to get two lemmas below automatically
theorem isLittleO_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
    f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g x‖ :=
  by
  constructor
  · rintro H (_ | n)
    · refine' (H.def one_pos).mono fun x h₀' => _
      rw [Nat.cast_zero, MulZeroClass.zero_mul]
      refine' h₀.elim (fun hf => (hf x).trans _) fun hg => hg x
      rwa [one_mul] at h₀' 
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (is_O_with_inv this).1 (H.def' <| inv_pos.2 this)
  · refine' fun H => is_o_iff.2 fun ε ε0 => _
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    refine' ((is_O_with_inv hn₀).2 (H n)).bound.mono fun x hfg => _
    refine' hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le ε0 hn.le) _)
    refine' h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) _) fun h => h x
    exact inv_pos.2 hn₀
#align asymptotics.is_o_iff_nat_mul_le_aux Asymptotics.isLittleO_iff_nat_mul_le_aux
-/

#print Asymptotics.isLittleO_iff_nat_mul_le /-
theorem isLittleO_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inr fun x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le Asymptotics.isLittleO_iff_nat_mul_le
-/

#print Asymptotics.isLittleO_iff_nat_mul_le' /-
theorem isLittleO_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inl fun x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le' Asymptotics.isLittleO_iff_nat_mul_le'
-/

/-! ### Subsingleton -/


#print Asymptotics.isLittleO_of_subsingleton /-
@[nontriviality]
theorem isLittleO_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  IsLittleO.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]
#align asymptotics.is_o_of_subsingleton Asymptotics.isLittleO_of_subsingleton
-/

#print Asymptotics.isBigO_of_subsingleton /-
@[nontriviality]
theorem isBigO_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  isLittleO_of_subsingleton.IsBigO
#align asymptotics.is_O_of_subsingleton Asymptotics.isBigO_of_subsingleton
-/

section congr

variable {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/


#print Asymptotics.isBigOWith_congr /-
theorem isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂ :=
  by
  unfold is_O_with
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁, e₂]
#align asymptotics.is_O_with_congr Asymptotics.isBigOWith_congr
-/

#print Asymptotics.IsBigOWith.congr' /-
theorem IsBigOWith.congr' (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₂ l f₂ g₂ :=
  (isBigOWith_congr hc hf hg).mp h
#align asymptotics.is_O_with.congr' Asymptotics.IsBigOWith.congr'
-/

#print Asymptotics.IsBigOWith.congr /-
theorem IsBigOWith.congr (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
    (hg : ∀ x, g₁ x = g₂ x) : IsBigOWith c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O_with.congr Asymptotics.IsBigOWith.congr
-/

#print Asymptotics.IsBigOWith.congr_left /-
theorem IsBigOWith.congr_left (h : IsBigOWith c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) :
    IsBigOWith c l f₂ g :=
  h.congr rfl hf fun _ => rfl
#align asymptotics.is_O_with.congr_left Asymptotics.IsBigOWith.congr_left
-/

#print Asymptotics.IsBigOWith.congr_right /-
theorem IsBigOWith.congr_right (h : IsBigOWith c l f g₁) (hg : ∀ x, g₁ x = g₂ x) :
    IsBigOWith c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg
#align asymptotics.is_O_with.congr_right Asymptotics.IsBigOWith.congr_right
-/

#print Asymptotics.IsBigOWith.congr_const /-
theorem IsBigOWith.congr_const (h : IsBigOWith c₁ l f g) (hc : c₁ = c₂) : IsBigOWith c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl
#align asymptotics.is_O_with.congr_const Asymptotics.IsBigOWith.congr_const
-/

#print Asymptotics.isBigO_congr /-
theorem isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ := by
  unfold is_O; exact exists_congr fun c => is_O_with_congr rfl hf hg
#align asymptotics.is_O_congr Asymptotics.isBigO_congr
-/

#print Asymptotics.IsBigO.congr' /-
theorem IsBigO.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (isBigO_congr hf hg).mp h
#align asymptotics.is_O.congr' Asymptotics.IsBigO.congr'
-/

#print Asymptotics.IsBigO.congr /-
theorem IsBigO.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O.congr Asymptotics.IsBigO.congr
-/

#print Asymptotics.IsBigO.congr_left /-
theorem IsBigO.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_O.congr_left Asymptotics.IsBigO.congr_left
-/

#print Asymptotics.IsBigO.congr_right /-
theorem IsBigO.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_O.congr_right Asymptotics.IsBigO.congr_right
-/

#print Asymptotics.isLittleO_congr /-
theorem isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ := by
  unfold is_o; exact forall₂_congr fun c hc => is_O_with_congr (Eq.refl c) hf hg
#align asymptotics.is_o_congr Asymptotics.isLittleO_congr
-/

#print Asymptotics.IsLittleO.congr' /-
theorem IsLittleO.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (isLittleO_congr hf hg).mp h
#align asymptotics.is_o.congr' Asymptotics.IsLittleO.congr'
-/

#print Asymptotics.IsLittleO.congr /-
theorem IsLittleO.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_o.congr Asymptotics.IsLittleO.congr
-/

#print Asymptotics.IsLittleO.congr_left /-
theorem IsLittleO.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_o.congr_left Asymptotics.IsLittleO.congr_left
-/

#print Asymptotics.IsLittleO.congr_right /-
theorem IsLittleO.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_o.congr_right Asymptotics.IsLittleO.congr_right
-/

#print Filter.EventuallyEq.trans_isBigO /-
@[trans]
theorem Filter.EventuallyEq.trans_isBigO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =O[l] g) : f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_O Filter.EventuallyEq.trans_isBigO
-/

#print Filter.EventuallyEq.trans_isLittleO /-
@[trans]
theorem Filter.EventuallyEq.trans_isLittleO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =o[l] g) : f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_o Filter.EventuallyEq.trans_isLittleO
-/

#print Asymptotics.IsBigO.trans_eventuallyEq /-
@[trans]
theorem IsBigO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_O.trans_eventually_eq Asymptotics.IsBigO.trans_eventuallyEq
-/

#print Asymptotics.IsLittleO.trans_eventuallyEq /-
@[trans]
theorem IsLittleO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =o[l] g₁)
    (hg : g₁ =ᶠ[l] g₂) : f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_o.trans_eventually_eq Asymptotics.IsLittleO.trans_eventuallyEq
-/

end congr

/-! ### Filter operations and transitivity -/


#print Asymptotics.IsBigOWith.comp_tendsto /-
theorem IsBigOWith.comp_tendsto (hcfg : IsBigOWith c l f g) {k : β → α} {l' : Filter β}
    (hk : Tendsto k l' l) : IsBigOWith c l' (f ∘ k) (g ∘ k) :=
  IsBigOWith.of_bound <| hk hcfg.bound
#align asymptotics.is_O_with.comp_tendsto Asymptotics.IsBigOWith.comp_tendsto
-/

#print Asymptotics.IsBigO.comp_tendsto /-
theorem IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k) :=
  isBigO_iff_isBigOWith.2 <| hfg.IsBigOWith.imp fun c h => h.comp_tendsto hk
#align asymptotics.is_O.comp_tendsto Asymptotics.IsBigO.comp_tendsto
-/

#print Asymptotics.IsLittleO.comp_tendsto /-
theorem IsLittleO.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  IsLittleO.of_isBigOWith fun c cpos => (hfg.forall_isBigOWith cpos).comp_tendsto hk
#align asymptotics.is_o.comp_tendsto Asymptotics.IsLittleO.comp_tendsto
-/

#print Asymptotics.isBigOWith_map /-
@[simp]
theorem isBigOWith_map {k : β → α} {l : Filter β} :
    IsBigOWith c (map k l) f g ↔ IsBigOWith c l (f ∘ k) (g ∘ k) := by unfold is_O_with;
  exact eventually_map
#align asymptotics.is_O_with_map Asymptotics.isBigOWith_map
-/

#print Asymptotics.isBigO_map /-
@[simp]
theorem isBigO_map {k : β → α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [is_O, is_O_with_map]
#align asymptotics.is_O_map Asymptotics.isBigO_map
-/

#print Asymptotics.isLittleO_map /-
@[simp]
theorem isLittleO_map {k : β → α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [is_o, is_O_with_map]
#align asymptotics.is_o_map Asymptotics.isLittleO_map
-/

#print Asymptotics.IsBigOWith.mono /-
theorem IsBigOWith.mono (h : IsBigOWith c l' f g) (hl : l ≤ l') : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| hl h.bound
#align asymptotics.is_O_with.mono Asymptotics.IsBigOWith.mono
-/

#print Asymptotics.IsBigO.mono /-
theorem IsBigO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
  isBigO_iff_isBigOWith.2 <| h.IsBigOWith.imp fun c h => h.mono hl
#align asymptotics.is_O.mono Asymptotics.IsBigO.mono
-/

#print Asymptotics.IsLittleO.mono /-
theorem IsLittleO.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos => (h.forall_isBigOWith cpos).mono hl
#align asymptotics.is_o.mono Asymptotics.IsLittleO.mono
-/

#print Asymptotics.IsBigOWith.trans /-
theorem IsBigOWith.trans (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 ≤ c) :
    IsBigOWith (c * c') l f k := by
  unfold is_O_with at *
  filter_upwards [hfg, hgk] with x hx hx'
  calc
    ‖f x‖ ≤ c * ‖g x‖ := hx
    _ ≤ c * (c' * ‖k x‖) := (mul_le_mul_of_nonneg_left hx' hc)
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm
#align asymptotics.is_O_with.trans Asymptotics.IsBigOWith.trans
-/

#print Asymptotics.IsBigO.trans /-
@[trans]
theorem IsBigO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
    f =O[l] k :=
  let ⟨c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨c', hc'⟩ := hgk.IsBigOWith
  (hc.trans hc' cnonneg).IsBigO
#align asymptotics.is_O.trans Asymptotics.IsBigO.trans
-/

#print Asymptotics.IsLittleO.trans_isBigOWith /-
theorem IsLittleO.trans_isBigOWith (hfg : f =o[l] g) (hgk : IsBigOWith c l g k) (hc : 0 < c) :
    f =o[l] k := by
  unfold is_o at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel _ hc.ne')
#align asymptotics.is_o.trans_is_O_with Asymptotics.IsLittleO.trans_isBigOWith
-/

#print Asymptotics.IsLittleO.trans_isBigO /-
@[trans]
theorem IsLittleO.trans_isBigO {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g)
    (hgk : g =O[l] k) : f =o[l] k :=
  let ⟨c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isBigOWith hc cpos
#align asymptotics.is_o.trans_is_O Asymptotics.IsLittleO.trans_isBigO
-/

#print Asymptotics.IsBigOWith.trans_isLittleO /-
theorem IsBigOWith.trans_isLittleO (hfg : IsBigOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c) :
    f =o[l] k := by
  unfold is_o at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel' _ hc.ne')
#align asymptotics.is_O_with.trans_is_o Asymptotics.IsBigOWith.trans_isLittleO
-/

#print Asymptotics.IsBigO.trans_isLittleO /-
@[trans]
theorem IsBigO.trans_isLittleO {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g)
    (hgk : g =o[l] k) : f =o[l] k :=
  let ⟨c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isLittleO hgk cpos
#align asymptotics.is_O.trans_is_o Asymptotics.IsBigO.trans_isLittleO
-/

#print Asymptotics.IsLittleO.trans /-
@[trans]
theorem IsLittleO.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  hfg.trans_isBigOWith hgk.IsBigOWith one_pos
#align asymptotics.is_o.trans Asymptotics.IsLittleO.trans
-/

#print Filter.Eventually.trans_isBigO /-
theorem Filter.Eventually.trans_isBigO {f : α → E} {g : α → F'} {k : α → G}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
  (IsBigO.of_bound' hfg).trans hgk
#align filter.eventually.trans_is_O Filter.Eventually.trans_isBigO
-/

#print Filter.Eventually.isBigO /-
theorem Filter.Eventually.isBigO {f : α → E} {g : α → ℝ} {l : Filter α}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ g x) : f =O[l] g :=
  IsBigO.of_bound' <| hfg.mono fun x hx => hx.trans <| Real.le_norm_self _
#align filter.eventually.is_O Filter.Eventually.isBigO
-/

section

variable (l)

#print Asymptotics.isBigOWith_of_le' /-
theorem isBigOWith_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| univ_mem' hfg
#align asymptotics.is_O_with_of_le' Asymptotics.isBigOWith_of_le'
-/

#print Asymptotics.isBigOWith_of_le /-
theorem isBigOWith_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : IsBigOWith 1 l f g :=
  isBigOWith_of_le' l fun x => by rw [one_mul]; exact hfg x
#align asymptotics.is_O_with_of_le Asymptotics.isBigOWith_of_le
-/

#print Asymptotics.isBigO_of_le' /-
theorem isBigO_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le' l hfg).IsBigO
#align asymptotics.is_O_of_le' Asymptotics.isBigO_of_le'
-/

#print Asymptotics.isBigO_of_le /-
theorem isBigO_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le l hfg).IsBigO
#align asymptotics.is_O_of_le Asymptotics.isBigO_of_le
-/

end

#print Asymptotics.isBigOWith_refl /-
theorem isBigOWith_refl (f : α → E) (l : Filter α) : IsBigOWith 1 l f f :=
  isBigOWith_of_le l fun _ => le_rfl
#align asymptotics.is_O_with_refl Asymptotics.isBigOWith_refl
-/

#print Asymptotics.isBigO_refl /-
theorem isBigO_refl (f : α → E) (l : Filter α) : f =O[l] f :=
  (isBigOWith_refl f l).IsBigO
#align asymptotics.is_O_refl Asymptotics.isBigO_refl
-/

#print Asymptotics.IsBigOWith.trans_le /-
theorem IsBigOWith.trans_le (hfg : IsBigOWith c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
    IsBigOWith c l f k :=
  (hfg.trans (isBigOWith_of_le l hgk) hc).congr_const <| mul_one c
#align asymptotics.is_O_with.trans_le Asymptotics.IsBigOWith.trans_le
-/

#print Asymptotics.IsBigO.trans_le /-
theorem IsBigO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
  hfg.trans (isBigO_of_le l hgk)
#align asymptotics.is_O.trans_le Asymptotics.IsBigO.trans_le
-/

#print Asymptotics.IsLittleO.trans_le /-
theorem IsLittleO.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
  hfg.trans_isBigOWith (isBigOWith_of_le _ hgk) zero_lt_one
#align asymptotics.is_o.trans_le Asymptotics.IsLittleO.trans_le
-/

#print Asymptotics.isLittleO_irrefl' /-
theorem isLittleO_irrefl' (h : ∃ᶠ x in l, ‖f' x‖ ≠ 0) : ¬f' =o[l] f' :=
  by
  intro ho
  rcases((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div, ← div_eq_inv_mul] at hle 
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_le hle
#align asymptotics.is_o_irrefl' Asymptotics.isLittleO_irrefl'
-/

#print Asymptotics.isLittleO_irrefl /-
theorem isLittleO_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
  isLittleO_irrefl' <| h.mono fun x => norm_ne_zero_iff.mpr
#align asymptotics.is_o_irrefl Asymptotics.isLittleO_irrefl
-/

#print Asymptotics.IsBigO.not_isLittleO /-
theorem IsBigO.not_isLittleO (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =o[l] f'' :=
  fun h' => isLittleO_irrefl hf (h.trans_isLittleO h')
#align asymptotics.is_O.not_is_o Asymptotics.IsBigO.not_isLittleO
-/

#print Asymptotics.IsLittleO.not_isBigO /-
theorem IsLittleO.not_isBigO (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =O[l] f'' :=
  fun h' => isLittleO_irrefl hf (h.trans_isBigO h')
#align asymptotics.is_o.not_is_O Asymptotics.IsLittleO.not_isBigO
-/

section Bot

variable (c f g)

#print Asymptotics.isBigOWith_bot /-
@[simp]
theorem isBigOWith_bot : IsBigOWith c ⊥ f g :=
  IsBigOWith.of_bound <| trivial
#align asymptotics.is_O_with_bot Asymptotics.isBigOWith_bot
-/

#print Asymptotics.isBigO_bot /-
@[simp]
theorem isBigO_bot : f =O[⊥] g :=
  (isBigOWith_bot 1 f g).IsBigO
#align asymptotics.is_O_bot Asymptotics.isBigO_bot
-/

#print Asymptotics.isLittleO_bot /-
@[simp]
theorem isLittleO_bot : f =o[⊥] g :=
  IsLittleO.of_isBigOWith fun c _ => isBigOWith_bot c f g
#align asymptotics.is_o_bot Asymptotics.isLittleO_bot
-/

end Bot

#print Asymptotics.isBigOWith_pure /-
@[simp]
theorem isBigOWith_pure {x} : IsBigOWith c (pure x) f g ↔ ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff
#align asymptotics.is_O_with_pure Asymptotics.isBigOWith_pure
-/

#print Asymptotics.IsBigOWith.sup /-
theorem IsBigOWith.sup (h : IsBigOWith c l f g) (h' : IsBigOWith c l' f g) :
    IsBigOWith c (l ⊔ l') f g :=
  IsBigOWith.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩
#align asymptotics.is_O_with.sup Asymptotics.IsBigOWith.sup
-/

#print Asymptotics.IsBigOWith.sup' /-
theorem IsBigOWith.sup' (h : IsBigOWith c l f g') (h' : IsBigOWith c' l' f g') :
    IsBigOWith (max c c') (l ⊔ l') f g' :=
  IsBigOWith.of_bound <|
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩
#align asymptotics.is_O_with.sup' Asymptotics.IsBigOWith.sup'
-/

#print Asymptotics.IsBigO.sup /-
theorem IsBigO.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
  let ⟨c, hc⟩ := h.IsBigOWith
  let ⟨c', hc'⟩ := h'.IsBigOWith
  (hc.sup' hc').IsBigO
#align asymptotics.is_O.sup Asymptotics.IsBigO.sup
-/

#print Asymptotics.IsLittleO.sup /-
theorem IsLittleO.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
  IsLittleO.of_isBigOWith fun c cpos => (h.forall_isBigOWith cpos).sup (h'.forall_isBigOWith cpos)
#align asymptotics.is_o.sup Asymptotics.IsLittleO.sup
-/

#print Asymptotics.isBigO_sup /-
@[simp]
theorem isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_O_sup Asymptotics.isBigO_sup
-/

#print Asymptotics.isLittleO_sup /-
@[simp]
theorem isLittleO_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_o_sup Asymptotics.isLittleO_sup
-/

#print Asymptotics.isBigOWith_insert /-
theorem isBigOWith_insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h : ‖g x‖ ≤ C * ‖g' x‖) : IsBigOWith C (𝓝[insert x s] x) g g' ↔ IsBigOWith C (𝓝[s] x) g g' :=
  by simp_rw [is_O_with, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and_iff]
#align asymptotics.is_O_with_insert Asymptotics.isBigOWith_insert
-/

#print Asymptotics.IsBigOWith.insert /-
theorem IsBigOWith.insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h1 : IsBigOWith C (𝓝[s] x) g g') (h2 : ‖g x‖ ≤ C * ‖g' x‖) :
    IsBigOWith C (𝓝[insert x s] x) g g' :=
  (isBigOWith_insert h2).mpr h1
#align asymptotics.is_O_with.insert Asymptotics.IsBigOWith.insert
-/

#print Asymptotics.isLittleO_insert /-
theorem isLittleO_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' :=
  by
  simp_rw [is_o]
  refine' forall_congr' fun c => forall_congr' fun hc => _
  rw [is_O_with_insert]
  rw [h, norm_zero]
  exact mul_nonneg hc.le (norm_nonneg _)
#align asymptotics.is_o_insert Asymptotics.isLittleO_insert
-/

#print Asymptotics.IsLittleO.insert /-
theorem IsLittleO.insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
  (isLittleO_insert h2).mpr h1
#align asymptotics.is_o.insert Asymptotics.IsLittleO.insert
-/

/-! ### Simplification : norm, abs -/


section NormAbs

variable {u v : α → ℝ}

#print Asymptotics.isBigOWith_norm_right /-
@[simp]
theorem isBigOWith_norm_right : (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g' := by
  simp only [is_O_with, norm_norm]
#align asymptotics.is_O_with_norm_right Asymptotics.isBigOWith_norm_right
-/

#print Asymptotics.isBigOWith_abs_right /-
@[simp]
theorem isBigOWith_abs_right : (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u :=
  @isBigOWith_norm_right _ _ _ _ _ _ f u l
#align asymptotics.is_O_with_abs_right Asymptotics.isBigOWith_abs_right
-/

alias is_O_with_norm_right ↔ is_O_with.of_norm_right is_O_with.norm_right
#align asymptotics.is_O_with.of_norm_right Asymptotics.IsBigOWith.of_norm_right
#align asymptotics.is_O_with.norm_right Asymptotics.IsBigOWith.norm_right

alias is_O_with_abs_right ↔ is_O_with.of_abs_right is_O_with.abs_right
#align asymptotics.is_O_with.of_abs_right Asymptotics.IsBigOWith.of_abs_right
#align asymptotics.is_O_with.abs_right Asymptotics.IsBigOWith.abs_right

#print Asymptotics.isBigO_norm_right /-
@[simp]
theorem isBigO_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g' := by unfold is_O;
  exact exists_congr fun _ => is_O_with_norm_right
#align asymptotics.is_O_norm_right Asymptotics.isBigO_norm_right
-/

#print Asymptotics.isBigO_abs_right /-
@[simp]
theorem isBigO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  @isBigO_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_O_abs_right Asymptotics.isBigO_abs_right
-/

alias is_O_norm_right ↔ is_O.of_norm_right is_O.norm_right
#align asymptotics.is_O.of_norm_right Asymptotics.IsBigO.of_norm_right
#align asymptotics.is_O.norm_right Asymptotics.IsBigO.norm_right

alias is_O_abs_right ↔ is_O.of_abs_right is_O.abs_right
#align asymptotics.is_O.of_abs_right Asymptotics.IsBigO.of_abs_right
#align asymptotics.is_O.abs_right Asymptotics.IsBigO.abs_right

#print Asymptotics.isLittleO_norm_right /-
@[simp]
theorem isLittleO_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g' := by unfold is_o;
  exact forall₂_congr fun _ _ => is_O_with_norm_right
#align asymptotics.is_o_norm_right Asymptotics.isLittleO_norm_right
-/

#print Asymptotics.isLittleO_abs_right /-
@[simp]
theorem isLittleO_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  @isLittleO_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_o_abs_right Asymptotics.isLittleO_abs_right
-/

alias is_o_norm_right ↔ is_o.of_norm_right is_o.norm_right
#align asymptotics.is_o.of_norm_right Asymptotics.IsLittleO.of_norm_right
#align asymptotics.is_o.norm_right Asymptotics.IsLittleO.norm_right

alias is_o_abs_right ↔ is_o.of_abs_right is_o.abs_right
#align asymptotics.is_o.of_abs_right Asymptotics.IsLittleO.of_abs_right
#align asymptotics.is_o.abs_right Asymptotics.IsLittleO.abs_right

#print Asymptotics.isBigOWith_norm_left /-
@[simp]
theorem isBigOWith_norm_left : IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g := by
  simp only [is_O_with, norm_norm]
#align asymptotics.is_O_with_norm_left Asymptotics.isBigOWith_norm_left
-/

#print Asymptotics.isBigOWith_abs_left /-
@[simp]
theorem isBigOWith_abs_left : IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g :=
  @isBigOWith_norm_left _ _ _ _ _ _ g u l
#align asymptotics.is_O_with_abs_left Asymptotics.isBigOWith_abs_left
-/

alias is_O_with_norm_left ↔ is_O_with.of_norm_left is_O_with.norm_left
#align asymptotics.is_O_with.of_norm_left Asymptotics.IsBigOWith.of_norm_left
#align asymptotics.is_O_with.norm_left Asymptotics.IsBigOWith.norm_left

alias is_O_with_abs_left ↔ is_O_with.of_abs_left is_O_with.abs_left
#align asymptotics.is_O_with.of_abs_left Asymptotics.IsBigOWith.of_abs_left
#align asymptotics.is_O_with.abs_left Asymptotics.IsBigOWith.abs_left

#print Asymptotics.isBigO_norm_left /-
@[simp]
theorem isBigO_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g := by unfold is_O;
  exact exists_congr fun _ => is_O_with_norm_left
#align asymptotics.is_O_norm_left Asymptotics.isBigO_norm_left
-/

#print Asymptotics.isBigO_abs_left /-
@[simp]
theorem isBigO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  @isBigO_norm_left _ _ _ _ _ g u l
#align asymptotics.is_O_abs_left Asymptotics.isBigO_abs_left
-/

alias is_O_norm_left ↔ is_O.of_norm_left is_O.norm_left
#align asymptotics.is_O.of_norm_left Asymptotics.IsBigO.of_norm_left
#align asymptotics.is_O.norm_left Asymptotics.IsBigO.norm_left

alias is_O_abs_left ↔ is_O.of_abs_left is_O.abs_left
#align asymptotics.is_O.of_abs_left Asymptotics.IsBigO.of_abs_left
#align asymptotics.is_O.abs_left Asymptotics.IsBigO.abs_left

#print Asymptotics.isLittleO_norm_left /-
@[simp]
theorem isLittleO_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g := by unfold is_o;
  exact forall₂_congr fun _ _ => is_O_with_norm_left
#align asymptotics.is_o_norm_left Asymptotics.isLittleO_norm_left
-/

#print Asymptotics.isLittleO_abs_left /-
@[simp]
theorem isLittleO_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  @isLittleO_norm_left _ _ _ _ _ g u l
#align asymptotics.is_o_abs_left Asymptotics.isLittleO_abs_left
-/

alias is_o_norm_left ↔ is_o.of_norm_left is_o.norm_left
#align asymptotics.is_o.of_norm_left Asymptotics.IsLittleO.of_norm_left
#align asymptotics.is_o.norm_left Asymptotics.IsLittleO.norm_left

alias is_o_abs_left ↔ is_o.of_abs_left is_o.abs_left
#align asymptotics.is_o.of_abs_left Asymptotics.IsLittleO.of_abs_left
#align asymptotics.is_o.abs_left Asymptotics.IsLittleO.abs_left

#print Asymptotics.isBigOWith_norm_norm /-
theorem isBigOWith_norm_norm :
    (IsBigOWith c l (fun x => ‖f' x‖) fun x => ‖g' x‖) ↔ IsBigOWith c l f' g' :=
  isBigOWith_norm_left.trans isBigOWith_norm_right
#align asymptotics.is_O_with_norm_norm Asymptotics.isBigOWith_norm_norm
-/

#print Asymptotics.isBigOWith_abs_abs /-
theorem isBigOWith_abs_abs :
    (IsBigOWith c l (fun x => |u x|) fun x => |v x|) ↔ IsBigOWith c l u v :=
  isBigOWith_abs_left.trans isBigOWith_abs_right
#align asymptotics.is_O_with_abs_abs Asymptotics.isBigOWith_abs_abs
-/

alias is_O_with_norm_norm ↔ is_O_with.of_norm_norm is_O_with.norm_norm
#align asymptotics.is_O_with.of_norm_norm Asymptotics.IsBigOWith.of_norm_norm
#align asymptotics.is_O_with.norm_norm Asymptotics.IsBigOWith.norm_norm

alias is_O_with_abs_abs ↔ is_O_with.of_abs_abs is_O_with.abs_abs
#align asymptotics.is_O_with.of_abs_abs Asymptotics.IsBigOWith.of_abs_abs
#align asymptotics.is_O_with.abs_abs Asymptotics.IsBigOWith.abs_abs

#print Asymptotics.isBigO_norm_norm /-
theorem isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g' :=
  isBigO_norm_left.trans isBigO_norm_right
#align asymptotics.is_O_norm_norm Asymptotics.isBigO_norm_norm
-/

#print Asymptotics.isBigO_abs_abs /-
theorem isBigO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  isBigO_abs_left.trans isBigO_abs_right
#align asymptotics.is_O_abs_abs Asymptotics.isBigO_abs_abs
-/

alias is_O_norm_norm ↔ is_O.of_norm_norm is_O.norm_norm
#align asymptotics.is_O.of_norm_norm Asymptotics.IsBigO.of_norm_norm
#align asymptotics.is_O.norm_norm Asymptotics.IsBigO.norm_norm

alias is_O_abs_abs ↔ is_O.of_abs_abs is_O.abs_abs
#align asymptotics.is_O.of_abs_abs Asymptotics.IsBigO.of_abs_abs
#align asymptotics.is_O.abs_abs Asymptotics.IsBigO.abs_abs

#print Asymptotics.isLittleO_norm_norm /-
theorem isLittleO_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g' :=
  isLittleO_norm_left.trans isLittleO_norm_right
#align asymptotics.is_o_norm_norm Asymptotics.isLittleO_norm_norm
-/

#print Asymptotics.isLittleO_abs_abs /-
theorem isLittleO_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  isLittleO_abs_left.trans isLittleO_abs_right
#align asymptotics.is_o_abs_abs Asymptotics.isLittleO_abs_abs
-/

alias is_o_norm_norm ↔ is_o.of_norm_norm is_o.norm_norm
#align asymptotics.is_o.of_norm_norm Asymptotics.IsLittleO.of_norm_norm
#align asymptotics.is_o.norm_norm Asymptotics.IsLittleO.norm_norm

alias is_o_abs_abs ↔ is_o.of_abs_abs is_o.abs_abs
#align asymptotics.is_o.of_abs_abs Asymptotics.IsLittleO.of_abs_abs
#align asymptotics.is_o.abs_abs Asymptotics.IsLittleO.abs_abs

end NormAbs

/-! ### Simplification: negate -/


#print Asymptotics.isBigOWith_neg_right /-
@[simp]
theorem isBigOWith_neg_right : (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g' := by
  simp only [is_O_with, norm_neg]
#align asymptotics.is_O_with_neg_right Asymptotics.isBigOWith_neg_right
-/

alias is_O_with_neg_right ↔ is_O_with.of_neg_right is_O_with.neg_right
#align asymptotics.is_O_with.of_neg_right Asymptotics.IsBigOWith.of_neg_right
#align asymptotics.is_O_with.neg_right Asymptotics.IsBigOWith.neg_right

#print Asymptotics.isBigO_neg_right /-
@[simp]
theorem isBigO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' := by unfold is_O;
  exact exists_congr fun _ => is_O_with_neg_right
#align asymptotics.is_O_neg_right Asymptotics.isBigO_neg_right
-/

alias is_O_neg_right ↔ is_O.of_neg_right is_O.neg_right
#align asymptotics.is_O.of_neg_right Asymptotics.IsBigO.of_neg_right
#align asymptotics.is_O.neg_right Asymptotics.IsBigO.neg_right

#print Asymptotics.isLittleO_neg_right /-
@[simp]
theorem isLittleO_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' := by unfold is_o;
  exact forall₂_congr fun _ _ => is_O_with_neg_right
#align asymptotics.is_o_neg_right Asymptotics.isLittleO_neg_right
-/

alias is_o_neg_right ↔ is_o.of_neg_right is_o.neg_right
#align asymptotics.is_o.of_neg_right Asymptotics.IsLittleO.of_neg_right
#align asymptotics.is_o.neg_right Asymptotics.IsLittleO.neg_right

#print Asymptotics.isBigOWith_neg_left /-
@[simp]
theorem isBigOWith_neg_left : IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g := by
  simp only [is_O_with, norm_neg]
#align asymptotics.is_O_with_neg_left Asymptotics.isBigOWith_neg_left
-/

alias is_O_with_neg_left ↔ is_O_with.of_neg_left is_O_with.neg_left
#align asymptotics.is_O_with.of_neg_left Asymptotics.IsBigOWith.of_neg_left
#align asymptotics.is_O_with.neg_left Asymptotics.IsBigOWith.neg_left

#print Asymptotics.isBigO_neg_left /-
@[simp]
theorem isBigO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g := by unfold is_O;
  exact exists_congr fun _ => is_O_with_neg_left
#align asymptotics.is_O_neg_left Asymptotics.isBigO_neg_left
-/

alias is_O_neg_left ↔ is_O.of_neg_left is_O.neg_left
#align asymptotics.is_O.of_neg_left Asymptotics.IsBigO.of_neg_left
#align asymptotics.is_O.neg_left Asymptotics.IsBigO.neg_left

#print Asymptotics.isLittleO_neg_left /-
@[simp]
theorem isLittleO_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g := by unfold is_o;
  exact forall₂_congr fun _ _ => is_O_with_neg_left
#align asymptotics.is_o_neg_left Asymptotics.isLittleO_neg_left
-/

alias is_o_neg_left ↔ is_o.of_neg_right is_o.neg_left
#align asymptotics.is_o.of_neg_right Asymptotics.IsLittleO.of_neg_right
#align asymptotics.is_o.neg_left Asymptotics.IsLittleO.neg_left

/-! ### Product of functions (right) -/


#print Asymptotics.isBigOWith_fst_prod /-
theorem isBigOWith_fst_prod : IsBigOWith 1 l f' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun x => le_max_left _ _
#align asymptotics.is_O_with_fst_prod Asymptotics.isBigOWith_fst_prod
-/

#print Asymptotics.isBigOWith_snd_prod /-
theorem isBigOWith_snd_prod : IsBigOWith 1 l g' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun x => le_max_right _ _
#align asymptotics.is_O_with_snd_prod Asymptotics.isBigOWith_snd_prod
-/

#print Asymptotics.isBigO_fst_prod /-
theorem isBigO_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_fst_prod.IsBigO
#align asymptotics.is_O_fst_prod Asymptotics.isBigO_fst_prod
-/

#print Asymptotics.isBigO_snd_prod /-
theorem isBigO_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_snd_prod.IsBigO
#align asymptotics.is_O_snd_prod Asymptotics.isBigO_snd_prod
-/

#print Asymptotics.isBigO_fst_prod' /-
theorem isBigO_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [is_O, is_O_with] using is_O_fst_prod
#align asymptotics.is_O_fst_prod' Asymptotics.isBigO_fst_prod'
-/

#print Asymptotics.isBigO_snd_prod' /-
theorem isBigO_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [is_O, is_O_with] using is_O_snd_prod
#align asymptotics.is_O_snd_prod' Asymptotics.isBigO_snd_prod'
-/

section

variable (f' k')

#print Asymptotics.IsBigOWith.prod_rightl /-
theorem IsBigOWith.prod_rightl (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (g' x, k' x) :=
  (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightl Asymptotics.IsBigOWith.prod_rightl
-/

#print Asymptotics.IsBigO.prod_rightl /-
theorem IsBigO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).IsBigO
#align asymptotics.is_O.prod_rightl Asymptotics.IsBigO.prod_rightl
-/

#print Asymptotics.IsLittleO.prod_rightl /-
theorem IsLittleO.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  IsLittleO.of_isBigOWith fun c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le
#align asymptotics.is_o.prod_rightl Asymptotics.IsLittleO.prod_rightl
-/

#print Asymptotics.IsBigOWith.prod_rightr /-
theorem IsBigOWith.prod_rightr (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (f' x, g' x) :=
  (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightr Asymptotics.IsBigOWith.prod_rightr
-/

#print Asymptotics.IsBigO.prod_rightr /-
theorem IsBigO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).IsBigO
#align asymptotics.is_O.prod_rightr Asymptotics.IsBigO.prod_rightr
-/

#print Asymptotics.IsLittleO.prod_rightr /-
theorem IsLittleO.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  IsLittleO.of_isBigOWith fun c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le
#align asymptotics.is_o.prod_rightr Asymptotics.IsLittleO.prod_rightr
-/

end

#print Asymptotics.IsBigOWith.prod_left_same /-
theorem IsBigOWith.prod_left_same (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k') :
    IsBigOWith c l (fun x => (f' x, g' x)) k' := by
  rw [is_O_with_iff] at * <;> filter_upwards [hf, hg] with x using max_le
#align asymptotics.is_O_with.prod_left_same Asymptotics.IsBigOWith.prod_left_same
-/

#print Asymptotics.IsBigOWith.prod_left /-
theorem IsBigOWith.prod_left (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k') :
    IsBigOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')
#align asymptotics.is_O_with.prod_left Asymptotics.IsBigOWith.prod_left
-/

#print Asymptotics.IsBigOWith.prod_left_fst /-
theorem IsBigOWith.prod_left_fst (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l f' k' :=
  (isBigOWith_fst_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_fst Asymptotics.IsBigOWith.prod_left_fst
-/

#print Asymptotics.IsBigOWith.prod_left_snd /-
theorem IsBigOWith.prod_left_snd (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l g' k' :=
  (isBigOWith_snd_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_snd Asymptotics.IsBigOWith.prod_left_snd
-/

#print Asymptotics.isBigOWith_prod_left /-
theorem isBigOWith_prod_left :
    IsBigOWith c l (fun x => (f' x, g' x)) k' ↔ IsBigOWith c l f' k' ∧ IsBigOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩
#align asymptotics.is_O_with_prod_left Asymptotics.isBigOWith_prod_left
-/

#print Asymptotics.IsBigO.prod_left /-
theorem IsBigO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨c, hf⟩ := hf.IsBigOWith
  let ⟨c', hg⟩ := hg.IsBigOWith
  (hf.prodLeft hg).IsBigO
#align asymptotics.is_O.prod_left Asymptotics.IsBigO.prod_left
-/

#print Asymptotics.IsBigO.prod_left_fst /-
theorem IsBigO.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k' :=
  IsBigO.trans isBigO_fst_prod
#align asymptotics.is_O.prod_left_fst Asymptotics.IsBigO.prod_left_fst
-/

#print Asymptotics.IsBigO.prod_left_snd /-
theorem IsBigO.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k' :=
  IsBigO.trans isBigO_snd_prod
#align asymptotics.is_O.prod_left_snd Asymptotics.IsBigO.prod_left_snd
-/

#print Asymptotics.isBigO_prod_left /-
@[simp]
theorem isBigO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩
#align asymptotics.is_O_prod_left Asymptotics.isBigO_prod_left
-/

#print Asymptotics.IsLittleO.prod_left /-
theorem IsLittleO.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') :
    (fun x => (f' x, g' x)) =o[l] k' :=
  IsLittleO.of_isBigOWith fun c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)
#align asymptotics.is_o.prod_left Asymptotics.IsLittleO.prod_left
-/

#print Asymptotics.IsLittleO.prod_left_fst /-
theorem IsLittleO.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_fst_prod
#align asymptotics.is_o.prod_left_fst Asymptotics.IsLittleO.prod_left_fst
-/

#print Asymptotics.IsLittleO.prod_left_snd /-
theorem IsLittleO.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_snd_prod
#align asymptotics.is_o.prod_left_snd Asymptotics.IsLittleO.prod_left_snd
-/

#print Asymptotics.isLittleO_prod_left /-
@[simp]
theorem isLittleO_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩
#align asymptotics.is_o_prod_left Asymptotics.isLittleO_prod_left
-/

#print Asymptotics.IsBigOWith.eq_zero_imp /-
theorem IsBigOWith.eq_zero_imp (h : IsBigOWith c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 <| by simpa [hg] using hx
#align asymptotics.is_O_with.eq_zero_imp Asymptotics.IsBigOWith.eq_zero_imp
-/

#print Asymptotics.IsBigO.eq_zero_imp /-
theorem IsBigO.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨C, hC⟩ := h.IsBigOWith
  hC.eq_zero_imp
#align asymptotics.is_O.eq_zero_imp Asymptotics.IsBigO.eq_zero_imp
-/

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

#print Asymptotics.IsBigOWith.add /-
theorem IsBigOWith.add (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [is_O_with] at * <;>
    filter_upwards [h₁, h₂] with x hx₁ hx₂ using
      calc
        ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
        _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm
#align asymptotics.is_O_with.add Asymptotics.IsBigOWith.add
-/

#print Asymptotics.IsBigO.add /-
theorem IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨c₁, hc₁⟩ := h₁.IsBigOWith
  let ⟨c₂, hc₂⟩ := h₂.IsBigOWith
  (hc₁.add hc₂).IsBigO
#align asymptotics.is_O.add Asymptotics.IsBigO.add
-/

#print Asymptotics.IsLittleO.add /-
theorem IsLittleO.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add
          (h₂.forall_isBigOWith <| half_pos cpos)).congr_const
      (add_halves c)
#align asymptotics.is_o.add Asymptotics.IsLittleO.add
-/

#print Asymptotics.IsLittleO.add_add /-
theorem IsLittleO.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine' (h₁.trans_le fun x => _).add (h₂.trans_le _) <;> simp [abs_of_nonneg, add_nonneg]
#align asymptotics.is_o.add_add Asymptotics.IsLittleO.add_add
-/

#print Asymptotics.IsBigO.add_isLittleO /-
theorem IsBigO.add_isLittleO (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.IsBigO
#align asymptotics.is_O.add_is_o Asymptotics.IsBigO.add_isLittleO
-/

#print Asymptotics.IsLittleO.add_isBigO /-
theorem IsLittleO.add_isBigO (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.IsBigO.add h₂
#align asymptotics.is_o.add_is_O Asymptotics.IsLittleO.add_isBigO
-/

#print Asymptotics.IsBigOWith.add_isLittleO /-
theorem IsBigOWith.add_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)
#align asymptotics.is_O_with.add_is_o Asymptotics.IsBigOWith.add_isLittleO
-/

#print Asymptotics.IsLittleO.add_isBigOWith /-
theorem IsLittleO.add_isBigOWith (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _
#align asymptotics.is_o.add_is_O_with Asymptotics.IsLittleO.add_isBigOWith
-/

#print Asymptotics.IsBigOWith.sub /-
theorem IsBigOWith.sub (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_O_with.sub Asymptotics.IsBigOWith.sub
-/

#print Asymptotics.IsBigOWith.sub_isLittleO /-
theorem IsBigOWith.sub_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_is_o h₂.neg_left hc
#align asymptotics.is_O_with.sub_is_o Asymptotics.IsBigOWith.sub_isLittleO
-/

#print Asymptotics.IsBigO.sub /-
theorem IsBigO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_O.sub Asymptotics.IsBigO.sub
-/

#print Asymptotics.IsLittleO.sub /-
theorem IsLittleO.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_o.sub Asymptotics.IsLittleO.sub
-/

end add_sub

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/


section IsOOAsRel

variable {f₁ f₂ f₃ : α → E'}

#print Asymptotics.IsBigOWith.symm /-
theorem IsBigOWith.symm (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g) :
    IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun x => neg_sub _ _
#align asymptotics.is_O_with.symm Asymptotics.IsBigOWith.symm
-/

#print Asymptotics.isBigOWith_comm /-
theorem isBigOWith_comm :
    IsBigOWith c l (fun x => f₁ x - f₂ x) g ↔ IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsBigOWith.symm, IsBigOWith.symm⟩
#align asymptotics.is_O_with_comm Asymptotics.isBigOWith_comm
-/

#print Asymptotics.IsBigO.symm /-
theorem IsBigO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun x => neg_sub _ _
#align asymptotics.is_O.symm Asymptotics.IsBigO.symm
-/

#print Asymptotics.isBigO_comm /-
theorem isBigO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsBigO.symm, IsBigO.symm⟩
#align asymptotics.is_O_comm Asymptotics.isBigO_comm
-/

#print Asymptotics.IsLittleO.symm /-
theorem IsLittleO.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left
#align asymptotics.is_o.symm Asymptotics.IsLittleO.symm
-/

#print Asymptotics.isLittleO_comm /-
theorem isLittleO_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsLittleO.symm, IsLittleO.symm⟩
#align asymptotics.is_o_comm Asymptotics.isLittleO_comm
-/

#print Asymptotics.IsBigOWith.triangle /-
theorem IsBigOWith.triangle (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
    (h₂ : IsBigOWith c' l (fun x => f₂ x - f₃ x) g) :
    IsBigOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O_with.triangle Asymptotics.IsBigOWith.triangle
-/

#print Asymptotics.IsBigO.triangle /-
theorem IsBigO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) : (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O.triangle Asymptotics.IsBigO.triangle
-/

#print Asymptotics.IsLittleO.triangle /-
theorem IsLittleO.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_o.triangle Asymptotics.IsLittleO.triangle
-/

#print Asymptotics.IsBigO.congr_of_sub /-
theorem IsBigO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩
#align asymptotics.is_O.congr_of_sub Asymptotics.IsBigO.congr_of_sub
-/

#print Asymptotics.IsLittleO.congr_of_sub /-
theorem IsLittleO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩
#align asymptotics.is_o.congr_of_sub Asymptotics.IsLittleO.congr_of_sub
-/

end IsOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

#print Asymptotics.isLittleO_zero /-
theorem isLittleO_zero : (fun x => (0 : E')) =o[l] g' :=
  IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)
#align asymptotics.is_o_zero Asymptotics.isLittleO_zero
-/

#print Asymptotics.isBigOWith_zero /-
theorem isBigOWith_zero (hc : 0 ≤ c) : IsBigOWith c l (fun x => (0 : E')) g' :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)
#align asymptotics.is_O_with_zero Asymptotics.isBigOWith_zero
-/

#print Asymptotics.isBigOWith_zero' /-
theorem isBigOWith_zero' : IsBigOWith 0 l (fun x => (0 : E')) g :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simp
#align asymptotics.is_O_with_zero' Asymptotics.isBigOWith_zero'
-/

#print Asymptotics.isBigO_zero /-
theorem isBigO_zero : (fun x => (0 : E')) =O[l] g :=
  isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩
#align asymptotics.is_O_zero Asymptotics.isBigO_zero
-/

#print Asymptotics.isBigO_refl_left /-
theorem isBigO_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (isBigO_zero g' l).congr_left fun x => (sub_self _).symm
#align asymptotics.is_O_refl_left Asymptotics.isBigO_refl_left
-/

#print Asymptotics.isLittleO_refl_left /-
theorem isLittleO_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (isLittleO_zero g' l).congr_left fun x => (sub_self _).symm
#align asymptotics.is_o_refl_left Asymptotics.isLittleO_refl_left
-/

variable {g g' l}

#print Asymptotics.isBigOWith_zero_right_iff /-
@[simp]
theorem isBigOWith_zero_right_iff : (IsBigOWith c l f'' fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [is_O_with, exists_prop, true_and_iff, norm_zero, MulZeroClass.mul_zero,
    norm_le_zero_iff, eventually_eq, Pi.zero_apply]
#align asymptotics.is_O_with_zero_right_iff Asymptotics.isBigOWith_zero_right_iff
-/

#print Asymptotics.isBigO_zero_right_iff /-
@[simp]
theorem isBigO_zero_right_iff : (f'' =O[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨c, hc⟩ := h.IsBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).IsBigO⟩
#align asymptotics.is_O_zero_right_iff Asymptotics.isBigO_zero_right_iff
-/

#print Asymptotics.isLittleO_zero_right_iff /-
@[simp]
theorem isLittleO_zero_right_iff : (f'' =o[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => isBigO_zero_right_iff.1 h.IsBigO, fun h =>
    IsLittleO.of_isBigOWith fun c hc => isBigOWith_zero_right_iff.2 h⟩
#align asymptotics.is_o_zero_right_iff Asymptotics.isLittleO_zero_right_iff
-/

#print Asymptotics.isBigOWith_const_const /-
theorem isBigOWith_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / ‖c'‖) l (fun x : α => c) fun x => c' :=
  by
  unfold is_O_with
  apply univ_mem'
  intro x
  rw [mem_set_of_eq, div_mul_cancel]
  rwa [Ne.def, norm_eq_zero]
#align asymptotics.is_O_with_const_const Asymptotics.isBigOWith_const_const
-/

#print Asymptotics.isBigO_const_const /-
theorem isBigO_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    (fun x : α => c) =O[l] fun x => c' :=
  (isBigOWith_const_const c hc' l).IsBigO
#align asymptotics.is_O_const_const Asymptotics.isBigO_const_const
-/

#print Asymptotics.isBigO_const_const_iff /-
@[simp]
theorem isBigO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.ne_bot] :
    ((fun x : α => c) =O[l] fun x => c') ↔ c' = 0 → c = 0 :=
  by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [eventually_eq]
  · simp [hc', is_O_const_const _ hc']
#align asymptotics.is_O_const_const_iff Asymptotics.isBigO_const_const_iff
-/

#print Asymptotics.isBigO_pure /-
@[simp]
theorem isBigO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := isBigO_const_const_iff _
#align asymptotics.is_O_pure Asymptotics.isBigO_pure
-/

end ZeroConst

#print Asymptotics.isBigOWith_top /-
@[simp]
theorem isBigOWith_top : IsBigOWith c ⊤ f g ↔ ∀ x, ‖f x‖ ≤ c * ‖g x‖ := by rw [is_O_with] <;> rfl
#align asymptotics.is_O_with_top Asymptotics.isBigOWith_top
-/

#print Asymptotics.isBigO_top /-
@[simp]
theorem isBigO_top : f =O[⊤] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by rw [is_O_iff] <;> rfl
#align asymptotics.is_O_top Asymptotics.isBigO_top
-/

#print Asymptotics.isLittleO_top /-
@[simp]
theorem isLittleO_top : f'' =o[⊤] g'' ↔ ∀ x, f'' x = 0 :=
  by
  refine' ⟨_, fun h => (is_o_zero g'' ⊤).congr (fun x => (h x).symm) fun x => rfl⟩
  simp only [is_o_iff, eventually_top]
  refine' fun h x => norm_le_zero_iff.1 _
  have : tendsto (fun c : ℝ => c * ‖g'' x‖) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (MulZeroClass.zero_mul _)).mono_left
      inf_le_left
  exact
    le_of_tendsto_of_tendsto tendsto_const_nhds this
      (eventually_nhdsWithin_iff.2 <| eventually_of_forall fun c hc => h hc x)
#align asymptotics.is_o_top Asymptotics.isLittleO_top
-/

#print Asymptotics.isBigOWith_principal /-
@[simp]
theorem isBigOWith_principal {s : Set α} : IsBigOWith c (𝓟 s) f g ↔ ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [is_O_with] <;> rfl
#align asymptotics.is_O_with_principal Asymptotics.isBigOWith_principal
-/

#print Asymptotics.isBigO_principal /-
theorem isBigO_principal {s : Set α} : f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [is_O_iff] <;> rfl
#align asymptotics.is_O_principal Asymptotics.isBigO_principal
-/

section

variable (F) [One F] [NormOneClass F]

#print Asymptotics.isBigOWith_const_one /-
theorem isBigOWith_const_one (c : E) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x : α => c) fun x => (1 : F) := by simp [is_O_with_iff]
#align asymptotics.is_O_with_const_one Asymptotics.isBigOWith_const_one
-/

#print Asymptotics.isBigO_const_one /-
theorem isBigO_const_one (c : E) (l : Filter α) : (fun x : α => c) =O[l] fun x => (1 : F) :=
  (isBigOWith_const_one F c l).IsBigO
#align asymptotics.is_O_const_one Asymptotics.isBigO_const_one
-/

#print Asymptotics.isLittleO_const_iff_isLittleO_one /-
theorem isLittleO_const_iff_isLittleO_one {c : F''} (hc : c ≠ 0) :
    (f =o[l] fun x => c) ↔ f =o[l] fun x => (1 : F) :=
  ⟨fun h => h.trans_isBigOWith (isBigOWith_const_one _ _ _) (norm_pos_iff.2 hc), fun h =>
    h.trans_isBigO <| isBigO_const_const _ hc _⟩
#align asymptotics.is_o_const_iff_is_o_one Asymptotics.isLittleO_const_iff_isLittleO_one
-/

#print Asymptotics.isLittleO_one_iff /-
@[simp]
theorem isLittleO_one_iff : f' =o[l] (fun x => 1 : α → F) ↔ Tendsto f' l (𝓝 0) := by
  simp only [is_o_iff, norm_one, mul_one, metric.nhds_basis_closed_ball.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]
#align asymptotics.is_o_one_iff Asymptotics.isLittleO_one_iff
-/

#print Asymptotics.isBigO_one_iff /-
@[simp]
theorem isBigO_one_iff : f =O[l] (fun x => 1 : α → F) ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ :=
  by simp only [is_O_iff, norm_one, mul_one]; rfl
#align asymptotics.is_O_one_iff Asymptotics.isBigO_one_iff
-/

alias is_O_one_iff ↔ _ _root_.filter.is_bounded_under.is_O_one
#align filter.is_bounded_under.is_O_one Filter.IsBoundedUnder.isBigO_one

#print Asymptotics.isLittleO_one_left_iff /-
@[simp]
theorem isLittleO_one_left_iff : (fun x => 1 : α → F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop :=
  calc
    (fun x => 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖(1 : F)‖ ≤ ‖f x‖ :=
      isLittleO_iff_nat_mul_le_aux <| Or.inl fun x => by simp only [norm_one, zero_le_one]
    _ ↔ ∀ n : ℕ, True → ∀ᶠ x in l, ‖f x‖ ∈ Ici (n : ℝ) := by
      simp only [norm_one, mul_one, true_imp_iff, mem_Ici]
    _ ↔ Tendsto (fun x => ‖f x‖) l atTop :=
      atTop_hasCountableBasis_of_archimedean.1.tendsto_right_iff.symm
#align asymptotics.is_o_one_left_iff Asymptotics.isLittleO_one_left_iff
-/

#print Filter.Tendsto.isBigO_one /-
theorem Filter.Tendsto.isBigO_one {c : E'} (h : Tendsto f' l (𝓝 c)) :
    f' =O[l] (fun x => 1 : α → F) :=
  h.norm.isBoundedUnder_le.isBigO_one F
#align filter.tendsto.is_O_one Filter.Tendsto.isBigO_one
-/

#print Asymptotics.IsBigO.trans_tendsto_nhds /-
theorem IsBigO.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) :
    f =O[l] (fun x => 1 : α → F) :=
  hfg.trans <| hg.isBigO_one F
#align asymptotics.is_O.trans_tendsto_nhds Asymptotics.IsBigO.trans_tendsto_nhds
-/

end

#print Asymptotics.isLittleO_const_iff /-
theorem isLittleO_const_iff {c : F''} (hc : c ≠ 0) : (f'' =o[l] fun x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (isLittleO_const_iff_isLittleO_one ℝ hc).trans (isLittleO_one_iff _)
#align asymptotics.is_o_const_iff Asymptotics.isLittleO_const_iff
-/

#print Asymptotics.isLittleO_id_const /-
theorem isLittleO_id_const {c : F''} (hc : c ≠ 0) : (fun x : E'' => x) =o[𝓝 0] fun x => c :=
  (isLittleO_const_iff hc).mpr (continuous_id.Tendsto 0)
#align asymptotics.is_o_id_const Asymptotics.isLittleO_id_const
-/

#print Filter.IsBoundedUnder.isBigO_const /-
theorem Filter.IsBoundedUnder.isBigO_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) {c : F''}
    (hc : c ≠ 0) : f =O[l] fun x => c :=
  (h.isBigO_one ℝ).trans (isBigO_const_const _ hc _)
#align filter.is_bounded_under.is_O_const Filter.IsBoundedUnder.isBigO_const
-/

#print Asymptotics.isBigO_const_of_tendsto /-
theorem isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
    f'' =O[l] fun x => c :=
  h.norm.isBoundedUnder_le.isBigO_const hc
#align asymptotics.is_O_const_of_tendsto Asymptotics.isBigO_const_of_tendsto
-/

#print Asymptotics.IsBigO.isBoundedUnder_le /-
theorem IsBigO.isBoundedUnder_le {c : F} (h : f =O[l] fun x => c) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩
#align asymptotics.is_O.is_bounded_under_le Asymptotics.IsBigO.isBoundedUnder_le
-/

#print Asymptotics.isBigO_const_of_ne /-
theorem isBigO_const_of_ne {c : F''} (hc : c ≠ 0) :
    (f =O[l] fun x => c) ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  ⟨fun h => h.isBoundedUnder_le, fun h => h.isBigO_const hc⟩
#align asymptotics.is_O_const_of_ne Asymptotics.isBigO_const_of_ne
-/

#print Asymptotics.isBigO_const_iff /-
theorem isBigO_const_iff {c : F''} :
    (f'' =O[l] fun x => c) ↔ (c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· ≤ ·) l fun x => ‖f'' x‖ :=
  by
  refine' ⟨fun h => ⟨fun hc => is_O_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, _⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts [(hcf hc).trans_isBigO (is_O_zero _ _), hf.is_O_const hc]
#align asymptotics.is_O_const_iff Asymptotics.isBigO_const_iff
-/

#print Asymptotics.isBigO_iff_isBoundedUnder_le_div /-
theorem isBigO_iff_isBoundedUnder_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ / ‖g'' x‖ :=
  by
  simp only [is_O_iff, is_bounded_under, is_bounded, eventually_map]
  exact
    exists_congr fun c =>
      eventually_congr <| h.mono fun x hx => (div_le_iff <| norm_pos_iff.2 hx).symm
#align asymptotics.is_O_iff_is_bounded_under_le_div Asymptotics.isBigO_iff_isBoundedUnder_le_div
-/

#print Asymptotics.isBigO_const_left_iff_pos_le_norm /-
/-- `(λ x, c) =O[l] f` if and only if `f` is bounded away from zero. -/
theorem isBigO_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
    (fun x => c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ‖f' x‖ :=
  by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine' ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, _⟩
    exact hC.bound.mono fun x => (div_le_iff' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine' is_O.of_bound (‖c‖ / b) (hb.mono fun x hx => _)
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)
#align asymptotics.is_O_const_left_iff_pos_le_norm Asymptotics.isBigO_const_left_iff_pos_le_norm
-/

section

variable (𝕜)

end

#print Asymptotics.IsBigO.trans_tendsto /-
theorem IsBigO.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  (isLittleO_one_iff ℝ).1 <| hfg.trans_isLittleO <| (isLittleO_one_iff ℝ).2 hg
#align asymptotics.is_O.trans_tendsto Asymptotics.IsBigO.trans_tendsto
-/

#print Asymptotics.IsLittleO.trans_tendsto /-
theorem IsLittleO.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  hfg.IsBigO.trans_tendsto hg
#align asymptotics.is_o.trans_tendsto Asymptotics.IsLittleO.trans_tendsto
-/

/-! ### Multiplication by a constant -/


#print Asymptotics.isBigOWith_const_mul_self /-
theorem isBigOWith_const_mul_self (c : R) (f : α → R) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x => c * f x) f :=
  isBigOWith_of_le' _ fun x => norm_mul_le _ _
#align asymptotics.is_O_with_const_mul_self Asymptotics.isBigOWith_const_mul_self
-/

#print Asymptotics.isBigO_const_mul_self /-
theorem isBigO_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (isBigOWith_const_mul_self c f l).IsBigO
#align asymptotics.is_O_const_mul_self Asymptotics.isBigO_const_mul_self
-/

#print Asymptotics.IsBigOWith.const_mul_left /-
theorem IsBigOWith.const_mul_left {f : α → R} (h : IsBigOWith c l f g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' * f x) g :=
  (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')
#align asymptotics.is_O_with.const_mul_left Asymptotics.IsBigOWith.const_mul_left
-/

#print Asymptotics.IsBigO.const_mul_left /-
theorem IsBigO.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨c, hc⟩ := h.IsBigOWith
  (hc.const_mul_left c').IsBigO
#align asymptotics.is_O.const_mul_left Asymptotics.IsBigO.const_mul_left
-/

#print Asymptotics.isBigOWith_self_const_mul' /-
theorem isBigOWith_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) :
    IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x :=
  (isBigOWith_const_mul_self ↑u⁻¹ _ l).congr_left fun x => u.inv_mul_cancel_left (f x)
#align asymptotics.is_O_with_self_const_mul' Asymptotics.isBigOWith_self_const_mul'
-/

#print Asymptotics.isBigOWith_self_const_mul /-
theorem isBigOWith_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    IsBigOWith ‖c‖⁻¹ l f fun x => c * f x :=
  (isBigOWith_self_const_mul' (Units.mk0 c hc) f l).congr_const <| norm_inv c
#align asymptotics.is_O_with_self_const_mul Asymptotics.isBigOWith_self_const_mul
-/

#print Asymptotics.isBigO_self_const_mul' /-
theorem isBigO_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).IsBigO
#align asymptotics.is_O_self_const_mul' Asymptotics.isBigO_self_const_mul'
-/

#print Asymptotics.isBigO_self_const_mul /-
theorem isBigO_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  isBigO_self_const_mul' (IsUnit.mk0 c hc) f l
#align asymptotics.is_O_self_const_mul Asymptotics.isBigO_self_const_mul
-/

#print Asymptotics.isBigO_const_mul_left_iff' /-
theorem isBigO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩
#align asymptotics.is_O_const_mul_left_iff' Asymptotics.isBigO_const_mul_left_iff'
-/

#print Asymptotics.isBigO_const_mul_left_iff /-
theorem isBigO_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  isBigO_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_left_iff Asymptotics.isBigO_const_mul_left_iff
-/

#print Asymptotics.IsLittleO.const_mul_left /-
theorem IsLittleO.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (isBigO_const_mul_self c f l).trans_isLittleO h
#align asymptotics.is_o.const_mul_left Asymptotics.IsLittleO.const_mul_left
-/

#print Asymptotics.isLittleO_const_mul_left_iff' /-
theorem isLittleO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩
#align asymptotics.is_o_const_mul_left_iff' Asymptotics.isLittleO_const_mul_left_iff'
-/

#print Asymptotics.isLittleO_const_mul_left_iff /-
theorem isLittleO_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  isLittleO_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_left_iff Asymptotics.isLittleO_const_mul_left_iff
-/

#print Asymptotics.IsBigOWith.of_const_mul_right /-
theorem IsBigOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f fun x => c * g x) : IsBigOWith (c' * ‖c‖) l f g :=
  h.trans (isBigOWith_const_mul_self c g l) hc'
#align asymptotics.is_O_with.of_const_mul_right Asymptotics.IsBigOWith.of_const_mul_right
-/

#print Asymptotics.IsBigO.of_const_mul_right /-
theorem IsBigO.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).IsBigO
#align asymptotics.is_O.of_const_mul_right Asymptotics.IsBigO.of_const_mul_right
-/

#print Asymptotics.IsBigOWith.const_mul_right' /-
theorem IsBigOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (isBigOWith_self_const_mul' _ _ _) hc'
#align asymptotics.is_O_with.const_mul_right' Asymptotics.IsBigOWith.const_mul_right'
-/

#print Asymptotics.IsBigOWith.const_mul_right /-
theorem IsBigOWith.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (isBigOWith_self_const_mul c hc g l) hc'
#align asymptotics.is_O_with.const_mul_right Asymptotics.IsBigOWith.const_mul_right
-/

#print Asymptotics.IsBigO.const_mul_right' /-
theorem IsBigO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (isBigO_self_const_mul' hc g l)
#align asymptotics.is_O.const_mul_right' Asymptotics.IsBigO.const_mul_right'
-/

#print Asymptotics.IsBigO.const_mul_right /-
theorem IsBigO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_O.const_mul_right Asymptotics.IsBigO.const_mul_right
-/

#print Asymptotics.isBigO_const_mul_right_iff' /-
theorem isBigO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_O_const_mul_right_iff' Asymptotics.isBigO_const_mul_right_iff'
-/

#print Asymptotics.isBigO_const_mul_right_iff /-
theorem isBigO_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  isBigO_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_right_iff Asymptotics.isBigO_const_mul_right_iff
-/

#print Asymptotics.IsLittleO.of_const_mul_right /-
theorem IsLittleO.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) :
    f =o[l] g :=
  h.trans_isBigO (isBigO_const_mul_self c g l)
#align asymptotics.is_o.of_const_mul_right Asymptotics.IsLittleO.of_const_mul_right
-/

#print Asymptotics.IsLittleO.const_mul_right' /-
theorem IsLittleO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO (isBigO_self_const_mul' hc g l)
#align asymptotics.is_o.const_mul_right' Asymptotics.IsLittleO.const_mul_right'
-/

#print Asymptotics.IsLittleO.const_mul_right /-
theorem IsLittleO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_o.const_mul_right Asymptotics.IsLittleO.const_mul_right
-/

#print Asymptotics.isLittleO_const_mul_right_iff' /-
theorem isLittleO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_o_const_mul_right_iff' Asymptotics.isLittleO_const_mul_right_iff'
-/

#print Asymptotics.isLittleO_const_mul_right_iff /-
theorem isLittleO_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  isLittleO_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_right_iff Asymptotics.isLittleO_const_mul_right_iff
-/

/-! ### Multiplication -/


#print Asymptotics.IsBigOWith.mul /-
theorem IsBigOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x :=
  by
  unfold is_O_with at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_comm]
#align asymptotics.is_O_with.mul Asymptotics.IsBigOWith.mul
-/

#print Asymptotics.IsBigO.mul /-
theorem IsBigO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨c, hc⟩ := h₁.IsBigOWith
  let ⟨c', hc'⟩ := h₂.IsBigOWith
  (hc.mul hc').IsBigO
#align asymptotics.is_O.mul Asymptotics.IsBigO.mul
-/

#print Asymptotics.IsBigO.mul_isLittleO /-
theorem IsBigO.mul_isLittleO {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  by
  unfold is_o at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gt c'pos))
#align asymptotics.is_O.mul_is_o Asymptotics.IsBigO.mul_isLittleO
-/

#print Asymptotics.IsLittleO.mul_isBigO /-
theorem IsLittleO.mul_isBigO {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  by
  unfold is_o at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gt c'pos))
#align asymptotics.is_o.mul_is_O Asymptotics.IsLittleO.mul_isBigO
-/

#print Asymptotics.IsLittleO.mul /-
theorem IsLittleO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  h₁.mul_isBigO h₂.IsBigO
#align asymptotics.is_o.mul Asymptotics.IsLittleO.mul
-/

#print Asymptotics.IsBigOWith.pow' /-
theorem IsBigOWith.pow' {f : α → R} {g : α → 𝕜} (h : IsBigOWith c l f g) :
    ∀ n : ℕ,
      IsBigOWith (Nat.casesOn n ‖(1 : R)‖ fun n => c ^ (n + 1)) l (fun x => f x ^ n) fun x =>
        g x ^ n
  | 0 => by simpa using is_O_with_const_const (1 : R) (one_ne_zero' 𝕜) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using h.mul (is_O_with.pow' (n + 1))
#align asymptotics.is_O_with.pow' Asymptotics.IsBigOWith.pow'
-/

#print Asymptotics.IsBigOWith.pow /-
theorem IsBigOWith.pow [NormOneClass R] {f : α → R} {g : α → 𝕜} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)
#align asymptotics.is_O_with.pow Asymptotics.IsBigOWith.pow
-/

#print Asymptotics.IsBigOWith.of_pow /-
theorem IsBigOWith.of_pow {n : ℕ} {f : α → 𝕜} {g : α → R} (h : IsBigOWith c l (f ^ n) (g ^ n))
    (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') : IsBigOWith c' l f g :=
  IsBigOWith.of_bound <|
    (h.weaken hc).bound.mono fun x hx =>
      le_of_pow_le_pow n (mul_nonneg hc' <| norm_nonneg _) hn.bot_lt <|
        calc
          ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
          _ ≤ c' ^ n * ‖g x ^ n‖ := hx
          _ ≤ c' ^ n * ‖g x‖ ^ n :=
            (mul_le_mul_of_nonneg_left (norm_pow_le' _ hn.bot_lt) (pow_nonneg hc' _))
          _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm
#align asymptotics.is_O_with.of_pow Asymptotics.IsBigOWith.of_pow
-/

#print Asymptotics.IsBigO.pow /-
theorem IsBigO.pow {f : α → R} {g : α → 𝕜} (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨C, hC⟩ := h.IsBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩
#align asymptotics.is_O.pow Asymptotics.IsBigO.pow
-/

#print Asymptotics.IsBigO.of_pow /-
theorem IsBigO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) =O[l] (g ^ n)) :
    f =O[l] g := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ C ≤ c ^ n
  exact ((eventually_ge_at_top _).And <| (tendsto_pow_at_top hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).IsBigO
#align asymptotics.is_O.of_pow Asymptotics.IsBigO.of_pow
-/

#print Asymptotics.IsLittleO.pow /-
theorem IsLittleO.pow {f : α → R} {g : α → 𝕜} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n :=
  by
  cases n; exact hn.false.elim; clear hn
  induction' n with n ihn; · simpa only [pow_one]
  convert h.mul ihn <;> simp [pow_succ]
#align asymptotics.is_o.pow Asymptotics.IsLittleO.pow
-/

#print Asymptotics.IsLittleO.of_pow /-
theorem IsLittleO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) :
    f =o[l] g :=
  IsLittleO.of_isBigOWith fun c hc => (h.def' <| pow_pos hc _).ofPow hn le_rfl hc.le
#align asymptotics.is_o.of_pow Asymptotics.IsLittleO.of_pow
-/

/-! ### Inverse -/


#print Asymptotics.IsBigOWith.inv_rev /-
theorem IsBigOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsBigOWith c l f g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : IsBigOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ :=
  by
  refine' is_O_with.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => _))
  cases' eq_or_ne (f x) 0 with hx hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, MulZeroClass.mul_zero]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_le_inv_of_le (norm_pos_iff.2 hx) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff hc] using hle
#align asymptotics.is_O_with.inv_rev Asymptotics.IsBigOWith.inv_rev
-/

#print Asymptotics.IsBigO.inv_rev /-
theorem IsBigO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨c, hc⟩ := h.IsBigOWith
  (hc.inv_rev h₀).IsBigO
#align asymptotics.is_O.inv_rev Asymptotics.IsBigO.inv_rev
-/

#print Asymptotics.IsLittleO.inv_rev /-
theorem IsLittleO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  IsLittleO.of_isBigOWith fun c hc => (h.def' hc).inv_rev h₀
#align asymptotics.is_o.inv_rev Asymptotics.IsLittleO.inv_rev
-/

/-! ### Scalar multiplication -/


section SmulConst

variable [NormedSpace 𝕜 E']

#print Asymptotics.IsBigOWith.const_smul_left /-
theorem IsBigOWith.const_smul_left (h : IsBigOWith c l f' g) (c' : 𝕜) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' • f' x) g :=
  IsBigOWith.of_norm_left <| by
    simpa only [← norm_smul, norm_norm] using h.norm_left.const_mul_left ‖c'‖
#align asymptotics.is_O_with.const_smul_left Asymptotics.IsBigOWith.const_smul_left
-/

#print Asymptotics.IsBigO.const_smul_left /-
theorem IsBigO.const_smul_left (h : f' =O[l] g) (c : 𝕜) : (c • f') =O[l] g :=
  let ⟨b, hb⟩ := h.IsBigOWith
  (hb.const_smul_left _).IsBigO
#align asymptotics.is_O.const_smul_left Asymptotics.IsBigO.const_smul_left
-/

#print Asymptotics.IsLittleO.const_smul_left /-
theorem IsLittleO.const_smul_left (h : f' =o[l] g) (c : 𝕜) : (c • f') =o[l] g :=
  IsLittleO.of_norm_left <| by simpa only [← norm_smul] using h.norm_left.const_mul_left ‖c‖
#align asymptotics.is_o.const_smul_left Asymptotics.IsLittleO.const_smul_left
-/

#print Asymptotics.isBigO_const_smul_left /-
theorem isBigO_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_left]; simp only [norm_smul]
  rw [is_O_const_mul_left_iff cne0, is_O_norm_left]
#align asymptotics.is_O_const_smul_left Asymptotics.isBigO_const_smul_left
-/

#print Asymptotics.isLittleO_const_smul_left /-
theorem isLittleO_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =o[l] g ↔ f' =o[l] g :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_left]; simp only [norm_smul]
  rw [is_o_const_mul_left_iff cne0, is_o_norm_left]
#align asymptotics.is_o_const_smul_left Asymptotics.isLittleO_const_smul_left
-/

#print Asymptotics.isBigO_const_smul_right /-
theorem isBigO_const_smul_right {c : 𝕜} (hc : c ≠ 0) : (f =O[l] fun x => c • f' x) ↔ f =O[l] f' :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_right]; simp only [norm_smul]
  rw [is_O_const_mul_right_iff cne0, is_O_norm_right]
#align asymptotics.is_O_const_smul_right Asymptotics.isBigO_const_smul_right
-/

#print Asymptotics.isLittleO_const_smul_right /-
theorem isLittleO_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c • f' x) ↔ f =o[l] f' :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_right]; simp only [norm_smul]
  rw [is_o_const_mul_right_iff cne0, is_o_norm_right]
#align asymptotics.is_o_const_smul_right Asymptotics.isLittleO_const_smul_right
-/

end SmulConst

section Smul

variable [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜'}

#print Asymptotics.IsBigOWith.smul /-
theorem IsBigOWith.smul (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g') :
    IsBigOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O_with.smul Asymptotics.IsBigOWith.smul
-/

#print Asymptotics.IsBigO.smul /-
theorem IsBigO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O.smul Asymptotics.IsBigO.smul
-/

#print Asymptotics.IsBigO.smul_isLittleO /-
theorem IsBigO.smul_isLittleO (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is_o h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O.smul_is_o Asymptotics.IsBigO.smul_isLittleO
-/

#print Asymptotics.IsLittleO.smul_isBigO /-
theorem IsLittleO.smul_isBigO (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is_O h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_o.smul_is_O Asymptotics.IsLittleO.smul_isBigO
-/

#print Asymptotics.IsLittleO.smul /-
theorem IsLittleO.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_o.smul Asymptotics.IsLittleO.smul
-/

end Smul

/-! ### Sum -/


section Sum

variable {ι : Type _} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

#print Asymptotics.IsBigOWith.sum /-
theorem IsBigOWith.sum (h : ∀ i ∈ s, IsBigOWith (C i) l (A i) g) :
    IsBigOWith (∑ i in s, C i) l (fun x => ∑ i in s, A i x) g :=
  by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_O_with_zero', Finset.sum_empty, forall_true_iff]
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align asymptotics.is_O_with.sum Asymptotics.IsBigOWith.sum
-/

#print Asymptotics.IsBigO.sum /-
theorem IsBigO.sum (h : ∀ i ∈ s, A i =O[l] g) : (fun x => ∑ i in s, A i x) =O[l] g :=
  by
  unfold is_O at *
  choose! C hC using h
  exact ⟨_, is_O_with.sum hC⟩
#align asymptotics.is_O.sum Asymptotics.IsBigO.sum
-/

#print Asymptotics.IsLittleO.sum /-
theorem IsLittleO.sum (h : ∀ i ∈ s, A i =o[l] g') : (fun x => ∑ i in s, A i x) =o[l] g' :=
  by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_o_zero, Finset.sum_empty, forall_true_iff]
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align asymptotics.is_o.sum Asymptotics.IsLittleO.sum
-/

end Sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/


#print Asymptotics.IsLittleO.tendsto_div_nhds_zero /-
theorem IsLittleO.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (isLittleO_one_iff 𝕜).mp <|
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_is_O (is_O_refl _ _)
      _ =O[l] fun x => (1 : 𝕜) := isBigO_of_le _ fun x => by simp [div_self_le_one]
#align asymptotics.is_o.tendsto_div_nhds_zero Asymptotics.IsLittleO.tendsto_div_nhds_zero
-/

#print Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero /-
theorem IsLittleO.tendsto_inv_smul_nhds_zero [NormedSpace 𝕜 E'] {f : α → E'} {g : α → 𝕜}
    {l : Filter α} (h : f =o[l] g) : Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero
#align asymptotics.is_o.tendsto_inv_smul_nhds_zero Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero
-/

#print Asymptotics.isLittleO_iff_tendsto' /-
theorem isLittleO_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨IsLittleO.tendsto_div_nhds_zero, fun h =>
    (((isLittleO_one_iff _).mpr h).mul_isBigO (isBigO_refl g l)).congr'
      (hgf.mono fun x => div_mul_cancel_of_imp) (eventually_of_forall fun x => one_mul _)⟩
#align asymptotics.is_o_iff_tendsto' Asymptotics.isLittleO_iff_tendsto'
-/

#print Asymptotics.isLittleO_iff_tendsto /-
theorem isLittleO_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  isLittleO_iff_tendsto' (eventually_of_forall hgf)
#align asymptotics.is_o_iff_tendsto Asymptotics.isLittleO_iff_tendsto
-/

alias is_o_iff_tendsto' ↔ _ is_o_of_tendsto'
#align asymptotics.is_o_of_tendsto' Asymptotics.isLittleO_of_tendsto'

alias is_o_iff_tendsto ↔ _ is_o_of_tendsto
#align asymptotics.is_o_of_tendsto Asymptotics.isLittleO_of_tendsto

#print Asymptotics.isLittleO_const_left_of_ne /-
theorem isLittleO_const_left_of_ne {c : E''} (hc : c ≠ 0) :
    (fun x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop :=
  by
  simp only [← is_o_one_left_iff ℝ]
  exact ⟨(is_O_const_const (1 : ℝ) hc l).trans_isLittleO, (is_O_const_one ℝ c l).trans_isLittleO⟩
#align asymptotics.is_o_const_left_of_ne Asymptotics.isLittleO_const_left_of_ne
-/

#print Asymptotics.isLittleO_const_left /-
@[simp]
theorem isLittleO_const_left {c : E''} :
    (fun x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop :=
  by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [is_o_zero, eq_self_iff_true, true_or_iff]
  · simp only [hc, false_or_iff, is_o_const_left_of_ne hc]
#align asymptotics.is_o_const_left Asymptotics.isLittleO_const_left
-/

#print Asymptotics.isLittleO_const_const_iff /-
@[simp]
theorem isLittleO_const_const_iff [NeBot l] {d : E''} {c : F''} :
    ((fun x => d) =o[l] fun x => c) ↔ d = 0 :=
  by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp [Function.const, this]
#align asymptotics.is_o_const_const_iff Asymptotics.isLittleO_const_const_iff
-/

#print Asymptotics.isLittleO_pure /-
@[simp]
theorem isLittleO_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun y : α => f'' x) =o[pure x] fun _ => g'' x := isLittleO_congr rfl rfl
    _ ↔ f'' x = 0 := isLittleO_const_const_iff
#align asymptotics.is_o_pure Asymptotics.isLittleO_pure
-/

#print Asymptotics.isLittleO_const_id_comap_norm_atTop /-
theorem isLittleO_const_id_comap_norm_atTop (c : F'') :
    (fun x : E'' => c) =o[comap norm atTop] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_comap
#align asymptotics.is_o_const_id_comap_norm_at_top Asymptotics.isLittleO_const_id_comap_norm_atTop
-/

#print Asymptotics.isLittleO_const_id_atTop /-
theorem isLittleO_const_id_atTop (c : E'') : (fun x : ℝ => c) =o[atTop] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop
#align asymptotics.is_o_const_id_at_top Asymptotics.isLittleO_const_id_atTop
-/

#print Asymptotics.isLittleO_const_id_atBot /-
theorem isLittleO_const_id_atBot (c : E'') : (fun x : ℝ => c) =o[atBot] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atBot_atTop
#align asymptotics.is_o_const_id_at_bot Asymptotics.isLittleO_const_id_atBot
-/

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/


section EventuallyMulDivCancel

variable {u v : α → 𝕜}

#print Asymptotics.IsBigOWith.eventually_mul_div_cancel /-
theorem IsBigOWith.eventually_mul_div_cancel (h : IsBigOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy
#align asymptotics.is_O_with.eventually_mul_div_cancel Asymptotics.IsBigOWith.eventually_mul_div_cancel
-/

#print Asymptotics.IsBigO.eventually_mul_div_cancel /-
/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsBigO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨c, hc⟩ := h.IsBigOWith
  hc.eventually_mul_div_cancel
#align asymptotics.is_O.eventually_mul_div_cancel Asymptotics.IsBigO.eventually_mul_div_cancel
-/

#print Asymptotics.IsLittleO.eventually_mul_div_cancel /-
/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsLittleO.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel
#align asymptotics.is_o.eventually_mul_div_cancel Asymptotics.IsLittleO.eventually_mul_div_cancel
-/

end EventuallyMulDivCancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/


section ExistsMulEq

variable {u v : α → 𝕜}

#print Asymptotics.isBigOWith_of_eq_mul /-
/-- If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
theorem isBigOWith_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c) (h : u =ᶠ[l] φ * v) :
    IsBigOWith c l u v := by
  unfold is_O_with
  refine' h.symm.rw (fun x a => ‖a‖ ≤ c * ‖v x‖) (hφ.mono fun x hx => _)
  simp only [norm_mul, Pi.mul_apply]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
#align asymptotics.is_O_with_of_eq_mul Asymptotics.isBigOWith_of_eq_mul
-/

#print Asymptotics.isBigOWith_iff_exists_eq_mul /-
theorem isBigOWith_iff_exists_eq_mul (hc : 0 ≤ c) :
    IsBigOWith c l u v ↔ ∃ (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
  by
  constructor
  · intro h
    use fun x => u x / v x
    refine' ⟨eventually.mono h.bound fun y hy => _, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact is_O_with_of_eq_mul φ hφ h
#align asymptotics.is_O_with_iff_exists_eq_mul Asymptotics.isBigOWith_iff_exists_eq_mul
-/

#print Asymptotics.IsBigOWith.exists_eq_mul /-
theorem IsBigOWith.exists_eq_mul (h : IsBigOWith c l u v) (hc : 0 ≤ c) :
    ∃ (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
  (isBigOWith_iff_exists_eq_mul hc).mp h
#align asymptotics.is_O_with.exists_eq_mul Asymptotics.IsBigOWith.exists_eq_mul
-/

#print Asymptotics.isBigO_iff_exists_eq_mul /-
theorem isBigO_iff_exists_eq_mul :
    u =O[l] v ↔ ∃ (φ : α → 𝕜) (hφ : l.IsBoundedUnder (· ≤ ·) (norm ∘ φ)), u =ᶠ[l] φ * v :=
  by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact is_O_iff_is_O_with.2 ⟨c, is_O_with_of_eq_mul φ hφ huvφ⟩
#align asymptotics.is_O_iff_exists_eq_mul Asymptotics.isBigO_iff_exists_eq_mul
-/

alias is_O_iff_exists_eq_mul ↔ is_O.exists_eq_mul _
#align asymptotics.is_O.exists_eq_mul Asymptotics.IsBigO.exists_eq_mul

#print Asymptotics.isLittleO_iff_exists_eq_mul /-
theorem isLittleO_iff_exists_eq_mul :
    u =o[l] v ↔ ∃ (φ : α → 𝕜) (hφ : Tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v :=
  by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · unfold is_o; rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hφ 
    exact is_O_with_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ
#align asymptotics.is_o_iff_exists_eq_mul Asymptotics.isLittleO_iff_exists_eq_mul
-/

alias is_o_iff_exists_eq_mul ↔ is_o.exists_eq_mul _
#align asymptotics.is_o.exists_eq_mul Asymptotics.IsLittleO.exists_eq_mul

end ExistsMulEq

/-! ### Miscellanous lemmas -/


#print Asymptotics.div_isBoundedUnder_of_isBigO /-
theorem div_isBoundedUnder_of_isBigO {α : Type _} {l : Filter α} {f g : α → 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ :=
  by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine' ⟨c, eventually_map.2 (hc.bound.mono fun x hx => _)⟩
  rw [norm_div]
  exact div_le_of_nonneg_of_le_mul (norm_nonneg _) h₀ hx
#align asymptotics.div_is_bounded_under_of_is_O Asymptotics.div_isBoundedUnder_of_isBigO
-/

#print Asymptotics.isBigO_iff_div_isBoundedUnder /-
theorem isBigO_iff_div_isBoundedUnder {α : Type _} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ :=
  by
  refine' ⟨div_is_bounded_under_of_is_O, fun h => _⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc 
  refine' is_O.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => _)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff (norm_pos_iff.2 hgx)).mp hx₂
#align asymptotics.is_O_iff_div_is_bounded_under Asymptotics.isBigO_iff_div_isBoundedUnder
-/

#print Asymptotics.isBigO_of_div_tendsto_nhds /-
theorem isBigO_of_div_tendsto_nhds {α : Type _} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c)) : f =O[l] g :=
  (isBigO_iff_div_isBoundedUnder hgf).2 <| H.norm.isBoundedUnder_le
#align asymptotics.is_O_of_div_tendsto_nhds Asymptotics.isBigO_of_div_tendsto_nhds
-/

#print Asymptotics.IsLittleO.tendsto_zero_of_tendsto /-
theorem IsLittleO.tendsto_zero_of_tendsto {α E 𝕜 : Type _} [NormedAddCommGroup E] [NormedField 𝕜]
    {u : α → E} {v : α → 𝕜} {l : Filter α} {y : 𝕜} (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) :
    Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun x => (1 : 𝕜)
  · rwa [is_o_one_iff] at h 
  exact huv.trans_is_O (hv.is_O_one 𝕜)
#align asymptotics.is_o.tendsto_zero_of_tendsto Asymptotics.IsLittleO.tendsto_zero_of_tendsto
-/

#print Asymptotics.isLittleO_pow_pow /-
theorem isLittleO_pow_pow {m n : ℕ} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m :=
  by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact is_O.mul_is_o (is_O_refl _ _) (is_o.pow ((is_o_one_iff _).2 tendsto_id) hp0)
#align asymptotics.is_o_pow_pow Asymptotics.isLittleO_pow_pow
-/

#print Asymptotics.isLittleO_norm_pow_norm_pow /-
theorem isLittleO_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m :=
  (isLittleO_pow_pow h).comp_tendsto tendsto_norm_zero
#align asymptotics.is_o_norm_pow_norm_pow Asymptotics.isLittleO_norm_pow_norm_pow
-/

#print Asymptotics.isLittleO_pow_id /-
theorem isLittleO_pow_id {n : ℕ} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x := by
  convert is_o_pow_pow h; simp only [pow_one]
#align asymptotics.is_o_pow_id Asymptotics.isLittleO_pow_id
-/

#print Asymptotics.isLittleO_norm_pow_id /-
theorem isLittleO_norm_pow_id {n : ℕ} (h : 1 < n) : (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x := by
  simpa only [pow_one, is_o_norm_right] using @is_o_norm_pow_norm_pow E' _ _ _ h
#align asymptotics.is_o_norm_pow_id Asymptotics.isLittleO_norm_pow_id
-/

#print Asymptotics.IsBigO.eq_zero_of_norm_pow_within /-
theorem IsBigO.eq_zero_of_norm_pow_within {f : E'' → F''} {s : Set E''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 0 < n) : f x₀ = 0 :=
  mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp <| by simp_rw [sub_self, norm_zero, zero_pow hn]
#align asymptotics.is_O.eq_zero_of_norm_pow_within Asymptotics.IsBigO.eq_zero_of_norm_pow_within
-/

#print Asymptotics.IsBigO.eq_zero_of_norm_pow /-
theorem IsBigO.eq_zero_of_norm_pow {f : E'' → F''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n) (hn : 0 < n) : f x₀ = 0 := by
  rw [← nhdsWithin_univ] at h ; exact h.eq_zero_of_norm_pow_within (mem_univ _) hn
#align asymptotics.is_O.eq_zero_of_norm_pow Asymptotics.IsBigO.eq_zero_of_norm_pow
-/

#print Asymptotics.isLittleO_pow_sub_pow_sub /-
theorem isLittleO_pow_sub_pow_sub (x₀ : E') {n m : ℕ} (h : n < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n :=
  haveI : tendsto (fun x => ‖x - x₀‖) (𝓝 x₀) (𝓝 0) :=
    by
    apply tendsto_norm_zero.comp
    rw [← sub_self x₀]
    exact tendsto_id.sub tendsto_const_nhds
  (is_o_pow_pow h).comp_tendsto this
#align asymptotics.is_o_pow_sub_pow_sub Asymptotics.isLittleO_pow_sub_pow_sub
-/

#print Asymptotics.isLittleO_pow_sub_sub /-
theorem isLittleO_pow_sub_sub (x₀ : E') {m : ℕ} (h : 1 < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀ := by
  simpa only [is_o_norm_right, pow_one] using is_o_pow_sub_pow_sub x₀ h
#align asymptotics.is_o_pow_sub_sub Asymptotics.isLittleO_pow_sub_sub
-/

#print Asymptotics.IsBigOWith.right_le_sub_of_lt_1 /-
theorem IsBigOWith.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      by
      simp only [mem_set_of_eq] at hx ⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff, mul_sub, mul_one, mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · exact sub_pos.2 hc
#align asymptotics.is_O_with.right_le_sub_of_lt_1 Asymptotics.IsBigOWith.right_le_sub_of_lt_1
-/

#print Asymptotics.IsBigOWith.right_le_add_of_lt_1 /-
theorem IsBigOWith.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (fun x => rfl) fun x => by
    rw [neg_sub, sub_neg_eq_add]
#align asymptotics.is_O_with.right_le_add_of_lt_1 Asymptotics.IsBigOWith.right_le_add_of_lt_1
-/

#print Asymptotics.IsLittleO.right_isBigO_sub /-
theorem IsLittleO.right_isBigO_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).IsBigO
#align asymptotics.is_o.right_is_O_sub Asymptotics.IsLittleO.right_isBigO_sub
-/

#print Asymptotics.IsLittleO.right_isBigO_add /-
theorem IsLittleO.right_isBigO_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).IsBigO
#align asymptotics.is_o.right_is_O_add Asymptotics.IsLittleO.right_isBigO_add
-/

#print Asymptotics.bound_of_isBigO_cofinite /-
/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`. -/
theorem bound_of_isBigO_cofinite (h : f =O[cofinite] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [is_O_with, eventually_cofinite] at hC 
  rcases(hC.to_finset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : ∀ x, C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ / ‖g'' x‖ ≤ C' := by simpa using hC'
  refine' ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => _⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le]
  exact fun hx => (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)
#align asymptotics.bound_of_is_O_cofinite Asymptotics.bound_of_isBigO_cofinite
-/

#print Asymptotics.isBigO_cofinite_iff /-
theorem isBigO_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) :
    f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ‖f'' x‖ ≤ C * ‖g'' x‖ :=
  ⟨fun h' =>
    let ⟨C, C₀, hC⟩ := bound_of_isBigO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (isBigO_top.2 h).mono le_top⟩
#align asymptotics.is_O_cofinite_iff Asymptotics.isBigO_cofinite_iff
-/

#print Asymptotics.bound_of_isBigO_nat_atTop /-
theorem bound_of_isBigO_nat_atTop {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[atTop] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  bound_of_isBigO_cofinite <| by rwa [Nat.cofinite_eq_atTop]
#align asymptotics.bound_of_is_O_nat_at_top Asymptotics.bound_of_isBigO_nat_atTop
-/

#print Asymptotics.isBigO_nat_atTop_iff /-
theorem isBigO_nat_atTop_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    f =O[atTop] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  rw [← Nat.cofinite_eq_atTop, is_O_cofinite_iff h]
#align asymptotics.is_O_nat_at_top_iff Asymptotics.isBigO_nat_atTop_iff
-/

#print Asymptotics.isBigO_one_nat_atTop_iff /-
theorem isBigO_one_nat_atTop_iff {f : ℕ → E''} :
    f =O[atTop] (fun n => 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ‖f n‖ ≤ C :=
  Iff.trans (isBigO_nat_atTop_iff fun n h => (one_ne_zero h).elim) <| by
    simp only [norm_one, mul_one]
#align asymptotics.is_O_one_nat_at_top_iff Asymptotics.isBigO_one_nat_atTop_iff
-/

#print Asymptotics.isBigOWith_pi /-
theorem isBigOWith_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} {C : ℝ} (hC : 0 ≤ C) :
    IsBigOWith C l f g' ↔ ∀ i, IsBigOWith C l (fun x => f x i) g' :=
  by
  have : ∀ x, 0 ≤ C * ‖g' x‖ := fun x => mul_nonneg hC (norm_nonneg _)
  simp only [is_O_with_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]
#align asymptotics.is_O_with_pi Asymptotics.isBigOWith_pi
-/

#print Asymptotics.isBigO_pi /-
@[simp]
theorem isBigO_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =O[l] g' ↔ ∀ i, (fun x => f x i) =O[l] g' :=
  by
  simp only [is_O_iff_eventually_is_O_with, ← eventually_all]
  exact eventually_congr (eventually_at_top.2 ⟨0, fun c => is_O_with_pi⟩)
#align asymptotics.is_O_pi Asymptotics.isBigO_pi
-/

#print Asymptotics.isLittleO_pi /-
@[simp]
theorem isLittleO_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =o[l] g' ↔ ∀ i, (fun x => f x i) =o[l] g' :=
  by
  simp (config := { contextual := true }) only [is_o, is_O_with_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩
#align asymptotics.is_o_pi Asymptotics.isLittleO_pi
-/

end Asymptotics

open Asymptotics

#print summable_of_isBigO /-
theorem summable_of_isBigO {ι E} [NormedAddCommGroup E] [CompleteSpace E] {f : ι → E} {g : ι → ℝ}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  let ⟨C, hC⟩ := h.IsBigOWith
  summable_of_norm_bounded_eventually (fun x => C * ‖g x‖) (hg.abs.mul_left _) hC.bound
#align summable_of_is_O summable_of_isBigO
-/

#print summable_of_isBigO_nat /-
theorem summable_of_isBigO_nat {E} [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → E} {g : ℕ → ℝ}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO hg <| Nat.cofinite_eq_atTop.symm ▸ h
#align summable_of_is_O_nat summable_of_isBigO_nat
-/

namespace LocalHomeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [Norm E] {F : Type _} [Norm F]

#print LocalHomeomorph.isBigOWith_congr /-
/-- Transfer `is_O_with` over a `local_homeomorph`. -/
theorem isBigOWith_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} {C : ℝ} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
    h.comp_tendsto <| by convert e.continuous_at (e.map_target hb); exact (e.right_inv hb).symm,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg g hx)⟩
#align local_homeomorph.is_O_with_congr LocalHomeomorph.isBigOWith_congr
-/

#print LocalHomeomorph.isBigO_congr /-
/-- Transfer `is_O` over a `local_homeomorph`. -/
theorem isBigO_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by unfold is_O;
  exact exists_congr fun C => e.is_O_with_congr hb
#align local_homeomorph.is_O_congr LocalHomeomorph.isBigO_congr
-/

#print LocalHomeomorph.isLittleO_congr /-
/-- Transfer `is_o` over a `local_homeomorph`. -/
theorem isLittleO_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} : f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by unfold is_o;
  exact forall₂_congr fun c hc => e.is_O_with_congr hb
#align local_homeomorph.is_o_congr LocalHomeomorph.isLittleO_congr
-/

end LocalHomeomorph

namespace Homeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [Norm E] {F : Type _} [Norm F]

open Asymptotics

#print Homeomorph.isBigOWith_congr /-
/-- Transfer `is_O_with` over a `homeomorph`. -/
theorem isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toLocalHomeomorph.isBigOWith_congr trivial
#align homeomorph.is_O_with_congr Homeomorph.isBigOWith_congr
-/

#print Homeomorph.isBigO_congr /-
/-- Transfer `is_O` over a `homeomorph`. -/
theorem isBigO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by unfold is_O;
  exact exists_congr fun C => e.is_O_with_congr
#align homeomorph.is_O_congr Homeomorph.isBigO_congr
-/

#print Homeomorph.isLittleO_congr /-
/-- Transfer `is_o` over a `homeomorph`. -/
theorem isLittleO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by unfold is_o;
  exact forall₂_congr fun c hc => e.is_O_with_congr
#align homeomorph.is_o_congr Homeomorph.isLittleO_congr
-/

end Homeomorph

