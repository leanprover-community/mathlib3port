/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Topology.Algebra.Order.LiminfLimsup
import Mathbin.Topology.LocalHomeomorph

/-!
# Asymptotics

We introduce these relations:

* `is_O_with c f g l` : "f is big O of g along l with constant c";
* `is_O f g l` : "f is big O of g along l";
* `is_o f g l` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

The relation `is_O_with c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `is_O` and `is_o`. Usually proofs outside of this file should use `is_O`
instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `is_O f g l ↔ is_O (λ x, ∥f x∥) (λ x, ∥g x∥) l`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `is_o f g l ↔ tendsto (λ x, f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/


open Filter Set

open TopologicalSpace BigOperators Classical Filter Nnreal

namespace Asymptotics

variable {α : Type _} {β : Type _} {E : Type _} {F : Type _} {G : Type _} {E' : Type _} {F' : Type _} {G' : Type _}
  {E'' : Type _} {F'' : Type _} {G'' : Type _} {R : Type _} {R' : Type _} {𝕜 : Type _} {𝕜' : Type _}

variable [HasNorm E] [HasNorm F] [HasNorm G]

variable [SemiNormedGroup E'] [SemiNormedGroup F'] [SemiNormedGroup G']

variable [NormedGroup E''] [NormedGroup F''] [NormedGroup G'']

variable [SemiNormedRing R] [SemiNormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']

variable {c c' : ℝ} {f : α → E} {g : α → F} {k : α → G}

variable {f' : α → E'} {g' : α → F'} {k' : α → G'}

variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}

variable {l l' : Filter α}

section Defs

/-! ### Definitions -/


/-- This version of the Landau notation `is_O_with C f g l` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by `C * ∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `is_O` instead of this relation. -/
irreducible_def IsOWith (c : ℝ) (f : α → E) (g : α → F) (l : Filter α) : Prop :=
  ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥

/-- Definition of `is_O_with`. We record it in a lemma as we will set `is_O_with` to be irreducible
at the end of this file. -/
theorem is_O_with_iff {c : ℝ} {f : α → E} {g : α → F} {l : Filter α} : IsOWith c f g l ↔ ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ :=
  by
  rw [is_O_with]

alias is_O_with_iff ↔ Asymptotics.IsOWith.bound Asymptotics.IsOWith.of_bound

/-- The Landau notation `is_O f g l` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by a constant multiple of `∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsO (f : α → E) (g : α → F) (l : Filter α) : Prop :=
  ∃ c : ℝ, IsOWith c f g l

/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem is_O_iff_is_O_with {f : α → E} {g : α → F} {l : Filter α} : IsO f g l ↔ ∃ c : ℝ, IsOWith c f g l := by
  rw [is_O]

/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem is_O_iff {f : α → E} {g : α → F} {l : Filter α} : IsO f g l ↔ ∃ c : ℝ, ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ := by
  simp [is_O, is_O_with]

theorem IsO.of_bound (c : ℝ) {f : α → E} {g : α → F} {l : Filter α} (h : ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥) : IsO f g l :=
  is_O_iff.2 ⟨c, h⟩

theorem IsO.bound {f : α → E} {g : α → F} {l : Filter α} : IsO f g l → ∃ c : ℝ, ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ :=
  is_O_iff.1

/-- The Landau notation `is_o f g l` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by an arbitrarily small constant
multiple of `∥g∥`. In other words, `∥f∥ / ∥g∥` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsOₓ (f : α → E) (g : α → F) (l : Filter α) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsOWith c f g l

/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem is_o_iff_forall_is_O_with {f : α → E} {g : α → F} {l : Filter α} :
    IsOₓ f g l ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsOWith c f g l := by
  rw [is_o]

alias is_o_iff_forall_is_O_with ↔ Asymptotics.IsOₓ.forall_is_O_with Asymptotics.IsOₓ.of_is_O_with

/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem is_o_iff {f : α → E} {g : α → F} {l : Filter α} :
    IsOₓ f g l ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ := by
  simp only [is_o, is_O_with]

alias is_o_iff ↔ Asymptotics.IsOₓ.bound Asymptotics.IsOₓ.of_bound

theorem IsOₓ.def {f : α → E} {g : α → F} {l : Filter α} (h : IsOₓ f g l) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ :=
  is_o_iff.1 h hc

theorem IsOₓ.def' {f : α → E} {g : α → F} {l : Filter α} (h : IsOₓ f g l) {c : ℝ} (hc : 0 < c) : IsOWith c f g l :=
  is_O_with_iff.2 <| is_o_iff.1 h hc

end Defs

/-! ### Conversions -/


theorem IsOWith.is_O (h : IsOWith c f g l) : IsO f g l := by
  rw [is_O] <;> exact ⟨c, h⟩

theorem IsOₓ.is_O_with (hgf : IsOₓ f g l) : IsOWith 1 f g l :=
  hgf.def' zero_lt_one

theorem IsOₓ.is_O (hgf : IsOₓ f g l) : IsO f g l :=
  hgf.IsOWith.IsO

theorem IsO.is_O_with {f : α → E} {g : α → F} {l : Filter α} : IsO f g l → ∃ c : ℝ, IsOWith c f g l :=
  is_O_iff_is_O_with.1

theorem IsOWith.weaken (h : IsOWith c f g' l) (hc : c ≤ c') : IsOWith c' f g' l :=
  is_O_with.of_bound <|
    (mem_of_superset h.bound) fun x hx =>
      calc
        ∥f x∥ ≤ c * ∥g' x∥ := hx
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        

theorem IsOWith.exists_pos (h : IsOWith c f g' l) : ∃ (c' : _)(H : 0 < c'), IsOWith c' f g' l :=
  ⟨max c 1, lt_of_lt_of_leₓ zero_lt_one (le_max_rightₓ c 1), h.weaken <| le_max_leftₓ c 1⟩

theorem IsO.exists_pos (h : IsO f g' l) : ∃ (c : _)(H : 0 < c), IsOWith c f g' l :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.exists_pos

theorem IsOWith.exists_nonneg (h : IsOWith c f g' l) : ∃ (c' : _)(H : 0 ≤ c'), IsOWith c' f g' l :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_ltₓ cpos, hc⟩

theorem IsO.exists_nonneg (h : IsO f g' l) : ∃ (c : _)(H : 0 ≤ c), IsOWith c f g' l :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.exists_nonneg

/-- `f = O(g)` if and only if `is_O_with c f g` for all sufficiently large `c`. -/
theorem is_O_iff_eventually_is_O_with : IsO f g' l ↔ ∀ᶠ c in at_top, IsOWith c f g' l :=
  is_O_iff_is_O_with.trans ⟨fun ⟨c, hc⟩ => mem_at_top_sets.2 ⟨c, fun c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩

/-- `f = O(g)` if and only if `∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥` for all sufficiently large `c`. -/
theorem is_O_iff_eventually : IsO f g' l ↔ ∀ᶠ c in at_top, ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g' x∥ :=
  is_O_iff_eventually_is_O_with.trans <| by
    simp only [is_O_with]

theorem IsO.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : IsO f g' l) (hb : l.HasBasis p s) :
    ∃ (c : ℝ)(hc : 0 < c)(i : ι)(hi : p i), ∀, ∀ x ∈ s i, ∀, ∥f x∥ ≤ c * ∥g' x∥ :=
  (flip Exists₂.imp h.exists_pos) fun c hc h => by
    simpa only [is_O_with_iff, hb.eventually_iff, exists_prop] using h

/-! ### Subsingleton -/


@[nontriviality]
theorem is_o_of_subsingleton [Subsingleton E'] : IsOₓ f' g' l :=
  is_o.of_bound fun c hc => by
    simp [Subsingleton.elimₓ (f' _) 0, mul_nonneg hc.le]

@[nontriviality]
theorem is_O_of_subsingleton [Subsingleton E'] : IsO f' g' l :=
  is_o_of_subsingleton.IsO

/-! ### Congruence -/


theorem is_O_with_congr {c₁ c₂} {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsOWith c₁ f₁ g₁ l ↔ IsOWith c₂ f₂ g₂ l := by
  unfold is_O_with
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁, e₂]

theorem IsOWith.congr' {c₁ c₂} {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsOWith c₁ f₁ g₁ l → IsOWith c₂ f₂ g₂ l :=
  (is_O_with_congr hc hf hg).mp

theorem IsOWith.congr {c₁ c₂} {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
    (hg : ∀ x, g₁ x = g₂ x) : IsOWith c₁ f₁ g₁ l → IsOWith c₂ f₂ g₂ l := fun h =>
  h.congr' hc (univ_mem' hf) (univ_mem' hg)

theorem IsOWith.congr_left {f₁ f₂ : α → E} {l : Filter α} (hf : ∀ x, f₁ x = f₂ x) :
    IsOWith c f₁ g l → IsOWith c f₂ g l :=
  IsOWith.congr rfl hf fun _ => rfl

theorem IsOWith.congr_right {g₁ g₂ : α → F} {l : Filter α} (hg : ∀ x, g₁ x = g₂ x) :
    IsOWith c f g₁ l → IsOWith c f g₂ l :=
  IsOWith.congr rfl (fun _ => rfl) hg

theorem IsOWith.congr_const {c₁ c₂} {l : Filter α} (hc : c₁ = c₂) : IsOWith c₁ f g l → IsOWith c₂ f g l :=
  IsOWith.congr hc (fun _ => rfl) fun _ => rfl

theorem is_O_congr {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsO f₁ g₁ l ↔ IsO f₂ g₂ l := by
  unfold is_O
  exact exists_congr fun c => is_O_with_congr rfl hf hg

theorem IsO.congr' {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsO f₁ g₁ l → IsO f₂ g₂ l :=
  (is_O_congr hf hg).mp

theorem IsO.congr {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    IsO f₁ g₁ l → IsO f₂ g₂ l := fun h => h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsO.congr_left {f₁ f₂ : α → E} {l : Filter α} (hf : ∀ x, f₁ x = f₂ x) : IsO f₁ g l → IsO f₂ g l :=
  IsO.congr hf fun _ => rfl

theorem IsO.congr_right {g₁ g₂ : α → E} {l : Filter α} (hg : ∀ x, g₁ x = g₂ x) : IsO f g₁ l → IsO f g₂ l :=
  IsO.congr (fun _ => rfl) hg

theorem is_o_congr {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsOₓ f₁ g₁ l ↔ IsOₓ f₂ g₂ l := by
  unfold is_o
  exact ball_congr fun c hc => is_O_with_congr (Eq.refl c) hf hg

theorem IsOₓ.congr' {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsOₓ f₁ g₁ l → IsOₓ f₂ g₂ l :=
  (is_o_congr hf hg).mp

theorem IsOₓ.congr {f₁ f₂ : α → E} {g₁ g₂ : α → F} {l : Filter α} (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    IsOₓ f₁ g₁ l → IsOₓ f₂ g₂ l := fun h => h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsOₓ.congr_left {f₁ f₂ : α → E} {l : Filter α} (hf : ∀ x, f₁ x = f₂ x) : IsOₓ f₁ g l → IsOₓ f₂ g l :=
  IsOₓ.congr hf fun _ => rfl

theorem IsOₓ.congr_right {g₁ g₂ : α → E} {l : Filter α} (hg : ∀ x, g₁ x = g₂ x) : IsOₓ f g₁ l → IsOₓ f g₂ l :=
  IsOₓ.congr (fun _ => rfl) hg

/-! ### Filter operations and transitivity -/


theorem IsOWith.comp_tendsto (hcfg : IsOWith c f g l) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    IsOWith c (f ∘ k) (g ∘ k) l' :=
  is_O_with.of_bound <| hk hcfg.bound

theorem IsO.comp_tendsto (hfg : IsO f g l) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) : IsO (f ∘ k) (g ∘ k) l' :=
  is_O_iff_is_O_with.2 <| hfg.IsOWith.imp fun c h => h.comp_tendsto hk

theorem IsOₓ.comp_tendsto (hfg : IsOₓ f g l) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    IsOₓ (f ∘ k) (g ∘ k) l' :=
  is_o.of_is_O_with fun c cpos => (hfg.forall_is_O_with cpos).comp_tendsto hk

@[simp]
theorem is_O_with_map {k : β → α} {l : Filter β} : IsOWith c f g (map k l) ↔ IsOWith c (f ∘ k) (g ∘ k) l := by
  unfold is_O_with
  exact mem_map

@[simp]
theorem is_O_map {k : β → α} {l : Filter β} : IsO f g (map k l) ↔ IsO (f ∘ k) (g ∘ k) l := by
  simp only [is_O, is_O_with_map]

@[simp]
theorem is_o_map {k : β → α} {l : Filter β} : IsOₓ f g (map k l) ↔ IsOₓ (f ∘ k) (g ∘ k) l := by
  simp only [is_o, is_O_with_map]

theorem IsOWith.mono (h : IsOWith c f g l') (hl : l ≤ l') : IsOWith c f g l :=
  is_O_with.of_bound <| hl h.bound

theorem IsO.mono (h : IsO f g l') (hl : l ≤ l') : IsO f g l :=
  is_O_iff_is_O_with.2 <| h.IsOWith.imp fun c h => h.mono hl

theorem IsOₓ.mono (h : IsOₓ f g l') (hl : l ≤ l') : IsOₓ f g l :=
  is_o.of_is_O_with fun c cpos => (h.forall_is_O_with cpos).mono hl

theorem IsOWith.trans (hfg : IsOWith c f g l) (hgk : IsOWith c' g k l) (hc : 0 ≤ c) : IsOWith (c * c') f k l := by
  unfold is_O_with  at *
  filter_upwards [hfg, hgk] with x hx hx'
  calc ∥f x∥ ≤ c * ∥g x∥ := hx _ ≤ c * (c' * ∥k x∥) := mul_le_mul_of_nonneg_left hx' hc _ = c * c' * ∥k x∥ :=
      (mul_assoc _ _ _).symm

theorem IsO.trans (hfg : IsO f g' l) (hgk : IsO g' k l) : IsO f k l :=
  let ⟨c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨c', hc'⟩ := hgk.IsOWith
  (hc.trans hc' cnonneg).IsO

theorem IsOₓ.trans_is_O_with (hfg : IsOₓ f g l) (hgk : IsOWith c g k l) (hc : 0 < c) : IsOₓ f k l := by
  unfold is_o  at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk (le_of_ltₓ this)).congr_const (div_mul_cancel _ (ne_of_gtₓ hc))

theorem IsOₓ.trans_is_O (hfg : IsOₓ f g l) (hgk : IsO g k' l) : IsOₓ f k' l :=
  let ⟨c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_is_O_with hc cpos

theorem IsOWith.trans_is_o (hfg : IsOWith c f g l) (hgk : IsOₓ g k l) (hc : 0 < c) : IsOₓ f k l := by
  unfold is_o  at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) (le_of_ltₓ hc)).congr_const (mul_div_cancel' _ (ne_of_gtₓ hc))

theorem IsO.trans_is_o (hfg : IsO f g' l) (hgk : IsOₓ g' k l) : IsOₓ f k l :=
  let ⟨c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_is_o hgk cpos

theorem IsOₓ.trans (hfg : IsOₓ f g l) (hgk : IsOₓ g k l) : IsOₓ f k l :=
  hfg.trans_is_O_with hgk.IsOWith one_pos

section

variable (l)

theorem is_O_with_of_le' (hfg : ∀ x, ∥f x∥ ≤ c * ∥g x∥) : IsOWith c f g l :=
  is_O_with.of_bound <| univ_mem' hfg

theorem is_O_with_of_le (hfg : ∀ x, ∥f x∥ ≤ ∥g x∥) : IsOWith 1 f g l :=
  (is_O_with_of_le' l) fun x => by
    rw [one_mulₓ]
    exact hfg x

theorem is_O_of_le' (hfg : ∀ x, ∥f x∥ ≤ c * ∥g x∥) : IsO f g l :=
  (is_O_with_of_le' l hfg).IsO

theorem is_O_of_le (hfg : ∀ x, ∥f x∥ ≤ ∥g x∥) : IsO f g l :=
  (is_O_with_of_le l hfg).IsO

end

theorem is_O_with_refl (f : α → E) (l : Filter α) : IsOWith 1 f f l :=
  (is_O_with_of_le l) fun _ => le_rfl

theorem is_O_refl (f : α → E) (l : Filter α) : IsO f f l :=
  (is_O_with_refl f l).IsO

theorem IsOWith.trans_le (hfg : IsOWith c f g l) (hgk : ∀ x, ∥g x∥ ≤ ∥k x∥) (hc : 0 ≤ c) : IsOWith c f k l :=
  (hfg.trans (is_O_with_of_le l hgk) hc).congr_const <| mul_oneₓ c

theorem IsO.trans_le (hfg : IsO f g' l) (hgk : ∀ x, ∥g' x∥ ≤ ∥k x∥) : IsO f k l :=
  hfg.trans (is_O_of_le l hgk)

theorem IsOₓ.trans_le (hfg : IsOₓ f g l) (hgk : ∀ x, ∥g x∥ ≤ ∥k x∥) : IsOₓ f k l :=
  hfg.trans_is_O_with (is_O_with_of_le _ hgk) zero_lt_one

section Bot

variable (c f g)

@[simp]
theorem is_O_with_bot : IsOWith c f g ⊥ :=
  is_O_with.of_bound <| trivialₓ

@[simp]
theorem is_O_bot : IsO f g ⊥ :=
  (is_O_with_bot 1 f g).IsO

@[simp]
theorem is_o_bot : IsOₓ f g ⊥ :=
  is_o.of_is_O_with fun c _ => is_O_with_bot c f g

end Bot

@[simp]
theorem is_O_with_pure {x} : IsOWith c f g (pure x) ↔ ∥f x∥ ≤ c * ∥g x∥ :=
  is_O_with_iff

theorem IsOWith.join (h : IsOWith c f g l) (h' : IsOWith c f g l') : IsOWith c f g (l⊔l') :=
  is_O_with.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩

theorem IsOWith.join' (h : IsOWith c f g' l) (h' : IsOWith c' f g' l') : IsOWith (max c c') f g' (l⊔l') :=
  is_O_with.of_bound <| mem_sup.2 ⟨(h.weaken <| le_max_leftₓ c c').bound, (h'.weaken <| le_max_rightₓ c c').bound⟩

theorem IsO.join (h : IsO f g' l) (h' : IsO f g' l') : IsO f g' (l⊔l') :=
  let ⟨c, hc⟩ := h.IsOWith
  let ⟨c', hc'⟩ := h'.IsOWith
  (hc.join' hc').IsO

theorem IsOₓ.join (h : IsOₓ f g l) (h' : IsOₓ f g l') : IsOₓ f g (l⊔l') :=
  is_o.of_is_O_with fun c cpos => (h.forall_is_O_with cpos).join (h'.forall_is_O_with cpos)

/-! ### Simplification : norm -/


@[simp]
theorem is_O_with_norm_right : IsOWith c f (fun x => ∥g' x∥) l ↔ IsOWith c f g' l := by
  simp only [is_O_with, norm_norm]

alias is_O_with_norm_right ↔ Asymptotics.IsOWith.of_norm_right Asymptotics.IsOWith.norm_right

@[simp]
theorem is_O_norm_right : IsO f (fun x => ∥g' x∥) l ↔ IsO f g' l := by
  unfold is_O
  exact exists_congr fun _ => is_O_with_norm_right

alias is_O_norm_right ↔ Asymptotics.IsO.of_norm_right Asymptotics.IsO.norm_right

@[simp]
theorem is_o_norm_right : IsOₓ f (fun x => ∥g' x∥) l ↔ IsOₓ f g' l := by
  unfold is_o
  exact forall₂_congrₓ fun _ _ => is_O_with_norm_right

alias is_o_norm_right ↔ Asymptotics.IsOₓ.of_norm_right Asymptotics.IsOₓ.norm_right

@[simp]
theorem is_O_with_norm_left : IsOWith c (fun x => ∥f' x∥) g l ↔ IsOWith c f' g l := by
  simp only [is_O_with, norm_norm]

alias is_O_with_norm_left ↔ Asymptotics.IsOWith.of_norm_left Asymptotics.IsOWith.norm_left

@[simp]
theorem is_O_norm_left : IsO (fun x => ∥f' x∥) g l ↔ IsO f' g l := by
  unfold is_O
  exact exists_congr fun _ => is_O_with_norm_left

alias is_O_norm_left ↔ Asymptotics.IsO.of_norm_left Asymptotics.IsO.norm_left

@[simp]
theorem is_o_norm_left : IsOₓ (fun x => ∥f' x∥) g l ↔ IsOₓ f' g l := by
  unfold is_o
  exact forall₂_congrₓ fun _ _ => is_O_with_norm_left

alias is_o_norm_left ↔ Asymptotics.IsOₓ.of_norm_left Asymptotics.IsOₓ.norm_left

theorem is_O_with_norm_norm : IsOWith c (fun x => ∥f' x∥) (fun x => ∥g' x∥) l ↔ IsOWith c f' g' l :=
  is_O_with_norm_left.trans is_O_with_norm_right

alias is_O_with_norm_norm ↔ Asymptotics.IsOWith.of_norm_norm Asymptotics.IsOWith.norm_norm

theorem is_O_norm_norm : IsO (fun x => ∥f' x∥) (fun x => ∥g' x∥) l ↔ IsO f' g' l :=
  is_O_norm_left.trans is_O_norm_right

alias is_O_norm_norm ↔ Asymptotics.IsO.of_norm_norm Asymptotics.IsO.norm_norm

theorem is_o_norm_norm : IsOₓ (fun x => ∥f' x∥) (fun x => ∥g' x∥) l ↔ IsOₓ f' g' l :=
  is_o_norm_left.trans is_o_norm_right

alias is_o_norm_norm ↔ Asymptotics.IsOₓ.of_norm_norm Asymptotics.IsOₓ.norm_norm

/-! ### Simplification: negate -/


@[simp]
theorem is_O_with_neg_right : IsOWith c f (fun x => -g' x) l ↔ IsOWith c f g' l := by
  simp only [is_O_with, norm_neg]

alias is_O_with_neg_right ↔ Asymptotics.IsOWith.of_neg_right Asymptotics.IsOWith.neg_right

@[simp]
theorem is_O_neg_right : IsO f (fun x => -g' x) l ↔ IsO f g' l := by
  unfold is_O
  exact exists_congr fun _ => is_O_with_neg_right

alias is_O_neg_right ↔ Asymptotics.IsO.of_neg_right Asymptotics.IsO.neg_right

@[simp]
theorem is_o_neg_right : IsOₓ f (fun x => -g' x) l ↔ IsOₓ f g' l := by
  unfold is_o
  exact forall₂_congrₓ fun _ _ => is_O_with_neg_right

alias is_o_neg_right ↔ Asymptotics.IsOₓ.of_neg_right Asymptotics.IsOₓ.neg_right

@[simp]
theorem is_O_with_neg_left : IsOWith c (fun x => -f' x) g l ↔ IsOWith c f' g l := by
  simp only [is_O_with, norm_neg]

alias is_O_with_neg_left ↔ Asymptotics.IsOWith.of_neg_left Asymptotics.IsOWith.neg_left

@[simp]
theorem is_O_neg_left : IsO (fun x => -f' x) g l ↔ IsO f' g l := by
  unfold is_O
  exact exists_congr fun _ => is_O_with_neg_left

alias is_O_neg_left ↔ Asymptotics.IsO.of_neg_left Asymptotics.IsO.neg_left

@[simp]
theorem is_o_neg_left : IsOₓ (fun x => -f' x) g l ↔ IsOₓ f' g l := by
  unfold is_o
  exact forall₂_congrₓ fun _ _ => is_O_with_neg_left

alias is_o_neg_left ↔ Asymptotics.IsOₓ.of_neg_right Asymptotics.IsOₓ.neg_left

/-! ### Product of functions (right) -/


theorem is_O_with_fst_prod : IsOWith 1 f' (fun x => (f' x, g' x)) l :=
  (is_O_with_of_le l) fun x => le_max_leftₓ _ _

theorem is_O_with_snd_prod : IsOWith 1 g' (fun x => (f' x, g' x)) l :=
  (is_O_with_of_le l) fun x => le_max_rightₓ _ _

theorem is_O_fst_prod : IsO f' (fun x => (f' x, g' x)) l :=
  is_O_with_fst_prod.IsO

theorem is_O_snd_prod : IsO g' (fun x => (f' x, g' x)) l :=
  is_O_with_snd_prod.IsO

theorem is_O_fst_prod' {f' : α → E' × F'} : IsO (fun x => (f' x).1) f' l := by
  simpa [is_O, is_O_with] using is_O_fst_prod

theorem is_O_snd_prod' {f' : α → E' × F'} : IsO (fun x => (f' x).2) f' l := by
  simpa [is_O, is_O_with] using is_O_snd_prod

section

variable (f' k')

theorem IsOWith.prod_rightl (h : IsOWith c f g' l) (hc : 0 ≤ c) : IsOWith c f (fun x => (g' x, k' x)) l :=
  (h.trans is_O_with_fst_prod hc).congr_const (mul_oneₓ c)

theorem IsO.prod_rightl (h : IsO f g' l) : IsO f (fun x => (g' x, k' x)) l :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).IsO

theorem IsOₓ.prod_rightl (h : IsOₓ f g' l) : IsOₓ f (fun x => (g' x, k' x)) l :=
  is_o.of_is_O_with fun c cpos => (h.forall_is_O_with cpos).prod_rightl k' (le_of_ltₓ cpos)

theorem IsOWith.prod_rightr (h : IsOWith c f g' l) (hc : 0 ≤ c) : IsOWith c f (fun x => (f' x, g' x)) l :=
  (h.trans is_O_with_snd_prod hc).congr_const (mul_oneₓ c)

theorem IsO.prod_rightr (h : IsO f g' l) : IsO f (fun x => (f' x, g' x)) l :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).IsO

theorem IsOₓ.prod_rightr (h : IsOₓ f g' l) : IsOₓ f (fun x => (f' x, g' x)) l :=
  is_o.of_is_O_with fun c cpos => (h.forall_is_O_with cpos).prod_rightr f' (le_of_ltₓ cpos)

end

theorem IsOWith.prod_left_same (hf : IsOWith c f' k' l) (hg : IsOWith c g' k' l) :
    IsOWith c (fun x => (f' x, g' x)) k' l := by
  rw [is_O_with_iff] at * <;> filter_upwards [hf, hg] with x using max_leₓ

theorem IsOWith.prod_left (hf : IsOWith c f' k' l) (hg : IsOWith c' g' k' l) :
    IsOWith (max c c') (fun x => (f' x, g' x)) k' l :=
  (hf.weaken <| le_max_leftₓ c c').prod_left_same (hg.weaken <| le_max_rightₓ c c')

theorem IsOWith.prod_left_fst (h : IsOWith c (fun x => (f' x, g' x)) k' l) : IsOWith c f' k' l :=
  (is_O_with_fst_prod.trans h zero_le_one).congr_const <| one_mulₓ c

theorem IsOWith.prod_left_snd (h : IsOWith c (fun x => (f' x, g' x)) k' l) : IsOWith c g' k' l :=
  (is_O_with_snd_prod.trans h zero_le_one).congr_const <| one_mulₓ c

theorem is_O_with_prod_left : IsOWith c (fun x => (f' x, g' x)) k' l ↔ IsOWith c f' k' l ∧ IsOWith c g' k' l :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩

theorem IsO.prod_left (hf : IsO f' k' l) (hg : IsO g' k' l) : IsO (fun x => (f' x, g' x)) k' l :=
  let ⟨c, hf⟩ := hf.IsOWith
  let ⟨c', hg⟩ := hg.IsOWith
  (hf.prodLeft hg).IsO

theorem IsO.prod_left_fst (h : IsO (fun x => (f' x, g' x)) k' l) : IsO f' k' l :=
  is_O_fst_prod.trans h

theorem IsO.prod_left_snd (h : IsO (fun x => (f' x, g' x)) k' l) : IsO g' k' l :=
  is_O_snd_prod.trans h

@[simp]
theorem is_O_prod_left : IsO (fun x => (f' x, g' x)) k' l ↔ IsO f' k' l ∧ IsO g' k' l :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩

theorem IsOₓ.prod_left (hf : IsOₓ f' k' l) (hg : IsOₓ g' k' l) : IsOₓ (fun x => (f' x, g' x)) k' l :=
  is_o.of_is_O_with fun c hc => (hf.forall_is_O_with hc).prod_left_same (hg.forall_is_O_with hc)

theorem IsOₓ.prod_left_fst (h : IsOₓ (fun x => (f' x, g' x)) k' l) : IsOₓ f' k' l :=
  is_O_fst_prod.trans_is_o h

theorem IsOₓ.prod_left_snd (h : IsOₓ (fun x => (f' x, g' x)) k' l) : IsOₓ g' k' l :=
  is_O_snd_prod.trans_is_o h

@[simp]
theorem is_o_prod_left : IsOₓ (fun x => (f' x, g' x)) k' l ↔ IsOₓ f' k' l ∧ IsOₓ g' k' l :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩

theorem IsOWith.eq_zero_imp (h : IsOWith c f'' g'' l) : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  (Eventually.mono h.bound) fun x hx hg =>
    norm_le_zero_iff.1 <| by
      simpa [hg] using hx

theorem IsO.eq_zero_imp (h : IsO f'' g'' l) : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨C, hC⟩ := h.IsOWith
  hC.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {c₁ c₂ : ℝ} {f₁ f₂ : α → E'}

theorem IsOWith.add (h₁ : IsOWith c₁ f₁ g l) (h₂ : IsOWith c₂ f₂ g l) : IsOWith (c₁ + c₂) (fun x => f₁ x + f₂ x) g l :=
  by
  rw [is_O_with] at * <;>
    filter_upwards [h₁,
      h₂] with x hx₁ hx₂ using calc
        ∥f₁ x + f₂ x∥ ≤ c₁ * ∥g x∥ + c₂ * ∥g x∥ := norm_add_le_of_le hx₁ hx₂
        _ = (c₁ + c₂) * ∥g x∥ := (add_mulₓ _ _ _).symm
        

theorem IsO.add (h₁ : IsO f₁ g l) (h₂ : IsO f₂ g l) : IsO (fun x => f₁ x + f₂ x) g l :=
  let ⟨c₁, hc₁⟩ := h₁.IsOWith
  let ⟨c₂, hc₂⟩ := h₂.IsOWith
  (hc₁.add hc₂).IsO

theorem IsOₓ.add (h₁ : IsOₓ f₁ g l) (h₂ : IsOₓ f₂ g l) : IsOₓ (fun x => f₁ x + f₂ x) g l :=
  is_o.of_is_O_with fun c cpos =>
    ((h₁.forall_is_O_with <| half_pos cpos).add (h₂.forall_is_O_with <| half_pos cpos)).congr_const (add_halves c)

theorem IsOₓ.add_add {g₁ g₂ : α → F'} (h₁ : IsOₓ f₁ g₁ l) (h₂ : IsOₓ f₂ g₂ l) :
    IsOₓ (fun x => f₁ x + f₂ x) (fun x => ∥g₁ x∥ + ∥g₂ x∥) l := by
  refine' (h₁.trans_le fun x => _).add (h₂.trans_le _) <;> simp [Real.norm_eq_abs, abs_of_nonneg, add_nonneg]

theorem IsO.add_is_o (h₁ : IsO f₁ g l) (h₂ : IsOₓ f₂ g l) : IsO (fun x => f₁ x + f₂ x) g l :=
  h₁.add h₂.IsO

theorem IsOₓ.add_is_O (h₁ : IsOₓ f₁ g l) (h₂ : IsO f₂ g l) : IsO (fun x => f₁ x + f₂ x) g l :=
  h₁.IsO.add h₂

theorem IsOWith.add_is_o (h₁ : IsOWith c₁ f₁ g l) (h₂ : IsOₓ f₂ g l) (hc : c₁ < c₂) :
    IsOWith c₂ (fun x => f₁ x + f₂ x) g l :=
  (h₁.add (h₂.forall_is_O_with (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)

theorem IsOₓ.add_is_O_with (h₁ : IsOₓ f₁ g l) (h₂ : IsOWith c₁ f₂ g l) (hc : c₁ < c₂) :
    IsOWith c₂ (fun x => f₁ x + f₂ x) g l :=
  (h₂.add_is_o h₁ hc).congr_left fun _ => add_commₓ _ _

theorem IsOWith.sub (h₁ : IsOWith c₁ f₁ g l) (h₂ : IsOWith c₂ f₂ g l) : IsOWith (c₁ + c₂) (fun x => f₁ x - f₂ x) g l :=
  by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsOWith.sub_is_o (h₁ : IsOWith c₁ f₁ g l) (h₂ : IsOₓ f₂ g l) (hc : c₁ < c₂) :
    IsOWith c₂ (fun x => f₁ x - f₂ x) g l := by
  simpa only [sub_eq_add_neg] using h₁.add_is_o h₂.neg_left hc

theorem IsO.sub (h₁ : IsO f₁ g l) (h₂ : IsO f₂ g l) : IsO (fun x => f₁ x - f₂ x) g l := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsOₓ.sub (h₁ : IsOₓ f₁ g l) (h₂ : IsOₓ f₂ g l) : IsOₓ (fun x => f₁ x - f₂ x) g l := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

end add_sub

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/


section IsOOAsRel

variable {f₁ f₂ f₃ : α → E'}

theorem IsOWith.symm (h : IsOWith c (fun x => f₁ x - f₂ x) g l) : IsOWith c (fun x => f₂ x - f₁ x) g l :=
  h.neg_left.congr_left fun x => neg_sub _ _

theorem is_O_with_comm : IsOWith c (fun x => f₁ x - f₂ x) g l ↔ IsOWith c (fun x => f₂ x - f₁ x) g l :=
  ⟨IsOWith.symm, IsOWith.symm⟩

theorem IsO.symm (h : IsO (fun x => f₁ x - f₂ x) g l) : IsO (fun x => f₂ x - f₁ x) g l :=
  h.neg_left.congr_left fun x => neg_sub _ _

theorem is_O_comm : IsO (fun x => f₁ x - f₂ x) g l ↔ IsO (fun x => f₂ x - f₁ x) g l :=
  ⟨IsO.symm, IsO.symm⟩

theorem IsOₓ.symm (h : IsOₓ (fun x => f₁ x - f₂ x) g l) : IsOₓ (fun x => f₂ x - f₁ x) g l := by
  simpa only [neg_sub] using h.neg_left

theorem is_o_comm : IsOₓ (fun x => f₁ x - f₂ x) g l ↔ IsOₓ (fun x => f₂ x - f₁ x) g l :=
  ⟨IsOₓ.symm, IsOₓ.symm⟩

theorem IsOWith.triangle (h₁ : IsOWith c (fun x => f₁ x - f₂ x) g l) (h₂ : IsOWith c' (fun x => f₂ x - f₃ x) g l) :
    IsOWith (c + c') (fun x => f₁ x - f₃ x) g l :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _

theorem IsO.triangle (h₁ : IsO (fun x => f₁ x - f₂ x) g l) (h₂ : IsO (fun x => f₂ x - f₃ x) g l) :
    IsO (fun x => f₁ x - f₃ x) g l :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _

theorem IsOₓ.triangle (h₁ : IsOₓ (fun x => f₁ x - f₂ x) g l) (h₂ : IsOₓ (fun x => f₂ x - f₃ x) g l) :
    IsOₓ (fun x => f₁ x - f₃ x) g l :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _

theorem IsO.congr_of_sub (h : IsO (fun x => f₁ x - f₂ x) g l) : IsO f₁ g l ↔ IsO f₂ g l :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩

theorem IsOₓ.congr_of_sub (h : IsOₓ (fun x => f₁ x - f₂ x) g l) : IsOₓ f₁ g l ↔ IsOₓ f₂ g l :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩

end IsOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

theorem is_o_zero : IsOₓ (fun x => (0 : E')) g' l :=
  is_o.of_bound fun c hc =>
    univ_mem' fun x => by
      simpa using mul_nonneg hc.le (norm_nonneg <| g' x)

theorem is_O_with_zero (hc : 0 ≤ c) : IsOWith c (fun x => (0 : E')) g' l :=
  is_O_with.of_bound <|
    univ_mem' fun x => by
      simpa using mul_nonneg hc (norm_nonneg <| g' x)

theorem is_O_with_zero' : IsOWith 0 (fun x => (0 : E')) g l :=
  is_O_with.of_bound <|
    univ_mem' fun x => by
      simp

theorem is_O_zero : IsO (fun x => (0 : E')) g l :=
  is_O_iff_is_O_with.2 ⟨0, is_O_with_zero' _ _⟩

theorem is_O_refl_left : IsO (fun x => f' x - f' x) g' l :=
  (is_O_zero g' l).congr_left fun x => (sub_self _).symm

theorem is_o_refl_left : IsOₓ (fun x => f' x - f' x) g' l :=
  (is_o_zero g' l).congr_left fun x => (sub_self _).symm

variable {g g' l}

@[simp]
theorem is_O_with_zero_right_iff : IsOWith c f'' (fun x => (0 : F'')) l ↔ ∀ᶠ x in l, f'' x = 0 := by
  simp only [is_O_with, exists_prop, true_andₓ, norm_zero, mul_zero, norm_le_zero_iff]

@[simp]
theorem is_O_zero_right_iff : IsO f'' (fun x => (0 : F'')) l ↔ ∀ᶠ x in l, f'' x = 0 :=
  ⟨fun h =>
    let ⟨c, hc⟩ := h.IsOWith
    is_O_with_zero_right_iff.1 hc,
    fun h => (is_O_with_zero_right_iff.2 h : IsOWith 1 _ _ _).IsO⟩

@[simp]
theorem is_o_zero_right_iff : IsOₓ f'' (fun x => (0 : F'')) l ↔ ∀ᶠ x in l, f'' x = 0 :=
  ⟨fun h => is_O_zero_right_iff.1 h.IsO, fun h => is_o.of_is_O_with fun c hc => is_O_with_zero_right_iff.2 h⟩

theorem is_O_with_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsOWith (∥c∥ / ∥c'∥) (fun x : α => c) (fun x => c') l := by
  unfold is_O_with
  apply univ_mem'
  intro x
  rw [mem_set_of_eq, div_mul_cancel]
  rwa [Ne.def, norm_eq_zero]

theorem is_O_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) : IsO (fun x : α => c) (fun x => c') l :=
  (is_O_with_const_const c hc' l).IsO

@[simp]
theorem is_O_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.ne_bot] :
    IsO (fun x : α => c) (fun x => c') l ↔ c' = 0 → c = 0 := by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp
    
  · simp [hc', is_O_const_const _ hc']
    

@[simp]
theorem is_O_pure {x} : IsO f'' g'' (pure x) ↔ g'' x = 0 → f'' x = 0 :=
  calc
    IsO f'' g'' (pure x) ↔ IsO (fun y : α => f'' x) (fun _ => g'' x) (pure x) := is_O_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := is_O_const_const_iff _
    

end ZeroConst

@[simp]
theorem is_O_with_top : IsOWith c f g ⊤ ↔ ∀ x, ∥f x∥ ≤ c * ∥g x∥ := by
  rw [is_O_with] <;> rfl

@[simp]
theorem is_O_top : IsO f g ⊤ ↔ ∃ C, ∀ x, ∥f x∥ ≤ C * ∥g x∥ := by
  rw [is_O_iff] <;> rfl

@[simp]
theorem is_o_top : IsOₓ f'' g'' ⊤ ↔ ∀ x, f'' x = 0 := by
  refine' ⟨_, fun h => (is_o_zero g'' ⊤).congr (fun x => (h x).symm) fun x => rfl⟩
  simp only [is_o_iff, eventually_top]
  refine' fun h x => norm_le_zero_iff.1 _
  have : tendsto (fun c : ℝ => c * ∥g'' x∥) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left inf_le_left
  exact
    le_of_tendsto_of_tendsto tendsto_const_nhds this
      (eventually_nhds_within_iff.2 <| eventually_of_forall fun c hc => h hc x)

@[simp]
theorem is_O_with_principal {s : Set α} : IsOWith c f g (𝓟 s) ↔ ∀, ∀ x ∈ s, ∀, ∥f x∥ ≤ c * ∥g x∥ := by
  rw [is_O_with] <;> rfl

theorem is_O_principal {s : Set α} : IsO f g (𝓟 s) ↔ ∃ c, ∀, ∀ x ∈ s, ∀, ∥f x∥ ≤ c * ∥g x∥ := by
  rw [is_O_iff] <;> rfl

theorem is_O_with_const_one (c : E) (l : Filter α) : IsOWith ∥c∥ (fun x : α => c) (fun x => (1 : 𝕜)) l := by
  refine' (is_O_with_const_const c _ l).congr_const _
  · rw [norm_one, div_one]
    
  · exact one_ne_zero
    

theorem is_O_const_one (c : E) (l : Filter α) : IsO (fun x : α => c) (fun x => (1 : 𝕜)) l :=
  (is_O_with_const_one c l).IsO

section

variable (𝕜)

theorem is_o_const_iff_is_o_one {c : F''} (hc : c ≠ 0) : IsOₓ f (fun x => c) l ↔ IsOₓ f (fun x => (1 : 𝕜)) l :=
  ⟨fun h => h.trans_is_O <| is_O_const_one c l, fun h => h.trans_is_O <| is_O_const_const _ hc _⟩

end

theorem is_o_const_iff {c : F''} (hc : c ≠ 0) : IsOₓ f'' (fun x => c) l ↔ Tendsto f'' l (𝓝 0) :=
  (is_o_const_iff_is_o_one ℝ hc).trans
    (by
      clear hc c
      simp only [is_o, is_O_with, norm_one, mul_oneₓ, metric.nhds_basis_closed_ball.tendsto_right_iff,
        Metric.mem_closed_ball, dist_zero_right])

theorem is_o_id_const {c : F''} (hc : c ≠ 0) : IsOₓ (fun x : E'' => x) (fun x => c) (𝓝 0) :=
  (is_o_const_iff hc).mpr (continuous_id.Tendsto 0)

theorem _root_.filter.is_bounded_under.is_O_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) {c : F''} (hc : c ≠ 0) :
    IsO f (fun x => c) l := by
  rcases h with ⟨C, hC⟩
  refine' (is_O.of_bound 1 _).trans (is_O_const_const C hc l)
  refine' (eventually_map.1 hC).mono fun x h => _
  calc ∥f x∥ ≤ C := h _ ≤ abs C := le_abs_self C _ = 1 * ∥C∥ := (one_mulₓ _).symm

theorem is_O_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) : IsO f'' (fun x => c) l :=
  h.norm.is_bounded_under_le.is_O_const hc

section

variable (𝕜)

theorem is_o_one_iff : IsOₓ f'' (fun x => (1 : 𝕜)) l ↔ Tendsto f'' l (𝓝 0) :=
  is_o_const_iff one_ne_zero

theorem is_O_one_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) : IsO f'' (fun x => (1 : 𝕜)) l :=
  is_O_const_of_tendsto h one_ne_zero

theorem IsO.trans_tendsto_nhds (hfg : IsO f g'' l) {y : F''} (hg : Tendsto g'' l (𝓝 y)) : IsO f (fun x => (1 : 𝕜)) l :=
  hfg.trans <| is_O_one_of_tendsto 𝕜 hg

end

theorem IsO.trans_tendsto (hfg : IsO f'' g'' l) (hg : Tendsto g'' l (𝓝 0)) : Tendsto f'' l (𝓝 0) :=
  (is_o_one_iff ℝ).1 <| hfg.trans_is_o <| (is_o_one_iff ℝ).2 hg

theorem IsOₓ.trans_tendsto (hfg : IsOₓ f'' g'' l) (hg : Tendsto g'' l (𝓝 0)) : Tendsto f'' l (𝓝 0) :=
  hfg.IsO.trans_tendsto hg

/-! ### Multiplication by a constant -/


theorem is_O_with_const_mul_self (c : R) (f : α → R) (l : Filter α) : IsOWith ∥c∥ (fun x => c * f x) f l :=
  (is_O_with_of_le' _) fun x => norm_mul_le _ _

theorem is_O_const_mul_self (c : R) (f : α → R) (l : Filter α) : IsO (fun x => c * f x) f l :=
  (is_O_with_const_mul_self c f l).IsO

theorem IsOWith.const_mul_left {f : α → R} (h : IsOWith c f g l) (c' : R) :
    IsOWith (∥c'∥ * c) (fun x => c' * f x) g l :=
  (is_O_with_const_mul_self c' f l).trans h (norm_nonneg c')

theorem IsO.const_mul_left {f : α → R} (h : IsO f g l) (c' : R) : IsO (fun x => c' * f x) g l :=
  let ⟨c, hc⟩ := h.IsOWith
  (hc.const_mul_left c').IsO

theorem is_O_with_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) : IsOWith ∥(↑u⁻¹ : R)∥ f (fun x => ↑u * f x) l :=
  (is_O_with_const_mul_self ↑u⁻¹ _ l).congr_left fun x => u.inv_mul_cancel_left (f x)

theorem is_O_with_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    IsOWith ∥c∥⁻¹ f (fun x => c * f x) l :=
  (is_O_with_self_const_mul' (Units.mk0 c hc) f l).congr_const <| norm_inv c

theorem is_O_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) : IsO f (fun x => c * f x) l :=
  let ⟨u, hu⟩ := hc
  hu ▸ (is_O_with_self_const_mul' u f l).IsO

theorem is_O_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) : IsO f (fun x => c * f x) l :=
  is_O_self_const_mul' (IsUnit.mk0 c hc) f l

theorem is_O_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) : IsO (fun x => c * f x) g l ↔ IsO f g l :=
  ⟨(is_O_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩

theorem is_O_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) : IsO (fun x => c * f x) g l ↔ IsO f g l :=
  is_O_const_mul_left_iff' <| IsUnit.mk0 c hc

theorem IsOₓ.const_mul_left {f : α → R} (h : IsOₓ f g l) (c : R) : IsOₓ (fun x => c * f x) g l :=
  (is_O_const_mul_self c f l).trans_is_o h

theorem is_o_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) : IsOₓ (fun x => c * f x) g l ↔ IsOₓ f g l :=
  ⟨(is_O_self_const_mul' hc f l).trans_is_o, fun h => h.const_mul_left c⟩

theorem is_o_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) : IsOₓ (fun x => c * f x) g l ↔ IsOₓ f g l :=
  is_o_const_mul_left_iff' <| IsUnit.mk0 c hc

theorem IsOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c') (h : IsOWith c' f (fun x => c * g x) l) :
    IsOWith (c' * ∥c∥) f g l :=
  h.trans (is_O_with_const_mul_self c g l) hc'

theorem IsO.of_const_mul_right {g : α → R} {c : R} (h : IsO f (fun x => c * g x) l) : IsO f g l :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).IsO

theorem IsOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c') (h : IsOWith c' f g l) :
    IsOWith (c' * ∥(↑u⁻¹ : R)∥) f (fun x => ↑u * g x) l :=
  h.trans (is_O_with_self_const_mul' _ _ _) hc'

theorem IsOWith.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c') (h : IsOWith c' f g l) :
    IsOWith (c' * ∥c∥⁻¹) f (fun x => c * g x) l :=
  h.trans (is_O_with_self_const_mul c hc g l) hc'

theorem IsO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : IsO f g l) : IsO f (fun x => c * g x) l :=
  h.trans (is_O_self_const_mul' hc g l)

theorem IsO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : IsO f g l) : IsO f (fun x => c * g x) l :=
  h.const_mul_right' <| IsUnit.mk0 c hc

theorem is_O_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) : IsO f (fun x => c * g x) l ↔ IsO f g l :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

theorem is_O_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) : IsO f (fun x => c * g x) l ↔ IsO f g l :=
  is_O_const_mul_right_iff' <| IsUnit.mk0 c hc

theorem IsOₓ.of_const_mul_right {g : α → R} {c : R} (h : IsOₓ f (fun x => c * g x) l) : IsOₓ f g l :=
  h.trans_is_O (is_O_const_mul_self c g l)

theorem IsOₓ.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : IsOₓ f g l) : IsOₓ f (fun x => c * g x) l :=
  h.trans_is_O (is_O_self_const_mul' hc g l)

theorem IsOₓ.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : IsOₓ f g l) : IsOₓ f (fun x => c * g x) l :=
  h.const_mul_right' <| IsUnit.mk0 c hc

theorem is_o_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) : IsOₓ f (fun x => c * g x) l ↔ IsOₓ f g l :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

theorem is_o_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) : IsOₓ f (fun x => c * g x) l ↔ IsOₓ f g l :=
  is_o_const_mul_right_iff' <| IsUnit.mk0 c hc

/-! ### Multiplication -/


theorem IsOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ} (h₁ : IsOWith c₁ f₁ g₁ l) (h₂ : IsOWith c₂ f₂ g₂ l) :
    IsOWith (c₁ * c₂) (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) l := by
  unfold is_O_with  at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_transₓ (norm_mul_le _ _)
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_transₓ (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_commₓ]

theorem IsO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : IsO f₁ g₁ l) (h₂ : IsO f₂ g₂ l) :
    IsO (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) l :=
  let ⟨c, hc⟩ := h₁.IsOWith
  let ⟨c', hc'⟩ := h₂.IsOWith
  (hc.mul hc').IsO

theorem IsO.mul_is_o {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : IsO f₁ g₁ l) (h₂ : IsOₓ f₂ g₂ l) :
    IsOₓ (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) l := by
  unfold is_o  at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gtₓ c'pos))

theorem IsOₓ.mul_is_O {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : IsOₓ f₁ g₁ l) (h₂ : IsO f₂ g₂ l) :
    IsOₓ (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) l := by
  unfold is_o  at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gtₓ c'pos))

theorem IsOₓ.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : IsOₓ f₁ g₁ l) (h₂ : IsOₓ f₂ g₂ l) :
    IsOₓ (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) l :=
  h₁.mul_is_O h₂.IsO

theorem IsOWith.pow' {f : α → R} {g : α → 𝕜} (h : IsOWith c f g l) :
    ∀ n : ℕ, IsOWith (Nat.casesOn n ∥(1 : R)∥ fun n => c ^ (n + 1)) (fun x => f x ^ n) (fun x => g x ^ n) l
  | 0 => by
    simpa using is_O_with_const_const (1 : R) (@one_ne_zero 𝕜 _ _) l
  | 1 => by
    simpa
  | n + 2 => by
    simpa [pow_succₓ] using h.mul (is_O_with.pow' (n + 1))

theorem IsOWith.pow [NormOneClass R] {f : α → R} {g : α → 𝕜} (h : IsOWith c f g l) :
    ∀ n : ℕ, IsOWith (c ^ n) (fun x => f x ^ n) (fun x => g x ^ n) l
  | 0 => by
    simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)

theorem IsO.pow {f : α → R} {g : α → 𝕜} (h : IsO f g l) (n : ℕ) : IsO (fun x => f x ^ n) (fun x => g x ^ n) l :=
  let ⟨C, hC⟩ := h.IsOWith
  is_O_iff_is_O_with.2 ⟨_, hC.pow' n⟩

theorem IsOₓ.pow {f : α → R} {g : α → 𝕜} (h : IsOₓ f g l) {n : ℕ} (hn : 0 < n) :
    IsOₓ (fun x => f x ^ n) (fun x => g x ^ n) l := by
  cases n
  exact hn.false.elim
  clear hn
  induction' n with n ihn
  · simpa only [pow_oneₓ]
    
  convert h.mul ihn <;> simp [pow_succₓ]

/-! ### Inverse -/


theorem IsOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsOWith c f g l) (h₀ : ∀ᶠ x in l, f x ≠ 0) :
    IsOWith c (fun x => (g x)⁻¹) (fun x => (f x)⁻¹) l := by
  refine' is_O_with.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => _))
  cases' le_or_ltₓ c 0 with hc hc
  · refine' (h₀ <| norm_le_zero_iff.1 _).elim
    exact hle.trans (mul_nonpos_of_nonpos_of_nonneg hc <| norm_nonneg _)
    
  · replace hle := inv_le_inv_of_le (norm_pos_iff.2 h₀) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff hc] using hle
    

theorem IsO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsO f g l) (h₀ : ∀ᶠ x in l, f x ≠ 0) :
    IsO (fun x => (g x)⁻¹) (fun x => (f x)⁻¹) l :=
  let ⟨c, hc⟩ := h.IsOWith
  (hc.inv_rev h₀).IsO

theorem IsOₓ.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsOₓ f g l) (h₀ : ∀ᶠ x in l, f x ≠ 0) :
    IsOₓ (fun x => (g x)⁻¹) (fun x => (f x)⁻¹) l :=
  is_o.of_is_O_with fun c hc => (h.def' hc).inv_rev h₀

/-! ### Scalar multiplication -/


section SmulConst

variable [NormedSpace 𝕜 E']

theorem IsOWith.const_smul_left (h : IsOWith c f' g l) (c' : 𝕜) : IsOWith (∥c'∥ * c) (fun x => c' • f' x) g l := by
  refine' ((h.norm_left.const_mul_left ∥c'∥).congr _ _ fun _ => rfl).of_norm_left <;>
    intros <;> simp only [norm_norm, norm_smul]

theorem is_O_const_smul_left_iff {c : 𝕜} (hc : c ≠ 0) : IsO (fun x => c • f' x) g l ↔ IsO f' g l := by
  have cne0 : ∥c∥ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_left]
  simp only [norm_smul]
  rw [is_O_const_mul_left_iff cne0, is_O_norm_left]

theorem is_o_const_smul_left (h : IsOₓ f' g l) (c : 𝕜) : IsOₓ (fun x => c • f' x) g l := by
  refine' ((h.norm_left.const_mul_left ∥c∥).congr_left _).of_norm_left
  exact fun x => (norm_smul _ _).symm

theorem is_o_const_smul_left_iff {c : 𝕜} (hc : c ≠ 0) : IsOₓ (fun x => c • f' x) g l ↔ IsOₓ f' g l := by
  have cne0 : ∥c∥ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_left]
  simp only [norm_smul]
  rw [is_o_const_mul_left_iff cne0, is_o_norm_left]

theorem is_O_const_smul_right {c : 𝕜} (hc : c ≠ 0) : IsO f (fun x => c • f' x) l ↔ IsO f f' l := by
  have cne0 : ∥c∥ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_right]
  simp only [norm_smul]
  rw [is_O_const_mul_right_iff cne0, is_O_norm_right]

theorem is_o_const_smul_right {c : 𝕜} (hc : c ≠ 0) : IsOₓ f (fun x => c • f' x) l ↔ IsOₓ f f' l := by
  have cne0 : ∥c∥ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_right]
  simp only [norm_smul]
  rw [is_o_const_mul_right_iff cne0, is_o_norm_right]

end SmulConst

section Smul

variable [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F']

theorem IsOWith.smul {k₁ k₂ : α → 𝕜} (h₁ : IsOWith c k₁ k₂ l) (h₂ : IsOWith c' f' g' l) :
    IsOWith (c * c') (fun x => k₁ x • f' x) (fun x => k₂ x • g' x) l := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
      

theorem IsO.smul {k₁ k₂ : α → 𝕜} (h₁ : IsO k₁ k₂ l) (h₂ : IsO f' g' l) :
    IsO (fun x => k₁ x • f' x) (fun x => k₂ x • g' x) l := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
      

theorem IsO.smul_is_o {k₁ k₂ : α → 𝕜} (h₁ : IsO k₁ k₂ l) (h₂ : IsOₓ f' g' l) :
    IsOₓ (fun x => k₁ x • f' x) (fun x => k₂ x • g' x) l := by
  refine' ((h₁.norm_norm.mul_is_o h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
      

theorem IsOₓ.smul_is_O {k₁ k₂ : α → 𝕜} (h₁ : IsOₓ k₁ k₂ l) (h₂ : IsO f' g' l) :
    IsOₓ (fun x => k₁ x • f' x) (fun x => k₂ x • g' x) l := by
  refine' ((h₁.norm_norm.mul_is_O h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
      

theorem IsOₓ.smul {k₁ k₂ : α → 𝕜} (h₁ : IsOₓ k₁ k₂ l) (h₂ : IsOₓ f' g' l) :
    IsOₓ (fun x => k₁ x • f' x) (fun x => k₂ x • g' x) l := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
      

end Smul

/-! ### Sum -/


section Sum

variable {ι : Type _} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

theorem IsOWith.sum (h : ∀, ∀ i ∈ s, ∀, IsOWith (C i) (A i) g l) :
    IsOWith (∑ i in s, C i) (fun x => ∑ i in s, A i x) g l := by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_O_with_zero', Finset.sum_empty, forall_true_iff]
    
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
    

theorem IsO.sum (h : ∀, ∀ i ∈ s, ∀, IsO (A i) g l) : IsO (fun x => ∑ i in s, A i x) g l := by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_O_zero, Finset.sum_empty, forall_true_iff]
    
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
    

theorem IsOₓ.sum (h : ∀, ∀ i ∈ s, ∀, IsOₓ (A i) g' l) : IsOₓ (fun x => ∑ i in s, A i x) g' l := by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_o_zero, Finset.sum_empty, forall_true_iff]
    
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
    

end Sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/


theorem IsOₓ.tendsto_div_nhds_zero {f g : α → 𝕜} {l : Filter α} (h : IsOₓ f g l) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
  have eq₁ : IsOₓ (fun x => f x / g x) (fun x => g x / g x) l := by
    simpa only [div_eq_mul_inv] using h.mul_is_O (is_O_refl _ _)
  have eq₂ : IsO (fun x => g x / g x) (fun x => (1 : 𝕜)) l :=
    is_O_of_le _ fun x => by
      simp [div_self_le_one]
  (is_o_one_iff 𝕜).mp (eq₁.trans_is_O eq₂)

theorem IsOₓ.tendsto_inv_smul_nhds_zero [NormedSpace 𝕜 E'] {f : α → E'} {g : α → 𝕜} {l : Filter α} (h : IsOₓ f g l) :
    Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero

theorem is_o_iff_tendsto' {f g : α → 𝕜} {l : Filter α} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    IsOₓ f g l ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (Iff.intro IsOₓ.tendsto_div_nhds_zero) fun h =>
    (((is_o_one_iff _).mpr h).mul_is_O (is_O_refl g l)).congr' (hgf.mono fun x => div_mul_cancel_of_imp)
      (eventually_of_forall fun x => one_mulₓ _)

theorem is_o_iff_tendsto {f g : α → 𝕜} {l : Filter α} (hgf : ∀ x, g x = 0 → f x = 0) :
    IsOₓ f g l ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  is_o_iff_tendsto' (eventually_of_forall hgf)

alias is_o_iff_tendsto' ↔ _ Asymptotics.is_o_of_tendsto'

alias is_o_iff_tendsto ↔ _ Asymptotics.is_o_of_tendsto

theorem is_o_const_left_of_ne {c : E''} (hc : c ≠ 0) : IsOₓ (fun x => c) g l ↔ Tendsto (norm ∘ g) l atTop := by
  constructor <;> intro h
  · refine' (at_top_basis' 1).tendsto_right_iff.2 fun C hC => _
    replace hC : 0 < C := zero_lt_one.trans_le hC
    replace h : is_o (fun _ => 1 : α → ℝ) g l := (is_O_const_const _ hc _).trans_is_o h
    refine' (h.def <| inv_pos.2 hC).mono fun x hx => _
    rwa [norm_one, ← div_eq_inv_mul, one_le_div hC] at hx
    
  · suffices : is_o (fun _ => 1 : α → ℝ) g l
    exact (is_O_const_const c (@one_ne_zero ℝ _ _) _).trans_is_o this
    refine' is_o_iff.2 fun ε ε0 => (tendsto_at_top.1 h ε⁻¹).mono fun x hx => _
    rwa [norm_one, ← inv_invₓ ε, ← div_eq_inv_mul, one_le_div (inv_pos.2 ε0)]
    

@[simp]
theorem is_o_const_left {c : E''} : IsOₓ (fun x => c) g'' l ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [is_o_zero, eq_self_iff_true, true_orₓ]
    
  · simp only [hc, false_orₓ, is_o_const_left_of_ne hc]
    

@[simp]
theorem is_o_const_const_iff [NeBot l] {d : E''} {c : F''} : IsOₓ (fun x => d) (fun x => c) l ↔ d = 0 := by
  have : ¬Tendsto (Function.const α ∥c∥) l atTop := not_tendsto_at_top_of_tendsto_nhds tendsto_const_nhds
  simp [Function.const, this]

@[simp]
theorem is_o_pure {x} : IsOₓ f'' g'' (pure x) ↔ f'' x = 0 :=
  calc
    IsOₓ f'' g'' (pure x) ↔ IsOₓ (fun y : α => f'' x) (fun _ => g'' x) (pure x) := is_o_congr rfl rfl
    _ ↔ f'' x = 0 := is_o_const_const_iff
    

theorem is_o_const_id_comap_norm_at_top (c : F'') : IsOₓ (fun x : E'' => c) id (comap norm atTop) :=
  is_o_const_left.2 <| Or.inr tendsto_comap

theorem is_o_const_id_at_top (c : E'') : IsOₓ (fun x : ℝ => c) id atTop :=
  is_o_const_left.2 <| Or.inr tendsto_abs_at_top_at_top

theorem is_o_const_id_at_bot (c : E'') : IsOₓ (fun x : ℝ => c) id atBot :=
  is_o_const_left.2 <| Or.inr tendsto_abs_at_bot_at_top

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/


section EventuallyMulDivCancel

variable {u v : α → 𝕜}

theorem IsOWith.eventually_mul_div_cancel (h : IsOWith c u v l) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy =>
    div_mul_cancel_of_imp fun hv => by
      simpa [hv] using hy

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsO.eventually_mul_div_cancel (h : IsO u v l) : u / v * v =ᶠ[l] u :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsOₓ.eventually_mul_div_cancel (h : IsOₓ u v l) : u / v * v =ᶠ[l] u :=
  (h.forall_is_O_with zero_lt_one).eventually_mul_div_cancel

end EventuallyMulDivCancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/


section ExistsMulEq

variable {u v : α → 𝕜}

/-- If `∥φ∥` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
theorem is_O_with_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c) (h : u =ᶠ[l] φ * v) : IsOWith c u v l := by
  unfold is_O_with
  refine' h.symm.rw (fun x a => ∥a∥ ≤ c * ∥v x∥) (hφ.mono fun x hx => _)
  simp only [norm_mul, Pi.mul_apply]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem is_O_with_iff_exists_eq_mul (hc : 0 ≤ c) :
    IsOWith c u v l ↔ ∃ (φ : α → 𝕜)(hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c), u =ᶠ[l] φ * v := by
  constructor
  · intro h
    use fun x => u x / v x
    refine' ⟨eventually.mono h.bound fun y hy => _, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy
    
  · rintro ⟨φ, hφ, h⟩
    exact is_O_with_of_eq_mul φ hφ h
    

theorem IsOWith.exists_eq_mul (h : IsOWith c u v l) (hc : 0 ≤ c) :
    ∃ (φ : α → 𝕜)(hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c), u =ᶠ[l] φ * v :=
  (is_O_with_iff_exists_eq_mul hc).mp h

theorem is_O_iff_exists_eq_mul : IsO u v l ↔ ∃ (φ : α → 𝕜)(hφ : l.IsBoundedUnder (· ≤ ·) (norm ∘ φ)), u =ᶠ[l] φ * v :=
  by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
    
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact is_O_iff_is_O_with.2 ⟨c, is_O_with_of_eq_mul φ hφ huvφ⟩
    

alias is_O_iff_exists_eq_mul ↔ Asymptotics.IsO.exists_eq_mul _

theorem is_o_iff_exists_eq_mul : IsOₓ u v l ↔ ∃ (φ : α → 𝕜)(hφ : Tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v := by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
    
  · unfold is_o
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedGroup.tendsto_nhds_zero] at hφ
    exact is_O_with_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_ltₓ) huvφ
    

alias is_o_iff_exists_eq_mul ↔ Asymptotics.IsOₓ.exists_eq_mul _

end ExistsMulEq

/-! ### Miscellanous lemmas -/


theorem div_is_bounded_under_of_is_O {α : Type _} {l : Filter α} {f g : α → 𝕜} (h : IsO f g l) :
    IsBoundedUnder (· ≤ ·) l fun x => ∥f x / g x∥ := by
  obtain ⟨c, hc⟩ := is_O_iff.mp h
  refine' ⟨max c 0, eventually_map.2 (Filter.mem_of_superset hc fun x hx => _)⟩
  simp only [mem_set_of_eq, norm_div] at hx⊢
  by_cases' hgx : g x = 0
  · rw [hgx, norm_zero, div_zero, le_max_iff]
    exact Or.inr le_rfl
    
  · exact le_max_iff.2 (Or.inl ((div_le_iff (norm_pos_iff.2 hgx)).2 hx))
    

theorem is_O_iff_div_is_bounded_under {α : Type _} {l : Filter α} {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    IsO f g l ↔ IsBoundedUnder (· ≤ ·) l fun x => ∥f x / g x∥ := by
  refine' ⟨div_is_bounded_under_of_is_O, fun h => _⟩
  obtain ⟨c, hc⟩ := h
  rw [Filter.eventually_iff] at hgf hc
  simp only [mem_set_of_eq, mem_map, norm_div] at hc
  refine' is_O_iff.2 ⟨c, Filter.eventually_of_mem (inter_mem hgf hc) fun x hx => _⟩
  by_cases' hgx : g x = 0
  · simp [hx.1 hgx, hgx]
    
  · refine' (div_le_iff (norm_pos_iff.2 hgx)).mp hx.2
    

theorem is_O_of_div_tendsto_nhds {α : Type _} {l : Filter α} {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜)
    (H : Filter.Tendsto (f / g) l (𝓝 c)) : IsO f g l :=
  (is_O_iff_div_is_bounded_under hgf).2 <| H.norm.is_bounded_under_le

theorem IsOₓ.tendsto_zero_of_tendsto {α E 𝕜 : Type _} [NormedGroup E] [NormedField 𝕜] {u : α → E} {v : α → 𝕜}
    {l : Filter α} {y : 𝕜} (huv : IsOₓ u v l) (hv : Tendsto v l (𝓝 y)) : Tendsto u l (𝓝 0) := by
  suffices h : is_o u (fun x => (1 : 𝕜)) l
  · rwa [is_o_one_iff] at h
    
  exact huv.trans_is_O (is_O_one_of_tendsto 𝕜 hv)

theorem is_o_pow_pow {m n : ℕ} (h : m < n) : IsOₓ (fun x : 𝕜 => x ^ n) (fun x => x ^ m) (𝓝 0) := by
  let p := n - m
  have nmp : n = m + p := (add_tsub_cancel_of_le (le_of_ltₓ h)).symm
  have : (fun x : 𝕜 => x ^ m) = fun x => x ^ m * 1 := by
    simp only [mul_oneₓ]
  simp only [this, pow_addₓ, nmp]
  refine' is_O.mul_is_o (is_O_refl _ _) ((is_o_one_iff _).2 _)
  convert (continuous_pow p).Tendsto (0 : 𝕜)
  exact (zero_pow (tsub_pos_of_lt h)).symm

theorem is_o_norm_pow_norm_pow {m n : ℕ} (h : m < n) : IsOₓ (fun x : E' => ∥x∥ ^ n) (fun x => ∥x∥ ^ m) (𝓝 (0 : E')) :=
  (is_o_pow_pow h).comp_tendsto tendsto_norm_zero

theorem is_o_pow_id {n : ℕ} (h : 1 < n) : IsOₓ (fun x : 𝕜 => x ^ n) (fun x => x) (𝓝 0) := by
  convert is_o_pow_pow h
  simp only [pow_oneₓ]

theorem is_o_norm_pow_id {n : ℕ} (h : 1 < n) : IsOₓ (fun x : E' => ∥x∥ ^ n) (fun x => x) (𝓝 0) := by
  simpa only [pow_oneₓ, is_o_norm_right] using @is_o_norm_pow_norm_pow E' _ _ _ h

theorem IsOWith.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : IsOWith c f₁ f₂ l) (hc : c < 1) :
    IsOWith (1 / (1 - c)) f₂ (fun x => f₂ x - f₁ x) l :=
  is_O_with.of_bound <|
    (mem_of_superset h.bound) fun x hx => by
      simp only [mem_set_of_eq] at hx⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff, mul_sub, mul_oneₓ, mul_comm]
      · exact le_transₓ (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
        
      · exact sub_pos.2 hc
        

theorem IsOWith.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : IsOWith c f₁ f₂ l) (hc : c < 1) :
    IsOWith (1 / (1 - c)) f₂ (fun x => f₁ x + f₂ x) l :=
  (h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (fun x => rfl) fun x => by
    rw [neg_sub, sub_neg_eq_add]

theorem IsOₓ.right_is_O_sub {f₁ f₂ : α → E'} (h : IsOₓ f₁ f₂ l) : IsO f₂ (fun x => f₂ x - f₁ x) l :=
  ((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).IsO

theorem IsOₓ.right_is_O_add {f₁ f₂ : α → E'} (h : IsOₓ f₁ f₂ l) : IsO f₂ (fun x => f₁ x + f₂ x) l :=
  ((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).IsO

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`∥f x∥ ≤ C * ∥g x∥` whenever `g x ≠ 0`. -/
theorem bound_of_is_O_cofinite (h : IsO f g'' cofinite) : ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ∥f x∥ ≤ C * ∥g'' x∥ := by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [is_O_with, eventually_cofinite] at hC
  rcases(hC.to_finset.image fun x => ∥f x∥ / ∥g'' x∥).exists_le with ⟨C', hC'⟩
  have : ∀ x, C * ∥g'' x∥ < ∥f x∥ → ∥f x∥ / ∥g'' x∥ ≤ C' := by
    simpa using hC'
  refine' ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => _⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_leₓ]
  exact fun hx => (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)

theorem is_O_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) : IsO f'' g'' cofinite ↔ ∃ C, ∀ x, ∥f'' x∥ ≤ C * ∥g'' x∥ :=
  ⟨fun h' =>
    let ⟨C, C₀, hC⟩ := bound_of_is_O_cofinite h'
    ⟨C, fun x =>
      if hx : g'' x = 0 then by
        simp [h _ hx, hx]
      else hC hx⟩,
    fun h => (is_O_top.2 h).mono le_top⟩

theorem bound_of_is_O_nat_at_top {f : ℕ → E} {g'' : ℕ → E''} (h : IsO f g'' atTop) :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ∥f x∥ ≤ C * ∥g'' x∥ :=
  bound_of_is_O_cofinite <| by
    rwa [Nat.cofinite_eq_at_top]

theorem is_O_nat_at_top_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    IsO f g atTop ↔ ∃ C, ∀ x, ∥f x∥ ≤ C * ∥g x∥ := by
  rw [← Nat.cofinite_eq_at_top, is_O_cofinite_iff h]

theorem is_O_one_nat_at_top_iff {f : ℕ → E''} : IsO f (fun n => 1 : ℕ → ℝ) atTop ↔ ∃ C, ∀ n, ∥f n∥ ≤ C :=
  Iff.trans (is_O_nat_at_top_iff fun n h => (one_ne_zero h).elim) <| by
    simp only [norm_one, mul_oneₓ]

theorem is_O_with_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedGroup (E' i)] {f : α → ∀ i, E' i} {C : ℝ}
    (hC : 0 ≤ C) : IsOWith C f g' l ↔ ∀ i, IsOWith C (fun x => f x i) g' l := by
  have : ∀ x, 0 ≤ C * ∥g' x∥ := fun x => mul_nonneg hC (norm_nonneg _)
  simp only [is_O_with_iff, pi_norm_le_iff (this _), eventually_all]

@[simp]
theorem is_O_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedGroup (E' i)] {f : α → ∀ i, E' i} :
    IsO f g' l ↔ ∀ i, IsO (fun x => f x i) g' l := by
  simp only [is_O_iff_eventually_is_O_with, ← eventually_all]
  exact eventually_congr (eventually_at_top.2 ⟨0, fun c => is_O_with_pi⟩)

@[simp]
theorem is_o_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedGroup (E' i)] {f : α → ∀ i, E' i} :
    IsOₓ f g' l ↔ ∀ i, IsOₓ (fun x => f x i) g' l := by
  simp (config := { contextual := true })only [is_o, is_O_with_pi, le_of_ltₓ]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩

end Asymptotics

open Asymptotics

theorem summable_of_is_O {ι E} [NormedGroup E] [CompleteSpace E] {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : IsO f g cofinite) : Summable f :=
  let ⟨C, hC⟩ := h.IsOWith
  summable_of_norm_bounded_eventually (fun x => C * ∥g x∥) (hg.abs.mul_left _) hC.bound

theorem summable_of_is_O_nat {E} [NormedGroup E] [CompleteSpace E] {f : ℕ → E} {g : ℕ → ℝ} (hg : Summable g)
    (h : IsO f g atTop) : Summable f :=
  summable_of_is_O hg <| Nat.cofinite_eq_at_top.symm ▸ h

namespace LocalHomeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [HasNorm E] {F : Type _} [HasNorm F]

/-- Transfer `is_O_with` over a `local_homeomorph`. -/
theorem is_O_with_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.Target) {f : β → E} {g : β → F} {C : ℝ} :
    IsOWith C f g (𝓝 b) ↔ IsOWith C (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
  ⟨fun h =>
    h.comp_tendsto <| by
      convert e.continuous_at (e.map_target hb)
      exact (e.right_inv hb).symm,
    fun h =>
    (h.comp_tendsto (e.continuous_at_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun x hx => congr_argₓ f hx)
      ((e.eventually_right_inverse hb).mono fun x hx => congr_argₓ g hx)⟩

/-- Transfer `is_O` over a `local_homeomorph`. -/
theorem is_O_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.Target) {f : β → E} {g : β → F} :
    IsO f g (𝓝 b) ↔ IsO (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) := by
  unfold is_O
  exact exists_congr fun C => e.is_O_with_congr hb

/-- Transfer `is_o` over a `local_homeomorph`. -/
theorem is_o_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.Target) {f : β → E} {g : β → F} :
    IsOₓ f g (𝓝 b) ↔ IsOₓ (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) := by
  unfold is_o
  exact forall₂_congrₓ fun c hc => e.is_O_with_congr hb

end LocalHomeomorph

namespace Homeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [HasNorm E] {F : Type _} [HasNorm F]

open Asymptotics

/-- Transfer `is_O_with` over a `homeomorph`. -/
theorem is_O_with_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    IsOWith C f g (𝓝 b) ↔ IsOWith C (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
  e.toLocalHomeomorph.is_O_with_congr trivialₓ

/-- Transfer `is_O` over a `homeomorph`. -/
theorem is_O_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} : IsO f g (𝓝 b) ↔ IsO (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) :=
  by
  unfold is_O
  exact exists_congr fun C => e.is_O_with_congr

/-- Transfer `is_o` over a `homeomorph`. -/
theorem is_o_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    IsOₓ f g (𝓝 b) ↔ IsOₓ (f ∘ e) (g ∘ e) (𝓝 (e.symm b)) := by
  unfold is_o
  exact forall₂_congrₓ fun c hc => e.is_O_with_congr

end Homeomorph

