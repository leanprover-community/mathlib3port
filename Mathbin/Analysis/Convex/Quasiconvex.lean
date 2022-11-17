/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Analysis.Convex.Function

/-!
# Quasiconvex and quasiconcave functions

This file defines quasiconvexity, quasiconcavity and quasilinearity of functions, which are
generalizations of unimodality and monotonicity. Convexity implies quasiconvexity, concavity implies
quasiconcavity, and monotonicity implies quasilinearity.

## Main declarations

* `quasiconvex_on 𝕜 s f`: Quasiconvexity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex.
* `quasiconcave_on 𝕜 s f`: Quasiconcavity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex.
* `quasilinear_on 𝕜 s f`: Quasilinearity of the function `f` on the set `s` with scalars `𝕜`. This
  means that `f` is both quasiconvex and quasiconcave.

## TODO

Prove that a quasilinear function between two linear orders is either monotone or antitone. This is
not hard but quite a pain to go about as there are many cases to consider.

## References

* https://en.wikipedia.org/wiki/Quasiconvex_function
-/


open Function OrderDual Set

variable {𝕜 E F β : Type _}

section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section OrderedAddCommMonoid

variable (𝕜) [OrderedAddCommMonoid β] [HasSmul 𝕜 E] (s : Set E) (f : E → β)

/-- A function is quasiconvex if all its sublevels are convex.
This means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex. -/
def QuasiconvexOn : Prop :=
  ∀ r, Convex 𝕜 ({ x ∈ s | f x ≤ r })
#align quasiconvex_on QuasiconvexOn

/-- A function is quasiconcave if all its superlevels are convex.
This means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex. -/
def QuasiconcaveOn : Prop :=
  ∀ r, Convex 𝕜 ({ x ∈ s | r ≤ f x })
#align quasiconcave_on QuasiconcaveOn

/-- A function is quasilinear if it is both quasiconvex and quasiconcave.
This means that, for all `r`,
the sets `{x ∈ s | f x ≤ r}` and `{x ∈ s | r ≤ f x}` are `𝕜`-convex. -/
def QuasilinearOn : Prop :=
  QuasiconvexOn 𝕜 s f ∧ QuasiconcaveOn 𝕜 s f
#align quasilinear_on QuasilinearOn

variable {𝕜 s f}

theorem QuasiconvexOn.dual : QuasiconvexOn 𝕜 s f → QuasiconcaveOn 𝕜 s (to_dual ∘ f) :=
  id
#align quasiconvex_on.dual QuasiconvexOn.dual

theorem QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f → QuasiconvexOn 𝕜 s (to_dual ∘ f) :=
  id
#align quasiconcave_on.dual QuasiconcaveOn.dual

theorem QuasilinearOn.dual : QuasilinearOn 𝕜 s f → QuasilinearOn 𝕜 s (to_dual ∘ f) :=
  And.symm
#align quasilinear_on.dual QuasilinearOn.dual

theorem Convex.quasiconvex_on_of_convex_le (hs : Convex 𝕜 s) (h : ∀ r, Convex 𝕜 { x | f x ≤ r }) :
    QuasiconvexOn 𝕜 s f := fun r => hs.inter (h r)
#align convex.quasiconvex_on_of_convex_le Convex.quasiconvex_on_of_convex_le

theorem Convex.quasiconcave_on_of_convex_ge (hs : Convex 𝕜 s) (h : ∀ r, Convex 𝕜 { x | r ≤ f x }) :
    QuasiconcaveOn 𝕜 s f :=
  @Convex.quasiconvex_on_of_convex_le 𝕜 E βᵒᵈ _ _ _ _ _ _ hs h
#align convex.quasiconcave_on_of_convex_ge Convex.quasiconcave_on_of_convex_ge

theorem QuasiconvexOn.convex [IsDirected β (· ≤ ·)] (hf : QuasiconvexOn 𝕜 s f) : Convex 𝕜 s :=
  fun x hx y hy a b ha hb hab =>
  let ⟨z, hxz, hyz⟩ := exists_ge_ge (f x) (f y)
  (hf _ ⟨hx, hxz⟩ ⟨hy, hyz⟩ ha hb hab).1
#align quasiconvex_on.convex QuasiconvexOn.convex

theorem QuasiconcaveOn.convex [IsDirected β (· ≥ ·)] (hf : QuasiconcaveOn 𝕜 s f) : Convex 𝕜 s :=
  hf.dual.Convex
#align quasiconcave_on.convex QuasiconcaveOn.convex

end OrderedAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid β]

section HasSmul

variable [HasSmul 𝕜 E] {s : Set E} {f g : E → β}

theorem QuasiconvexOn.sup (hf : QuasiconvexOn 𝕜 s f) (hg : QuasiconvexOn 𝕜 s g) : QuasiconvexOn 𝕜 s (f ⊔ g) := by
  intro r
  simp_rw [Pi.sup_def, sup_le_iff, Set.sep_and]
  exact (hf r).inter (hg r)
#align quasiconvex_on.sup QuasiconvexOn.sup

theorem QuasiconcaveOn.inf (hf : QuasiconcaveOn 𝕜 s f) (hg : QuasiconcaveOn 𝕜 s g) : QuasiconcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg
#align quasiconcave_on.inf QuasiconcaveOn.inf

theorem quasiconvex_on_iff_le_max :
    QuasiconvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ max (f x) (f y) :=
  ⟨fun hf =>
    ⟨hf.Convex, fun x hx y hy a b ha hb hab => (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).2⟩,
    fun hf r x hx y hy a b ha hb hab => ⟨hf.1 hx.1 hy.1 ha hb hab, (hf.2 hx.1 hy.1 ha hb hab).trans $ max_le hx.2 hy.2⟩⟩
#align quasiconvex_on_iff_le_max quasiconvex_on_iff_le_max

theorem quasiconcave_on_iff_min_le :
    QuasiconcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → min (f x) (f y) ≤ f (a • x + b • y) :=
  @quasiconvex_on_iff_le_max 𝕜 E βᵒᵈ _ _ _ _ _ _
#align quasiconcave_on_iff_min_le quasiconcave_on_iff_min_le

theorem quasilinear_on_iff_mem_interval :
    QuasilinearOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x⦄,
          x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ∈ interval (f x) (f y) :=
  by
  rw [QuasilinearOn, quasiconvex_on_iff_le_max, quasiconcave_on_iff_min_le, and_and_and_comm, and_self_iff]
  apply and_congr_right'
  simp_rw [← forall_and, interval, mem_Icc, and_comm']
#align quasilinear_on_iff_mem_interval quasilinear_on_iff_mem_interval

theorem QuasiconvexOn.convex_lt (hf : QuasiconvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) := by
  refine' fun x hx y hy a b ha hb hab => _
  have h := hf _ ⟨hx.1, le_max_left _ _⟩ ⟨hy.1, le_max_right _ _⟩ ha hb hab
  exact ⟨h.1, h.2.trans_lt $ max_lt hx.2 hy.2⟩
#align quasiconvex_on.convex_lt QuasiconvexOn.convex_lt

theorem QuasiconcaveOn.convex_gt (hf : QuasiconcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r
#align quasiconcave_on.convex_gt QuasiconcaveOn.convex_gt

end HasSmul

section OrderedSmul

variable [HasSmul 𝕜 E] [Module 𝕜 β] [OrderedSmul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.quasiconvex_on (hf : ConvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le
#align convex_on.quasiconvex_on ConvexOn.quasiconvex_on

theorem ConcaveOn.quasiconcave_on (hf : ConcaveOn 𝕜 s f) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge
#align concave_on.quasiconcave_on ConcaveOn.quasiconcave_on

end OrderedSmul

end LinearOrderedAddCommMonoid

end AddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [OrderedAddCommMonoid β] [Module 𝕜 E] [OrderedSmul 𝕜 E] {s : Set E} {f : E → β}

theorem MonotoneOn.quasiconvex_on (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs
#align monotone_on.quasiconvex_on MonotoneOn.quasiconvex_on

theorem MonotoneOn.quasiconcave_on (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs
#align monotone_on.quasiconcave_on MonotoneOn.quasiconcave_on

theorem MonotoneOn.quasilinear_on (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.QuasiconvexOn hs, hf.QuasiconcaveOn hs⟩
#align monotone_on.quasilinear_on MonotoneOn.quasilinear_on

theorem AntitoneOn.quasiconvex_on (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs
#align antitone_on.quasiconvex_on AntitoneOn.quasiconvex_on

theorem AntitoneOn.quasiconcave_on (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs
#align antitone_on.quasiconcave_on AntitoneOn.quasiconcave_on

theorem AntitoneOn.quasilinear_on (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.QuasiconvexOn hs, hf.QuasiconcaveOn hs⟩
#align antitone_on.quasilinear_on AntitoneOn.quasilinear_on

theorem Monotone.quasiconvex_on (hf : Monotone f) : QuasiconvexOn 𝕜 univ f :=
  (hf.MonotoneOn _).QuasiconvexOn convex_univ
#align monotone.quasiconvex_on Monotone.quasiconvex_on

theorem Monotone.quasiconcave_on (hf : Monotone f) : QuasiconcaveOn 𝕜 univ f :=
  (hf.MonotoneOn _).QuasiconcaveOn convex_univ
#align monotone.quasiconcave_on Monotone.quasiconcave_on

theorem Monotone.quasilinear_on (hf : Monotone f) : QuasilinearOn 𝕜 univ f :=
  ⟨hf.QuasiconvexOn, hf.QuasiconcaveOn⟩
#align monotone.quasilinear_on Monotone.quasilinear_on

theorem Antitone.quasiconvex_on (hf : Antitone f) : QuasiconvexOn 𝕜 univ f :=
  (hf.AntitoneOn _).QuasiconvexOn convex_univ
#align antitone.quasiconvex_on Antitone.quasiconvex_on

theorem Antitone.quasiconcave_on (hf : Antitone f) : QuasiconcaveOn 𝕜 univ f :=
  (hf.AntitoneOn _).QuasiconcaveOn convex_univ
#align antitone.quasiconcave_on Antitone.quasiconcave_on

theorem Antitone.quasilinear_on (hf : Antitone f) : QuasilinearOn 𝕜 univ f :=
  ⟨hf.QuasiconvexOn, hf.QuasiconcaveOn⟩
#align antitone.quasilinear_on Antitone.quasilinear_on

end LinearOrderedAddCommMonoid

end OrderedSemiring

