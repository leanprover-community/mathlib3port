/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, FranÃ§ois Dupuis
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Tactic.FieldSimp
import Mathbin.Tactic.Linarith.Default
import Mathbin.Tactic.Ring

/-!
# Convex and concave functions

This file defines convex and concave functions in vector spaces and proves the finite Jensen
inequality. The integral version can be found in `analysis.convex.integral`.

A function `f : E â Î²` is `convex_on` a set `s` if `s` is itself a convex set, and for any two
points `x y â s`, the segment joining `(x, f x)` to `(y, f y)` is above the graph of `f`.
Equivalently, `convex_on ð f s` means that the epigraph `{p : E Ã Î² | p.1 â s â§ f p.1 â¤ p.2}` is
a convex set.

## Main declarations

* `convex_on ð s f`: The function `f` is convex on `s` with scalars `ð`.
* `concave_on ð s f`: The function `f` is concave on `s` with scalars `ð`.
* `strict_convex_on ð s f`: The function `f` is strictly convex on `s` with scalars `ð`.
* `strict_concave_on ð s f`: The function `f` is strictly concave on `s` with scalars `ð`.
-/


open Finset LinearMap Set

open BigOperators Classical Convex Pointwise

variable {ð E F Î² Î¹ : Type _}

section OrderedSemiring

variable [OrderedSemiring ð]

section AddCommMonoidâ

variable [AddCommMonoidâ E] [AddCommMonoidâ F]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid Î²]

section HasSmul

variable (ð) [HasSmul ð E] [HasSmul ð Î²] (s : Set E) (f : E â Î²)

/-- Convexity of functions -/
def ConvexOn : Prop :=
  Convex ð s â§
    â â¦x y : Eâ¦, x â s â y â s â â â¦a b : ðâ¦, 0 â¤ a â 0 â¤ b â a + b = 1 â f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y

/-- Concavity of functions -/
def ConcaveOn : Prop :=
  Convex ð s â§
    â â¦x y : Eâ¦, x â s â y â s â â â¦a b : ðâ¦, 0 â¤ a â 0 â¤ b â a + b = 1 â a â¢ f x + b â¢ f y â¤ f (a â¢ x + b â¢ y)

/-- Strict convexity of functions -/
def StrictConvexOn : Prop :=
  Convex ð s â§
    â â¦x y : Eâ¦, x â s â y â s â x â  y â â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â f (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y

/-- Strict concavity of functions -/
def StrictConcaveOn : Prop :=
  Convex ð s â§
    â â¦x y : Eâ¦, x â s â y â s â x â  y â â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â a â¢ f x + b â¢ f y < f (a â¢ x + b â¢ y)

variable {ð s f}

open OrderDual (toDual ofDual)

theorem ConvexOn.dual (hf : ConvexOn ð s f) : ConcaveOn ð s (to_dual â f) :=
  hf

theorem ConcaveOn.dual (hf : ConcaveOn ð s f) : ConvexOn ð s (to_dual â f) :=
  hf

theorem StrictConvexOn.dual (hf : StrictConvexOn ð s f) : StrictConcaveOn ð s (to_dual â f) :=
  hf

theorem StrictConcaveOn.dual (hf : StrictConcaveOn ð s f) : StrictConvexOn ð s (to_dual â f) :=
  hf

theorem convex_on_id {s : Set Î²} (hs : Convex ð s) : ConvexOn ð s id :=
  â¨hs, by
    intros
    rflâ©

theorem concave_on_id {s : Set Î²} (hs : Convex ð s) : ConcaveOn ð s id :=
  â¨hs, by
    intros
    rflâ©

theorem ConvexOn.subset {t : Set E} (hf : ConvexOn ð t f) (hst : s â t) (hs : Convex ð s) : ConvexOn ð s f :=
  â¨hs, fun x y hx hy => hf.2 (hst hx) (hst hy)â©

theorem ConcaveOn.subset {t : Set E} (hf : ConcaveOn ð t f) (hst : s â t) (hs : Convex ð s) : ConcaveOn ð s f :=
  â¨hs, fun x y hx hy => hf.2 (hst hx) (hst hy)â©

theorem StrictConvexOn.subset {t : Set E} (hf : StrictConvexOn ð t f) (hst : s â t) (hs : Convex ð s) :
    StrictConvexOn ð s f :=
  â¨hs, fun x y hx hy => hf.2 (hst hx) (hst hy)â©

theorem StrictConcaveOn.subset {t : Set E} (hf : StrictConcaveOn ð t f) (hst : s â t) (hs : Convex ð s) :
    StrictConcaveOn ð s f :=
  â¨hs, fun x y hx hy => hf.2 (hst hx) (hst hy)â©

end HasSmul

section DistribMulAction

variable [HasSmul ð E] [DistribMulAction ð Î²] {s : Set E} {f g : E â Î²}

theorem ConvexOn.add (hf : ConvexOn ð s f) (hg : ConvexOn ð s g) : ConvexOn ð s (f + g) :=
  â¨hf.1, fun x y hx hy a b ha hb hab =>
    calc
      f (a â¢ x + b â¢ y) + g (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y + (a â¢ g x + b â¢ g y) :=
        add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
      _ = a â¢ (f x + g x) + b â¢ (f y + g y) := by
        rw [smul_add, smul_add, add_add_add_commâ]
      â©

theorem ConcaveOn.add (hf : ConcaveOn ð s f) (hg : ConcaveOn ð s g) : ConcaveOn ð s (f + g) :=
  hf.dual.add hg

end DistribMulAction

section Module

variable [HasSmul ð E] [Module ð Î²] {s : Set E} {f : E â Î²}

theorem convex_on_const (c : Î²) (hs : Convex ð s) : ConvexOn ð s fun x : E => c :=
  â¨hs, fun x y _ _ a b _ _ hab => (Convex.combo_self hab c).Geâ©

theorem concave_on_const (c : Î²) (hs : Convex ð s) : ConcaveOn ð s fun x : E => c :=
  @convex_on_const _ _ Î²áµáµ _ _ _ _ _ _ c hs

theorem convex_on_of_convex_epigraph (h : Convex ð { p : E Ã Î² | p.1 â s â§ f p.1 â¤ p.2 }) : ConvexOn ð s f :=
  â¨fun x y hx hy a b ha hb hab => (@h (x, f x) (y, f y) â¨hx, le_rflâ© â¨hy, le_rflâ© a b ha hb hab).1,
    fun x y hx hy a b ha hb hab => (@h (x, f x) (y, f y) â¨hx, le_rflâ© â¨hy, le_rflâ© a b ha hb hab).2â©

theorem concave_on_of_convex_hypograph (h : Convex ð { p : E Ã Î² | p.1 â s â§ p.2 â¤ f p.1 }) : ConcaveOn ð s f :=
  @convex_on_of_convex_epigraph ð E Î²áµáµ _ _ _ _ _ _ _ h

end Module

section OrderedSmul

variable [HasSmul ð E] [Module ð Î²] [OrderedSmul ð Î²] {s : Set E} {f : E â Î²}

theorem ConvexOn.convex_le (hf : ConvexOn ð s f) (r : Î²) : Convex ð ({ x â s | f x â¤ r }) :=
  fun x y hx hy a b ha hb hab =>
  â¨hf.1 hx.1 hy.1 ha hb hab,
    calc
      f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y := hf.2 hx.1 hy.1 ha hb hab
      _ â¤ a â¢ r + b â¢ r := add_le_add (smul_le_smul_of_nonneg hx.2 ha) (smul_le_smul_of_nonneg hy.2 hb)
      _ = r := Convex.combo_self hab r
      â©

theorem ConcaveOn.convex_ge (hf : ConcaveOn ð s f) (r : Î²) : Convex ð ({ x â s | r â¤ f x }) :=
  hf.dual.convex_le r

theorem ConvexOn.convex_epigraph (hf : ConvexOn ð s f) : Convex ð { p : E Ã Î² | p.1 â s â§ f p.1 â¤ p.2 } := by
  rintro â¨x, râ© â¨y, tâ© â¨hx, hrâ© â¨hy, htâ© a b ha hb hab
  refine' â¨hf.1 hx hy ha hb hab, _â©
  calc f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y := hf.2 hx hy ha hb hab _ â¤ a â¢ r + b â¢ t :=
      add_le_add (smul_le_smul_of_nonneg hr ha) (smul_le_smul_of_nonneg ht hb)

theorem ConcaveOn.convex_hypograph (hf : ConcaveOn ð s f) : Convex ð { p : E Ã Î² | p.1 â s â§ p.2 â¤ f p.1 } :=
  hf.dual.convex_epigraph

theorem convex_on_iff_convex_epigraph : ConvexOn ð s f â Convex ð { p : E Ã Î² | p.1 â s â§ f p.1 â¤ p.2 } :=
  â¨ConvexOn.convex_epigraph, convex_on_of_convex_epigraphâ©

theorem concave_on_iff_convex_hypograph : ConcaveOn ð s f â Convex ð { p : E Ã Î² | p.1 â s â§ p.2 â¤ f p.1 } :=
  @convex_on_iff_convex_epigraph ð E Î²áµáµ _ _ _ _ _ _ _ f

end OrderedSmul

section Module

variable [Module ð E] [HasSmul ð Î²] {s : Set E} {f : E â Î²}

/-- Right translation preserves convexity. -/
theorem ConvexOn.translate_right (hf : ConvexOn ð s f) (c : E) :
    ConvexOn ð ((fun z => c + z) â»Â¹' s) (f â fun z => c + z) :=
  â¨hf.1.translate_preimage_right _, fun x y hx hy a b ha hb hab =>
    calc
      f (c + (a â¢ x + b â¢ y)) = f (a â¢ (c + x) + b â¢ (c + y)) := by
        rw [smul_add, smul_add, add_add_add_commâ, Convex.combo_self hab]
      _ â¤ a â¢ f (c + x) + b â¢ f (c + y) := hf.2 hx hy ha hb hab
      â©

/-- Right translation preserves concavity. -/
theorem ConcaveOn.translate_right (hf : ConcaveOn ð s f) (c : E) :
    ConcaveOn ð ((fun z => c + z) â»Â¹' s) (f â fun z => c + z) :=
  hf.dual.translate_right _

/-- Left translation preserves convexity. -/
theorem ConvexOn.translate_left (hf : ConvexOn ð s f) (c : E) :
    ConvexOn ð ((fun z => c + z) â»Â¹' s) (f â fun z => z + c) := by
  simpa only [â add_commâ] using hf.translate_right _

/-- Left translation preserves concavity. -/
theorem ConcaveOn.translate_left (hf : ConcaveOn ð s f) (c : E) :
    ConcaveOn ð ((fun z => c + z) â»Â¹' s) (f â fun z => z + c) :=
  hf.dual.translate_left _

end Module

section Module

variable [Module ð E] [Module ð Î²]

theorem convex_on_iff_forall_pos {s : Set E} {f : E â Î²} :
    ConvexOn ð s f â
      Convex ð s â§
        â â¦x y : Eâ¦, x â s â y â s â â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y :=
  by
  refine'
    and_congr_right' â¨fun h x y hx hy a b ha hb hab => h hx hy ha.le hb.le hab, fun h x y hx hy a b ha hb hab => _â©
  obtain rfl | ha' := ha.eq_or_lt
  Â· rw [zero_addâ] at hab
    subst b
    simp_rw [zero_smul, zero_addâ, one_smul]
    
  obtain rfl | hb' := hb.eq_or_lt
  Â· rw [add_zeroâ] at hab
    subst a
    simp_rw [zero_smul, add_zeroâ, one_smul]
    
  exact h hx hy ha' hb' hab

theorem concave_on_iff_forall_pos {s : Set E} {f : E â Î²} :
    ConcaveOn ð s f â
      Convex ð s â§
        â â¦x y : Eâ¦, x â s â y â s â â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â a â¢ f x + b â¢ f y â¤ f (a â¢ x + b â¢ y) :=
  @convex_on_iff_forall_pos ð E Î²áµáµ _ _ _ _ _ _ _

theorem convex_on_iff_pairwise_pos {s : Set E} {f : E â Î²} :
    ConvexOn ð s f â
      Convex ð s â§
        s.Pairwise fun x y => â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y :=
  by
  rw [convex_on_iff_forall_pos]
  refine' and_congr_right' â¨fun h x hx y hy _ a b ha hb hab => h hx hy ha hb hab, fun h x y hx hy a b ha hb hab => _â©
  obtain rfl | hxy := eq_or_ne x y
  Â· rw [Convex.combo_self hab, Convex.combo_self hab]
    
  exact h hx hy hxy ha hb hab

theorem concave_on_iff_pairwise_pos {s : Set E} {f : E â Î²} :
    ConcaveOn ð s f â
      Convex ð s â§
        s.Pairwise fun x y => â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â a â¢ f x + b â¢ f y â¤ f (a â¢ x + b â¢ y) :=
  @convex_on_iff_pairwise_pos ð E Î²áµáµ _ _ _ _ _ _ _

/-- A linear map is convex. -/
theorem LinearMap.convex_on (f : E ââ[ð] Î²) {s : Set E} (hs : Convex ð s) : ConvexOn ð s f :=
  â¨hs, fun _ _ _ _ _ _ _ _ _ => by
    rw [f.map_add, f.map_smul, f.map_smul]â©

/-- A linear map is concave. -/
theorem LinearMap.concave_on (f : E ââ[ð] Î²) {s : Set E} (hs : Convex ð s) : ConcaveOn ð s f :=
  â¨hs, fun _ _ _ _ _ _ _ _ _ => by
    rw [f.map_add, f.map_smul, f.map_smul]â©

theorem StrictConvexOn.convex_on {s : Set E} {f : E â Î²} (hf : StrictConvexOn ð s f) : ConvexOn ð s f :=
  convex_on_iff_pairwise_pos.mpr â¨hf.1, fun x hx y hy hxy a b ha hb hab => (hf.2 hx hy hxy ha hb hab).leâ©

theorem StrictConcaveOn.concave_on {s : Set E} {f : E â Î²} (hf : StrictConcaveOn ð s f) : ConcaveOn ð s f :=
  hf.dual.ConvexOn

section OrderedSmul

variable [OrderedSmul ð Î²] {s : Set E} {f : E â Î²}

theorem StrictConvexOn.convex_lt (hf : StrictConvexOn ð s f) (r : Î²) : Convex ð ({ x â s | f x < r }) :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    â¨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y := hf.2 hx.1 hy.1 hxy ha hb hab
        _ â¤ a â¢ r + b â¢ r := add_le_add (smul_lt_smul_of_pos hx.2 ha).le (smul_lt_smul_of_pos hy.2 hb).le
        _ = r := Convex.combo_self hab r
        â©

theorem StrictConcaveOn.convex_gt (hf : StrictConcaveOn ð s f) (r : Î²) : Convex ð ({ x â s | r < f x }) :=
  hf.dual.convex_lt r

end OrderedSmul

section LinearOrderâ

variable [LinearOrderâ E] {s : Set E} {f : E â Î²}

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is convex, it suffices to
verify the inequality `f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y` only for `x < y` and positive `a`,
`b`. The main use case is `E = ð` however one can apply it, e.g., to `ð^n` with lexicographic order.
-/
theorem LinearOrderâ.convex_on_of_lt (hs : Convex ð s)
    (hf :
      â â¦x y : Eâ¦,
        x â s â y â s â x < y â â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y) :
    ConvexOn ð s f := by
  refine' convex_on_iff_pairwise_pos.2 â¨hs, fun x hx y hy hxy a b ha hb hab => _â©
  wlog h : x â¤ y using x y a b, y x b a
  Â· exact le_totalâ _ _
    
  exact hf hx hy (h.lt_of_ne hxy) ha hb hab

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is concave it suffices to
verify the inequality `a â¢ f x + b â¢ f y â¤ f (a â¢ x + b â¢ y)` for `x < y` and positive `a`, `b`. The
main use case is `E = â` however one can apply it, e.g., to `â^n` with lexicographic order. -/
theorem LinearOrderâ.concave_on_of_lt (hs : Convex ð s)
    (hf :
      â â¦x y : Eâ¦,
        x â s â y â s â x < y â â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â a â¢ f x + b â¢ f y â¤ f (a â¢ x + b â¢ y)) :
    ConcaveOn ð s f :=
  @LinearOrderâ.convex_on_of_lt _ _ Î²áµáµ _ _ _ _ _ _ s f hs hf

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly convex, it suffices
to verify the inequality `f (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y` for `x < y` and positive `a`, `b`.
The main use case is `E = ð` however one can apply it, e.g., to `ð^n` with lexicographic order. -/
theorem LinearOrderâ.strict_convex_on_of_lt (hs : Convex ð s)
    (hf :
      â â¦x y : Eâ¦,
        x â s â y â s â x < y â â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â f (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y) :
    StrictConvexOn ð s f := by
  refine' â¨hs, fun x y hx hy hxy a b ha hb hab => _â©
  wlog h : x â¤ y using x y a b, y x b a
  Â· exact le_totalâ _ _
    
  exact hf hx hy (h.lt_of_ne hxy) ha hb hab

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly concave it suffices
to verify the inequality `a â¢ f x + b â¢ f y < f (a â¢ x + b â¢ y)` for `x < y` and positive `a`, `b`.
The main use case is `E = ð` however one can apply it, e.g., to `ð^n` with lexicographic order. -/
theorem LinearOrderâ.strict_concave_on_of_lt (hs : Convex ð s)
    (hf :
      â â¦x y : Eâ¦,
        x â s â y â s â x < y â â â¦a b : ðâ¦, 0 < a â 0 < b â a + b = 1 â a â¢ f x + b â¢ f y < f (a â¢ x + b â¢ y)) :
    StrictConcaveOn ð s f :=
  @LinearOrderâ.strict_convex_on_of_lt _ _ Î²áµáµ _ _ _ _ _ _ _ _ hs hf

end LinearOrderâ

end Module

section Module

variable [Module ð E] [Module ð F] [HasSmul ð Î²]

/-- If `g` is convex on `s`, so is `(f â g)` on `f â»Â¹' s` for a linear `f`. -/
theorem ConvexOn.comp_linear_map {f : F â Î²} {s : Set F} (hf : ConvexOn ð s f) (g : E ââ[ð] F) :
    ConvexOn ð (g â»Â¹' s) (f â g) :=
  â¨hf.1.linear_preimage _, fun x y hx hy a b ha hb hab =>
    calc
      f (g (a â¢ x + b â¢ y)) = f (a â¢ g x + b â¢ g y) := by
        rw [g.map_add, g.map_smul, g.map_smul]
      _ â¤ a â¢ f (g x) + b â¢ f (g y) := hf.2 hx hy ha hb hab
      â©

/-- If `g` is concave on `s`, so is `(g â f)` on `f â»Â¹' s` for a linear `f`. -/
theorem ConcaveOn.comp_linear_map {f : F â Î²} {s : Set F} (hf : ConcaveOn ð s f) (g : E ââ[ð] F) :
    ConcaveOn ð (g â»Â¹' s) (f â g) :=
  hf.dual.comp_linear_map g

end Module

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid Î²]

section DistribMulAction

variable [HasSmul ð E] [DistribMulAction ð Î²] {s : Set E} {f g : E â Î²}

theorem StrictConvexOn.add_convex_on (hf : StrictConvexOn ð s f) (hg : ConvexOn ð s g) : StrictConvexOn ð s (f + g) :=
  â¨hf.1, fun x y hx hy hxy a b ha hb hab =>
    calc
      f (a â¢ x + b â¢ y) + g (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y + (a â¢ g x + b â¢ g y) :=
        add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
      _ = a â¢ (f x + g x) + b â¢ (f y + g y) := by
        rw [smul_add, smul_add, add_add_add_commâ]
      â©

theorem ConvexOn.add_strict_convex_on (hf : ConvexOn ð s f) (hg : StrictConvexOn ð s g) : StrictConvexOn ð s (f + g) :=
  add_commâ g f â¸ hg.add_convex_on hf

theorem StrictConvexOn.add (hf : StrictConvexOn ð s f) (hg : StrictConvexOn ð s g) : StrictConvexOn ð s (f + g) :=
  â¨hf.1, fun x y hx hy hxy a b ha hb hab =>
    calc
      f (a â¢ x + b â¢ y) + g (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y + (a â¢ g x + b â¢ g y) :=
        add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
      _ = a â¢ (f x + g x) + b â¢ (f y + g y) := by
        rw [smul_add, smul_add, add_add_add_commâ]
      â©

theorem StrictConcaveOn.add_concave_on (hf : StrictConcaveOn ð s f) (hg : ConcaveOn ð s g) :
    StrictConcaveOn ð s (f + g) :=
  hf.dual.add_convex_on hg.dual

theorem ConcaveOn.add_strict_concave_on (hf : ConcaveOn ð s f) (hg : StrictConcaveOn ð s g) :
    StrictConcaveOn ð s (f + g) :=
  hf.dual.add_strict_convex_on hg.dual

theorem StrictConcaveOn.add (hf : StrictConcaveOn ð s f) (hg : StrictConcaveOn ð s g) : StrictConcaveOn ð s (f + g) :=
  hf.dual.add hg

end DistribMulAction

section Module

variable [Module ð E] [Module ð Î²] [OrderedSmul ð Î²] {s : Set E} {f : E â Î²}

theorem ConvexOn.convex_lt (hf : ConvexOn ð s f) (r : Î²) : Convex ð ({ x â s | f x < r }) :=
  convex_iff_forall_pos.2 fun x y hx hy a b ha hb hab =>
    â¨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y := hf.2 hx.1 hy.1 ha.le hb.le hab
        _ < a â¢ r + b â¢ r := add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hx.2 ha) (smul_le_smul_of_nonneg hy.2.le hb.le)
        _ = r := Convex.combo_self hab _
        â©

theorem ConcaveOn.convex_gt (hf : ConcaveOn ð s f) (r : Î²) : Convex ð ({ x â s | r < f x }) :=
  hf.dual.convex_lt r

theorem ConvexOn.open_segment_subset_strict_epigraph (hf : ConvexOn ð s f) (p q : E Ã Î²) (hp : p.1 â s â§ f p.1 < p.2)
    (hq : q.1 â s â§ f q.1 â¤ q.2) : OpenSegment ð p q â { p : E Ã Î² | p.1 â s â§ f p.1 < p.2 } := by
  rintro _ â¨a, b, ha, hb, hab, rflâ©
  refine' â¨hf.1 hp.1 hq.1 ha.le hb.le hab, _â©
  calc f (a â¢ p.1 + b â¢ q.1) â¤ a â¢ f p.1 + b â¢ f q.1 := hf.2 hp.1 hq.1 ha.le hb.le hab _ < a â¢ p.2 + b â¢ q.2 :=
      add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hp.2 ha) (smul_le_smul_of_nonneg hq.2 hb.le)

theorem ConcaveOn.open_segment_subset_strict_hypograph (hf : ConcaveOn ð s f) (p q : E Ã Î²) (hp : p.1 â s â§ p.2 < f p.1)
    (hq : q.1 â s â§ q.2 â¤ f q.1) : OpenSegment ð p q â { p : E Ã Î² | p.1 â s â§ p.2 < f p.1 } :=
  hf.dual.open_segment_subset_strict_epigraph p q hp hq

theorem ConvexOn.convex_strict_epigraph (hf : ConvexOn ð s f) : Convex ð { p : E Ã Î² | p.1 â s â§ f p.1 < p.2 } :=
  convex_iff_open_segment_subset.mpr fun p q hp hq => hf.open_segment_subset_strict_epigraph p q hp â¨hq.1, hq.2.leâ©

theorem ConcaveOn.convex_strict_hypograph (hf : ConcaveOn ð s f) : Convex ð { p : E Ã Î² | p.1 â s â§ p.2 < f p.1 } :=
  hf.dual.convex_strict_epigraph

end Module

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid Î²] [HasSmul ð E] [Module ð Î²] [OrderedSmul ð Î²] {s : Set E} {f g : E â Î²}

/-- The pointwise maximum of convex functions is convex. -/
theorem ConvexOn.sup (hf : ConvexOn ð s f) (hg : ConvexOn ð s g) : ConvexOn ð s (fâg) := by
  refine' â¨hf.left, fun x y hx hy a b ha hb hab => sup_le _ _â©
  Â· calc f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y := hf.right hx hy ha hb hab _ â¤ a â¢ (f xâg x) + b â¢ (f yâg y) :=
        add_le_add (smul_le_smul_of_nonneg le_sup_left ha) (smul_le_smul_of_nonneg le_sup_left hb)
    
  Â· calc g (a â¢ x + b â¢ y) â¤ a â¢ g x + b â¢ g y := hg.right hx hy ha hb hab _ â¤ a â¢ (f xâg x) + b â¢ (f yâg y) :=
        add_le_add (smul_le_smul_of_nonneg le_sup_right ha) (smul_le_smul_of_nonneg le_sup_right hb)
    

/-- The pointwise minimum of concave functions is concave. -/
theorem ConcaveOn.inf (hf : ConcaveOn ð s f) (hg : ConcaveOn ð s g) : ConcaveOn ð s (fâg) :=
  hf.dual.sup hg

/-- The pointwise maximum of strictly convex functions is strictly convex. -/
theorem StrictConvexOn.sup (hf : StrictConvexOn ð s f) (hg : StrictConvexOn ð s g) : StrictConvexOn ð s (fâg) :=
  â¨hf.left, fun x y hx hy hxy a b ha hb hab =>
    max_ltâ
      (calc
        f (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y := hf.2 hx hy hxy ha hb hab
        _ â¤ a â¢ (f xâg x) + b â¢ (f yâg y) :=
          add_le_add (smul_le_smul_of_nonneg le_sup_left ha.le) (smul_le_smul_of_nonneg le_sup_left hb.le)
        )
      (calc
        g (a â¢ x + b â¢ y) < a â¢ g x + b â¢ g y := hg.2 hx hy hxy ha hb hab
        _ â¤ a â¢ (f xâg x) + b â¢ (f yâg y) :=
          add_le_add (smul_le_smul_of_nonneg le_sup_right ha.le) (smul_le_smul_of_nonneg le_sup_right hb.le)
        )â©

/-- The pointwise minimum of strictly concave functions is strictly concave. -/
theorem StrictConcaveOn.inf (hf : StrictConcaveOn ð s f) (hg : StrictConcaveOn ð s g) : StrictConcaveOn ð s (fâg) :=
  hf.dual.sup hg

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
theorem ConvexOn.le_on_segment' (hf : ConvexOn ð s f) {x y : E} (hx : x â s) (hy : y â s) {a b : ð} (ha : 0 â¤ a)
    (hb : 0 â¤ b) (hab : a + b = 1) : f (a â¢ x + b â¢ y) â¤ max (f x) (f y) :=
  calc
    f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y := hf.2 hx hy ha hb hab
    _ â¤ a â¢ max (f x) (f y) + b â¢ max (f x) (f y) :=
      add_le_add (smul_le_smul_of_nonneg (le_max_leftâ _ _) ha) (smul_le_smul_of_nonneg (le_max_rightâ _ _) hb)
    _ = max (f x) (f y) := Convex.combo_self hab _
    

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
theorem ConcaveOn.ge_on_segment' (hf : ConcaveOn ð s f) {x y : E} (hx : x â s) (hy : y â s) {a b : ð} (ha : 0 â¤ a)
    (hb : 0 â¤ b) (hab : a + b = 1) : min (f x) (f y) â¤ f (a â¢ x + b â¢ y) :=
  hf.dual.le_on_segment' hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
theorem ConvexOn.le_on_segment (hf : ConvexOn ð s f) {x y z : E} (hx : x â s) (hy : y â s) (hz : z â [x -[ð] y]) :
    f z â¤ max (f x) (f y) :=
  let â¨a, b, ha, hb, hab, hzâ© := hz
  hz â¸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
theorem ConcaveOn.ge_on_segment (hf : ConcaveOn ð s f) {x y z : E} (hx : x â s) (hy : y â s) (hz : z â [x -[ð] y]) :
    min (f x) (f y) â¤ f z :=
  hf.dual.le_on_segment hx hy hz

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
theorem StrictConvexOn.lt_on_open_segment' (hf : StrictConvexOn ð s f) {x y : E} (hx : x â s) (hy : y â s) (hxy : x â  y)
    {a b : ð} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : f (a â¢ x + b â¢ y) < max (f x) (f y) :=
  calc
    f (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y := hf.2 hx hy hxy ha hb hab
    _ â¤ a â¢ max (f x) (f y) + b â¢ max (f x) (f y) :=
      add_le_add (smul_le_smul_of_nonneg (le_max_leftâ _ _) ha.le) (smul_le_smul_of_nonneg (le_max_rightâ _ _) hb.le)
    _ = max (f x) (f y) := Convex.combo_self hab _
    

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
theorem StrictConcaveOn.lt_on_open_segment' (hf : StrictConcaveOn ð s f) {x y : E} (hx : x â s) (hy : y â s)
    (hxy : x â  y) {a b : ð} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : min (f x) (f y) < f (a â¢ x + b â¢ y) :=
  hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
theorem StrictConvexOn.lt_on_open_segment (hf : StrictConvexOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hxy : x â  y) (hz : z â OpenSegment ð x y) : f z < max (f x) (f y) :=
  let â¨a, b, ha, hb, hab, hzâ© := hz
  hz â¸ hf.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
theorem StrictConcaveOn.lt_on_open_segment (hf : StrictConcaveOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hxy : x â  y) (hz : z â OpenSegment ð x y) : min (f x) (f y) < f z :=
  hf.dual.lt_on_open_segment hx hy hxy hz

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid

variable [LinearOrderedCancelAddCommMonoid Î²]

section OrderedSmul

variable [HasSmul ð E] [Module ð Î²] [OrderedSmul ð Î²] {s : Set E} {f g : E â Î²}

theorem ConvexOn.le_left_of_right_le' (hf : ConvexOn ð s f) {x y : E} (hx : x â s) (hy : y â s) {a b : ð} (ha : 0 < a)
    (hb : 0 â¤ b) (hab : a + b = 1) (hfy : f y â¤ f (a â¢ x + b â¢ y)) : f (a â¢ x + b â¢ y) â¤ f x :=
  le_of_not_ltâ fun h =>
    lt_irreflâ (f (a â¢ x + b â¢ y)) <|
      calc
        f (a â¢ x + b â¢ y) â¤ a â¢ f x + b â¢ f y := hf.2 hx hy ha.le hb hab
        _ < a â¢ f (a â¢ x + b â¢ y) + b â¢ f (a â¢ x + b â¢ y) :=
          add_lt_add_of_lt_of_le (smul_lt_smul_of_pos h ha) (smul_le_smul_of_nonneg hfy hb)
        _ = f (a â¢ x + b â¢ y) := Convex.combo_self hab _
        

theorem ConcaveOn.left_le_of_le_right' (hf : ConcaveOn ð s f) {x y : E} (hx : x â s) (hy : y â s) {a b : ð} (ha : 0 < a)
    (hb : 0 â¤ b) (hab : a + b = 1) (hfy : f (a â¢ x + b â¢ y) â¤ f y) : f x â¤ f (a â¢ x + b â¢ y) :=
  hf.dual.le_left_of_right_le' hx hy ha hb hab hfy

theorem ConvexOn.le_right_of_left_le' (hf : ConvexOn ð s f) {x y : E} {a b : ð} (hx : x â s) (hy : y â s) (ha : 0 â¤ a)
    (hb : 0 < b) (hab : a + b = 1) (hfx : f x â¤ f (a â¢ x + b â¢ y)) : f (a â¢ x + b â¢ y) â¤ f y := by
  rw [add_commâ] at hab hfxâ¢
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx

theorem ConcaveOn.right_le_of_le_left' (hf : ConcaveOn ð s f) {x y : E} {a b : ð} (hx : x â s) (hy : y â s) (ha : 0 â¤ a)
    (hb : 0 < b) (hab : a + b = 1) (hfx : f (a â¢ x + b â¢ y) â¤ f x) : f y â¤ f (a â¢ x + b â¢ y) :=
  hf.dual.le_right_of_left_le' hx hy ha hb hab hfx

theorem ConvexOn.le_left_of_right_le (hf : ConvexOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hz : z â OpenSegment ð x y) (hyz : f y â¤ f z) : f z â¤ f x := by
  obtain â¨a, b, ha, hb, hab, rflâ© := hz
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz

theorem ConcaveOn.left_le_of_le_right (hf : ConcaveOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hz : z â OpenSegment ð x y) (hyz : f z â¤ f y) : f x â¤ f z :=
  hf.dual.le_left_of_right_le hx hy hz hyz

theorem ConvexOn.le_right_of_left_le (hf : ConvexOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hz : z â OpenSegment ð x y) (hxz : f x â¤ f z) : f z â¤ f y := by
  obtain â¨a, b, ha, hb, hab, rflâ© := hz
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz

theorem ConcaveOn.right_le_of_le_left (hf : ConcaveOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hz : z â OpenSegment ð x y) (hxz : f z â¤ f x) : f y â¤ f z :=
  hf.dual.le_right_of_left_le hx hy hz hxz

end OrderedSmul

section Module

variable [Module ð E] [Module ð Î²] [OrderedSmul ð Î²] {s : Set E} {f g : E â Î²}

/- The following lemmas don't require `module ð E` if you add the hypothesis `x â  y`. At the time of
the writing, we decided the resulting lemmas wouldn't be useful. Feel free to reintroduce them. -/
theorem StrictConvexOn.lt_left_of_right_lt' (hf : StrictConvexOn ð s f) {x y : E} (hx : x â s) (hy : y â s) {a b : ð}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f y < f (a â¢ x + b â¢ y)) : f (a â¢ x + b â¢ y) < f x :=
  not_leâ.1 fun h =>
    lt_irreflâ (f (a â¢ x + b â¢ y)) <|
      calc
        f (a â¢ x + b â¢ y) < a â¢ f x + b â¢ f y :=
          hf.2 hx hy
            (by
              rintro rfl
              rw [Convex.combo_self hab] at hfy
              exact lt_irreflâ _ hfy)
            ha hb hab
        _ < a â¢ f (a â¢ x + b â¢ y) + b â¢ f (a â¢ x + b â¢ y) :=
          add_lt_add_of_le_of_lt (smul_le_smul_of_nonneg h ha.le) (smul_lt_smul_of_pos hfy hb)
        _ = f (a â¢ x + b â¢ y) := Convex.combo_self hab _
        

theorem StrictConcaveOn.left_lt_of_lt_right' (hf : StrictConcaveOn ð s f) {x y : E} (hx : x â s) (hy : y â s) {a b : ð}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f (a â¢ x + b â¢ y) < f y) : f x < f (a â¢ x + b â¢ y) :=
  hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy

theorem StrictConvexOn.lt_right_of_left_lt' (hf : StrictConvexOn ð s f) {x y : E} {a b : ð} (hx : x â s) (hy : y â s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x < f (a â¢ x + b â¢ y)) : f (a â¢ x + b â¢ y) < f y := by
  rw [add_commâ] at hab hfxâ¢
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx

theorem StrictConcaveOn.lt_right_of_left_lt' (hf : StrictConcaveOn ð s f) {x y : E} {a b : ð} (hx : x â s) (hy : y â s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a â¢ x + b â¢ y) < f x) : f y < f (a â¢ x + b â¢ y) :=
  hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx

theorem StrictConvexOn.lt_left_of_right_lt (hf : StrictConvexOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hz : z â OpenSegment ð x y) (hyz : f y < f z) : f z < f x := by
  obtain â¨a, b, ha, hb, hab, rflâ© := hz
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz

theorem StrictConcaveOn.left_lt_of_lt_right (hf : StrictConcaveOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hz : z â OpenSegment ð x y) (hyz : f z < f y) : f x < f z :=
  hf.dual.lt_left_of_right_lt hx hy hz hyz

theorem StrictConvexOn.lt_right_of_left_lt (hf : StrictConvexOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hz : z â OpenSegment ð x y) (hxz : f x < f z) : f z < f y := by
  obtain â¨a, b, ha, hb, hab, rflâ© := hz
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz

theorem StrictConcaveOn.lt_right_of_left_lt (hf : StrictConcaveOn ð s f) {x y z : E} (hx : x â s) (hy : y â s)
    (hz : z â OpenSegment ð x y) (hxz : f z < f x) : f y < f z :=
  hf.dual.lt_right_of_left_lt hx hy hz hxz

end Module

end LinearOrderedCancelAddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup Î²] [HasSmul ð E] [Module ð Î²] {s : Set E} {f g : E â Î²}

/-- A function `-f` is convex iff `f` is concave. -/
@[simp]
theorem neg_convex_on_iff : ConvexOn ð s (-f) â ConcaveOn ð s f := by
  constructor
  Â· rintro â¨hconv, hâ©
    refine' â¨hconv, fun x y hx hy a b ha hb hab => _â©
    simp [â neg_apply, â neg_le, â add_commâ] at h
    exact h hx hy ha hb hab
    
  Â· rintro â¨hconv, hâ©
    refine' â¨hconv, fun x y hx hy a b ha hb hab => _â©
    rw [â neg_le_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_negâ]
    exact h hx hy ha hb hab
    

/-- A function `-f` is concave iff `f` is convex. -/
@[simp]
theorem neg_concave_on_iff : ConcaveOn ð s (-f) â ConvexOn ð s f := by
  rw [â neg_convex_on_iff, neg_negâ f]

/-- A function `-f` is strictly convex iff `f` is strictly concave. -/
@[simp]
theorem neg_strict_convex_on_iff : StrictConvexOn ð s (-f) â StrictConcaveOn ð s f := by
  constructor
  Â· rintro â¨hconv, hâ©
    refine' â¨hconv, fun x y hx hy hxy a b ha hb hab => _â©
    simp [â neg_apply, â neg_lt, â add_commâ] at h
    exact h hx hy hxy ha hb hab
    
  Â· rintro â¨hconv, hâ©
    refine' â¨hconv, fun x y hx hy hxy a b ha hb hab => _â©
    rw [â neg_lt_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_negâ]
    exact h hx hy hxy ha hb hab
    

/-- A function `-f` is strictly concave iff `f` is strictly convex. -/
@[simp]
theorem neg_strict_concave_on_iff : StrictConcaveOn ð s (-f) â StrictConvexOn ð s f := by
  rw [â neg_strict_convex_on_iff, neg_negâ f]

alias neg_convex_on_iff â _ ConcaveOn.neg

alias neg_concave_on_iff â _ ConvexOn.neg

alias neg_strict_convex_on_iff â _ StrictConcaveOn.neg

alias neg_strict_concave_on_iff â _ StrictConvexOn.neg

theorem ConvexOn.sub (hf : ConvexOn ð s f) (hg : ConcaveOn ð s g) : ConvexOn ð s (f - g) :=
  (sub_eq_add_neg f g).symm â¸ hf.add hg.neg

theorem ConcaveOn.sub (hf : ConcaveOn ð s f) (hg : ConvexOn ð s g) : ConcaveOn ð s (f - g) :=
  (sub_eq_add_neg f g).symm â¸ hf.add hg.neg

theorem StrictConvexOn.sub (hf : StrictConvexOn ð s f) (hg : StrictConcaveOn ð s g) : StrictConvexOn ð s (f - g) :=
  (sub_eq_add_neg f g).symm â¸ hf.add hg.neg

theorem StrictConcaveOn.sub (hf : StrictConcaveOn ð s f) (hg : StrictConvexOn ð s g) : StrictConcaveOn ð s (f - g) :=
  (sub_eq_add_neg f g).symm â¸ hf.add hg.neg

theorem ConvexOn.sub_strict_concave_on (hf : ConvexOn ð s f) (hg : StrictConcaveOn ð s g) :
    StrictConvexOn ð s (f - g) :=
  (sub_eq_add_neg f g).symm â¸ hf.add_strict_convex_on hg.neg

theorem ConcaveOn.sub_strict_convex_on (hf : ConcaveOn ð s f) (hg : StrictConvexOn ð s g) :
    StrictConcaveOn ð s (f - g) :=
  (sub_eq_add_neg f g).symm â¸ hf.add_strict_concave_on hg.neg

theorem StrictConvexOn.sub_concave_on (hf : StrictConvexOn ð s f) (hg : ConcaveOn ð s g) : StrictConvexOn ð s (f - g) :=
  (sub_eq_add_neg f g).symm â¸ hf.add_convex_on hg.neg

theorem StrictConcaveOn.sub_convex_on (hf : StrictConcaveOn ð s f) (hg : ConvexOn ð s g) :
    StrictConcaveOn ð s (f - g) :=
  (sub_eq_add_neg f g).symm â¸ hf.add_concave_on hg.neg

end OrderedAddCommGroup

end AddCommMonoidâ

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [OrderedAddCommMonoid Î²] [Module ð E] [HasSmul ð Î²] {s : Set E} {f : E â Î²}

/-- Right translation preserves strict convexity. -/
theorem StrictConvexOn.translate_right (hf : StrictConvexOn ð s f) (c : E) :
    StrictConvexOn ð ((fun z => c + z) â»Â¹' s) (f â fun z => c + z) :=
  â¨hf.1.translate_preimage_right _, fun x y hx hy hxy a b ha hb hab =>
    calc
      f (c + (a â¢ x + b â¢ y)) = f (a â¢ (c + x) + b â¢ (c + y)) := by
        rw [smul_add, smul_add, add_add_add_commâ, Convex.combo_self hab]
      _ < a â¢ f (c + x) + b â¢ f (c + y) := hf.2 hx hy ((add_right_injective c).Ne hxy) ha hb hab
      â©

/-- Right translation preserves strict concavity. -/
theorem StrictConcaveOn.translate_right (hf : StrictConcaveOn ð s f) (c : E) :
    StrictConcaveOn ð ((fun z => c + z) â»Â¹' s) (f â fun z => c + z) :=
  hf.dual.translate_right _

/-- Left translation preserves strict convexity. -/
theorem StrictConvexOn.translate_left (hf : StrictConvexOn ð s f) (c : E) :
    StrictConvexOn ð ((fun z => c + z) â»Â¹' s) (f â fun z => z + c) := by
  simpa only [â add_commâ] using hf.translate_right _

/-- Left translation preserves strict concavity. -/
theorem StrictConcaveOn.translate_left (hf : StrictConcaveOn ð s f) (c : E) :
    StrictConcaveOn ð ((fun z => c + z) â»Â¹' s) (f â fun z => z + c) := by
  simpa only [â add_commâ] using hf.translate_right _

end AddCancelCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring ð] [AddCommMonoidâ E]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid Î²]

section Module

variable [HasSmul ð E] [Module ð Î²] [OrderedSmul ð Î²] {s : Set E} {f : E â Î²}

theorem ConvexOn.smul {c : ð} (hc : 0 â¤ c) (hf : ConvexOn ð s f) : ConvexOn ð s fun x => c â¢ f x :=
  â¨hf.1, fun x y hx hy a b ha hb hab =>
    calc
      c â¢ f (a â¢ x + b â¢ y) â¤ c â¢ (a â¢ f x + b â¢ f y) := smul_le_smul_of_nonneg (hf.2 hx hy ha hb hab) hc
      _ = a â¢ c â¢ f x + b â¢ c â¢ f y := by
        rw [smul_add, smul_comm c, smul_comm c] <;> infer_instance
      â©

theorem ConcaveOn.smul {c : ð} (hc : 0 â¤ c) (hf : ConcaveOn ð s f) : ConcaveOn ð s fun x => c â¢ f x :=
  hf.dual.smul hc

end Module

end OrderedAddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [LinearOrderedField ð] [AddCommGroupâ E] [AddCommGroupâ F]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid Î²]

section Module

variable [Module ð E] [Module ð F] [HasSmul ð Î²]

/-- If a function is convex on `s`, it remains convex when precomposed by an affine map. -/
theorem ConvexOn.comp_affine_map {f : F â Î²} (g : E âáµ[ð] F) {s : Set F} (hf : ConvexOn ð s f) :
    ConvexOn ð (g â»Â¹' s) (f â g) :=
  â¨hf.1.affine_preimage _, fun x y hx hy a b ha hb hab =>
    calc
      (f â g) (a â¢ x + b â¢ y) = f (g (a â¢ x + b â¢ y)) := rfl
      _ = f (a â¢ g x + b â¢ g y) := by
        rw [Convex.combo_affine_apply hab]
      _ â¤ a â¢ f (g x) + b â¢ f (g y) := hf.2 hx hy ha hb hab
      â©

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
theorem ConcaveOn.comp_affine_map {f : F â Î²} (g : E âáµ[ð] F) {s : Set F} (hf : ConcaveOn ð s f) :
    ConcaveOn ð (g â»Â¹' s) (f â g) :=
  hf.dual.comp_affine_map g

end Module

end OrderedAddCommMonoid

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField ð] [AddCommMonoidâ E]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid Î²]

section HasSmul

variable [HasSmul ð E] [HasSmul ð Î²] {s : Set E}

theorem convex_on_iff_div {f : E â Î²} :
    ConvexOn ð s f â
      Convex ð s â§
        â â¦x y : Eâ¦,
          x â s â
            y â s â
              â â¦a b : ðâ¦,
                0 â¤ a â
                  0 â¤ b â
                    0 < a + b â f ((a / (a + b)) â¢ x + (b / (a + b)) â¢ y) â¤ (a / (a + b)) â¢ f x + (b / (a + b)) â¢ f y :=
  and_congr Iff.rfl
    â¨by
      intro h x y hx hy a b ha hb hab
      apply h hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le)
      rw [â add_div, div_self hab.ne'], by
      intro h x y hx hy a b ha hb hab
      simpa [â hab, â zero_lt_one] using h hx hy ha hbâ©

theorem concave_on_iff_div {f : E â Î²} :
    ConcaveOn ð s f â
      Convex ð s â§
        â â¦x y : Eâ¦,
          x â s â
            y â s â
              â â¦a b : ðâ¦,
                0 â¤ a â
                  0 â¤ b â
                    0 < a + b â (a / (a + b)) â¢ f x + (b / (a + b)) â¢ f y â¤ f ((a / (a + b)) â¢ x + (b / (a + b)) â¢ y) :=
  @convex_on_iff_div _ _ Î²áµáµ _ _ _ _ _ _ _

theorem strict_convex_on_iff_div {f : E â Î²} :
    StrictConvexOn ð s f â
      Convex ð s â§
        â â¦x y : Eâ¦,
          x â s â
            y â s â
              x â  y â
                â â¦a b : ðâ¦,
                  0 < a â
                    0 < b â f ((a / (a + b)) â¢ x + (b / (a + b)) â¢ y) < (a / (a + b)) â¢ f x + (b / (a + b)) â¢ f y :=
  and_congr Iff.rfl
    â¨by
      intro h x y hx hy hxy a b ha hb
      have hab := add_pos ha hb
      apply h hx hy hxy (div_pos ha hab) (div_pos hb hab)
      rw [â add_div, div_self hab.ne'], by
      intro h x y hx hy hxy a b ha hb hab
      simpa [â hab, â zero_lt_one] using h hx hy hxy ha hbâ©

theorem strict_concave_on_iff_div {f : E â Î²} :
    StrictConcaveOn ð s f â
      Convex ð s â§
        â â¦x y : Eâ¦,
          x â s â
            y â s â
              x â  y â
                â â¦a b : ðâ¦,
                  0 < a â
                    0 < b â (a / (a + b)) â¢ f x + (b / (a + b)) â¢ f y < f ((a / (a + b)) â¢ x + (b / (a + b)) â¢ y) :=
  @strict_convex_on_iff_div _ _ Î²áµáµ _ _ _ _ _ _ _

end HasSmul

end OrderedAddCommMonoid

end LinearOrderedField

section

variable [LinearOrderedField ð] [LinearOrderedCancelAddCommMonoid Î²] [Module ð Î²] [OrderedSmul ð Î²] {x y z : ð}
  {s : Set ð} {f : ð â Î²}

theorem ConvexOn.le_right_of_left_le'' (hf : ConvexOn ð s f) (hx : x â s) (hz : z â s) (hxy : x < y) (hyz : y â¤ z)
    (h : f x â¤ f y) : f y â¤ f z :=
  hyz.eq_or_lt.elim (fun hyz => (congr_arg f hyz).le) fun hyz =>
    hf.le_right_of_left_le hx hz (Ioo_subset_open_segment â¨hxy, hyzâ©) h

theorem ConvexOn.le_left_of_right_le'' (hf : ConvexOn ð s f) (hx : x â s) (hz : z â s) (hxy : x â¤ y) (hyz : y < z)
    (h : f z â¤ f y) : f y â¤ f x :=
  hxy.eq_or_lt.elim (fun hxy => (congr_arg f hxy).Ge) fun hxy =>
    hf.le_left_of_right_le hx hz (Ioo_subset_open_segment â¨hxy, hyzâ©) h

theorem ConcaveOn.right_le_of_le_left'' (hf : ConcaveOn ð s f) (hx : x â s) (hz : z â s) (hxy : x < y) (hyz : y â¤ z)
    (h : f y â¤ f x) : f z â¤ f y :=
  hf.dual.le_right_of_left_le'' hx hz hxy hyz h

theorem ConcaveOn.left_le_of_le_right'' (hf : ConcaveOn ð s f) (hx : x â s) (hz : z â s) (hxy : x â¤ y) (hyz : y < z)
    (h : f y â¤ f z) : f x â¤ f y :=
  hf.dual.le_left_of_right_le'' hx hz hxy hyz h

end

