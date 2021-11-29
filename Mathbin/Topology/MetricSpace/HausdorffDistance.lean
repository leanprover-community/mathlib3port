import Mathbin.Topology.MetricSpace.Isometry 
import Mathbin.Topology.Instances.Ennreal 
import Mathbin.Analysis.SpecificLimits

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This files introduces:
* `inf_edist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Hausdorff_edist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `inf_dist` and `Hausdorff_dist`
* `thickening δ s`, the open thickening by radius `δ` of a set `s` in a pseudo emetric space.
-/


noncomputable theory

open_locale Classical Nnreal Ennreal TopologicalSpace

universe u v w

open Classical Set Function TopologicalSpace Filter

namespace Emetric

section InfEdist

variable{α : Type u}{β : Type v}[PseudoEmetricSpace α][PseudoEmetricSpace β]{x y : α}{s t : Set α}{Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ≥0∞`. -/


/-- The minimal edistance of a point to a set -/
def inf_edist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅(y : _)(_ : y ∈ s), edist x y

@[simp]
theorem inf_edist_empty : inf_edist x ∅ = ∞ :=
  infi_emptyset

theorem le_inf_edist {d} : d ≤ inf_edist x s ↔ ∀ y (_ : y ∈ s), d ≤ edist x y :=
  by 
    simp only [inf_edist, le_infi_iff]

/-- The edist to a union is the minimum of the edists -/
@[simp]
theorem inf_edist_union : inf_edist x (s ∪ t) = inf_edist x s⊓inf_edist x t :=
  infi_union

/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp]
theorem inf_edist_singleton : inf_edist x {y} = edist x y :=
  infi_singleton

/-- The edist to a set is bounded above by the edist to any of its points -/
theorem inf_edist_le_edist_of_mem (h : y ∈ s) : inf_edist x s ≤ edist x y :=
  binfi_le _ h

/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
theorem inf_edist_zero_of_mem (h : x ∈ s) : inf_edist x s = 0 :=
  nonpos_iff_eq_zero.1$ @edist_self _ _ x ▸ inf_edist_le_edist_of_mem h

/-- The edist is monotonous with respect to inclusion -/
theorem inf_edist_le_inf_edist_of_subset (h : s ⊆ t) : inf_edist x t ≤ inf_edist x s :=
  infi_le_infi_of_subset h

/-- If the edist to a set is `< r`, there exists a point in the set at edistance `< r` -/
theorem exists_edist_lt_of_inf_edist_lt {r : ℝ≥0∞} (h : inf_edist x s < r) : ∃ (y : _)(_ : y ∈ s), edist x y < r :=
  by 
    simpa only [inf_edist, infi_lt_iff] using h

/-- The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y` -/
theorem inf_edist_le_inf_edist_add_edist : inf_edist x s ≤ inf_edist y s+edist x y :=
  calc (⨅(z : _)(_ : z ∈ s), edist x z) ≤ ⨅(z : _)(_ : z ∈ s), edist y z+edist x y :=
    binfi_le_binfi$ fun z hz => (edist_triangle _ _ _).trans_eq (add_commₓ _ _)
    _ = (⨅(z : _)(_ : z ∈ s), edist y z)+edist x y :=
    by 
      simp only [Ennreal.infi_add]
    

/-- The edist to a set depends continuously on the point -/
@[continuity]
theorem continuous_inf_edist : Continuous fun x => inf_edist x s :=
  continuous_of_le_add_edist 1
      (by 
        simp )$
    by 
      simp only [one_mulₓ, inf_edist_le_inf_edist_add_edist, forall_2_true_iff]

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The edist to a set and to its closure coincide -/
theorem inf_edist_closure : «expr = »(inf_edist x (closure s), inf_edist x s) :=
begin
  refine [expr le_antisymm (inf_edist_le_inf_edist_of_subset subset_closure) _],
  refine [expr ennreal.le_of_forall_pos_le_add (λ ε εpos h, _)],
  have [ident ε0] [":", expr «expr < »(0, («expr / »(ε, 2) : «exprℝ≥0∞»()))] [":=", expr by simpa [] [] [] ["[", expr pos_iff_ne_zero, "]"] [] ["using", expr εpos]],
  have [] [":", expr «expr < »(inf_edist x (closure s), «expr + »(inf_edist x (closure s), «expr / »(ε, 2)))] [],
  from [expr ennreal.lt_add_right h.ne ε0.ne'],
  rcases [expr exists_edist_lt_of_inf_edist_lt this, "with", "⟨", ident y, ",", ident ycs, ",", ident hy, "⟩"],
  rcases [expr emetric.mem_closure_iff.1 ycs «expr / »(ε, 2) ε0, "with", "⟨", ident z, ",", ident zs, ",", ident dyz, "⟩"],
  calc
    «expr ≤ »(inf_edist x s, edist x z) : inf_edist_le_edist_of_mem zs
    «expr ≤ »(..., «expr + »(edist x y, edist y z)) : edist_triangle _ _ _
    «expr ≤ »(..., «expr + »(«expr + »(inf_edist x (closure s), «expr / »(ε, 2)), «expr / »(ε, 2))) : add_le_add (le_of_lt hy) (le_of_lt dyz)
    «expr = »(..., «expr + »(inf_edist x (closure s), «expr↑ »(ε))) : by rw ["[", expr add_assoc, ",", expr ennreal.add_halves, "]"] []
end

/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
theorem mem_closure_iff_inf_edist_zero : x ∈ Closure s ↔ inf_edist x s = 0 :=
  ⟨fun h =>
      by 
        rw [←inf_edist_closure] <;> exact inf_edist_zero_of_mem h,
    fun h =>
      Emetric.mem_closure_iff.2$
        fun ε εpos =>
          exists_edist_lt_of_inf_edist_lt
            (by 
              rwa [h])⟩

/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
theorem mem_iff_inf_edist_zero_of_closed (h : IsClosed s) : x ∈ s ↔ inf_edist x s = 0 :=
  by 
    convert ← mem_closure_iff_inf_edist_zero 
    exact h.closure_eq

theorem disjoint_closed_ball_of_lt_inf_edist {r : ℝ≥0∞} (h : r < inf_edist x s) : Disjoint (closed_ball x r) s :=
  by 
    rw [disjoint_left]
    intro y hy h'y 
    apply lt_irreflₓ (inf_edist x s)
    calc inf_edist x s ≤ edist x y := inf_edist_le_edist_of_mem h'y _ ≤ r :=
      by 
        rwa [mem_closed_ball, edist_comm] at hy _ < inf_edist x s :=
      h

/-- The infimum edistance is invariant under isometries -/
theorem inf_edist_image (hΦ : Isometry Φ) : inf_edist (Φ x) (Φ '' t) = inf_edist x t :=
  by 
    simp only [inf_edist, infi_image, hΦ.edist_eq]

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem _root_.is_open.exists_Union_is_closed
{U : set α}
(hU : is_open U) : «expr∃ , »((F : exprℕ() → set α), «expr ∧ »(∀
  n, is_closed (F n), «expr ∧ »(∀ n, «expr ⊆ »(F n, U), «expr ∧ »(«expr = »(«expr⋃ , »((n), F n), U), monotone F)))) :=
begin
  obtain ["⟨", ident a, ",", ident a_pos, ",", ident a_lt_one, "⟩", ":", expr «expr∃ , »((a : «exprℝ≥0∞»()), «expr ∧ »(«expr < »(0, a), «expr < »(a, 1))), ":=", expr exists_between ennreal.zero_lt_one],
  let [ident F] [] [":=", expr λ n : exprℕ(), «expr ⁻¹' »(λ x, inf_edist x «expr ᶜ»(U), Ici «expr ^ »(a, n))],
  have [ident F_subset] [":", expr ∀ n, «expr ⊆ »(F n, U)] [],
  { assume [binders (n x hx)],
    by_contra [ident h],
    rw ["[", "<-", expr mem_compl_iff, ",", expr mem_iff_inf_edist_zero_of_closed (is_open.is_closed_compl hU), "]"] ["at", ident h],
    have [] [":", expr «expr < »(0, inf_edist x «expr ᶜ»(U))] [":=", expr lt_of_lt_of_le (ennreal.pow_pos a_pos _) hx],
    rw [expr h] ["at", ident this],
    exact [expr lt_irrefl _ this] },
  refine [expr ⟨F, λ n, is_closed.preimage continuous_inf_edist is_closed_Ici, F_subset, _, _⟩],
  show [expr monotone F],
  { assume [binders (m n hmn x hx)],
    simp [] [] ["only"] ["[", expr mem_Ici, ",", expr mem_preimage, "]"] [] ["at", ident hx, "⊢"],
    apply [expr le_trans (ennreal.pow_le_pow_of_le_one a_lt_one.le hmn) hx] },
  show [expr «expr = »(«expr⋃ , »((n), F n), U)],
  { refine [expr subset.antisymm (by simp [] [] ["only"] ["[", expr Union_subset_iff, ",", expr F_subset, ",", expr forall_const, "]"] [] []) (λ
      x hx, _)],
    have [] [":", expr «expr¬ »(«expr ∈ »(x, «expr ᶜ»(U)))] [],
    by simpa [] [] [] [] [] ["using", expr hx],
    rw [expr mem_iff_inf_edist_zero_of_closed (is_open.is_closed_compl hU)] ["at", ident this],
    have [ident B] [":", expr «expr < »(0, inf_edist x «expr ᶜ»(U))] [],
    by simpa [] [] [] ["[", expr pos_iff_ne_zero, "]"] [] ["using", expr this],
    have [] [":", expr filter.tendsto (λ
      n, «expr ^ »(a, n)) at_top (expr𝓝() 0)] [":=", expr ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 a_lt_one],
    rcases [expr ((tendsto_order.1 this).2 _ B).exists, "with", "⟨", ident n, ",", ident hn, "⟩"],
    simp [] [] ["only"] ["[", expr mem_Union, ",", expr mem_Ici, ",", expr mem_preimage, "]"] [] [],
    exact [expr ⟨n, hn.le⟩] }
end

end InfEdist

/-! ### The Hausdorff distance as a function into `ℝ≥0∞`. -/


/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
@[irreducible]
def Hausdorff_edist {α : Type u} [PseudoEmetricSpace α] (s t : Set α) : ℝ≥0∞ :=
  (⨆(x : _)(_ : x ∈ s), inf_edist x t)⊔⨆(y : _)(_ : y ∈ t), inf_edist y s

theorem Hausdorff_edist_def {α : Type u} [PseudoEmetricSpace α] (s t : Set α) :
  Hausdorff_edist s t = (⨆(x : _)(_ : x ∈ s), inf_edist x t)⊔⨆(y : _)(_ : y ∈ t), inf_edist y s :=
  by 
    rw [Hausdorff_edist]

section HausdorffEdist

variable{α : Type u}{β : Type v}[PseudoEmetricSpace α][PseudoEmetricSpace β]{x y : α}{s t u : Set α}{Φ : α → β}

/-- The Hausdorff edistance of a set to itself vanishes -/
@[simp]
theorem Hausdorff_edist_self : Hausdorff_edist s s = 0 :=
  by 
    simp only [Hausdorff_edist_def, sup_idem, Ennreal.supr_eq_zero]
    exact fun x hx => inf_edist_zero_of_mem hx

/-- The Haudorff edistances of `s` to `t` and of `t` to `s` coincide -/
theorem Hausdorff_edist_comm : Hausdorff_edist s t = Hausdorff_edist t s :=
  by 
    unfold Hausdorff_edist <;> apply sup_comm

/-- Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set -/
theorem Hausdorff_edist_le_of_inf_edist {r : ℝ≥0∞} (H1 : ∀ x (_ : x ∈ s), inf_edist x t ≤ r)
  (H2 : ∀ x (_ : x ∈ t), inf_edist x s ≤ r) : Hausdorff_edist s t ≤ r :=
  by 
    simp only [Hausdorff_edist, sup_le_iff, supr_le_iff]
    exact ⟨H1, H2⟩

/-- Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem Hausdorff_edist_le_of_mem_edist {r : ℝ≥0∞} (H1 : ∀ x (_ : x ∈ s), ∃ (y : _)(_ : y ∈ t), edist x y ≤ r)
  (H2 : ∀ x (_ : x ∈ t), ∃ (y : _)(_ : y ∈ s), edist x y ≤ r) : Hausdorff_edist s t ≤ r :=
  by 
    refine' Hausdorff_edist_le_of_inf_edist _ _
    ·
      intro x xs 
      rcases H1 x xs with ⟨y, yt, hy⟩
      exact le_transₓ (inf_edist_le_edist_of_mem yt) hy
    ·
      intro x xt 
      rcases H2 x xt with ⟨y, ys, hy⟩
      exact le_transₓ (inf_edist_le_edist_of_mem ys) hy

/-- The distance to a set is controlled by the Hausdorff distance -/
theorem inf_edist_le_Hausdorff_edist_of_mem (h : x ∈ s) : inf_edist x t ≤ Hausdorff_edist s t :=
  by 
    rw [Hausdorff_edist_def]
    refine' le_transₓ _ le_sup_left 
    exact le_bsupr x h

/-- If the Hausdorff distance is `<r`, then any point in one of the sets has
a corresponding point at distance `<r` in the other set -/
theorem exists_edist_lt_of_Hausdorff_edist_lt {r : ℝ≥0∞} (h : x ∈ s) (H : Hausdorff_edist s t < r) :
  ∃ (y : _)(_ : y ∈ t), edist x y < r :=
  exists_edist_lt_of_inf_edist_lt$
    calc inf_edist x t ≤ Hausdorff_edist s t := inf_edist_le_Hausdorff_edist_of_mem h 
      _ < r := H
      

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The distance from `x` to `s` or `t` is controlled in terms of the Hausdorff distance
between `s` and `t` -/
theorem inf_edist_le_inf_edist_add_Hausdorff_edist : «expr ≤ »(inf_edist x t, «expr + »(inf_edist x s, Hausdorff_edist s t)) :=
«expr $ »(ennreal.le_of_forall_pos_le_add, λ ε εpos h, begin
   have [ident ε0] [":", expr «expr ≠ »((«expr / »(ε, 2) : «exprℝ≥0∞»()), 0)] [":=", expr by simpa [] [] [] ["[", expr pos_iff_ne_zero, "]"] [] ["using", expr εpos]],
   have [] [":", expr «expr < »(inf_edist x s, «expr + »(inf_edist x s, «expr / »(ε, 2)))] [":=", expr ennreal.lt_add_right (ennreal.add_lt_top.1 h).1.ne ε0],
   rcases [expr exists_edist_lt_of_inf_edist_lt this, "with", "⟨", ident y, ",", ident ys, ",", ident dxy, "⟩"],
   have [] [":", expr «expr < »(Hausdorff_edist s t, «expr + »(Hausdorff_edist s t, «expr / »(ε, 2)))] [":=", expr ennreal.lt_add_right (ennreal.add_lt_top.1 h).2.ne ε0],
   rcases [expr exists_edist_lt_of_Hausdorff_edist_lt ys this, "with", "⟨", ident z, ",", ident zt, ",", ident dyz, "⟩"],
   calc
     «expr ≤ »(inf_edist x t, edist x z) : inf_edist_le_edist_of_mem zt
     «expr ≤ »(..., «expr + »(edist x y, edist y z)) : edist_triangle _ _ _
     «expr ≤ »(..., «expr + »(«expr + »(inf_edist x s, «expr / »(ε, 2)), «expr + »(Hausdorff_edist s t, «expr / »(ε, 2)))) : add_le_add dxy.le dyz.le
     «expr = »(..., «expr + »(«expr + »(inf_edist x s, Hausdorff_edist s t), ε)) : by simp [] [] [] ["[", expr ennreal.add_halves, ",", expr add_comm, ",", expr add_left_comm, "]"] [] []
 end)

/-- The Hausdorff edistance is invariant under eisometries -/
theorem Hausdorff_edist_image (h : Isometry Φ) : Hausdorff_edist (Φ '' s) (Φ '' t) = Hausdorff_edist s t :=
  by 
    simp only [Hausdorff_edist_def, supr_image, inf_edist_image h]

/-- The Hausdorff distance is controlled by the diameter of the union -/
theorem Hausdorff_edist_le_ediam (hs : s.nonempty) (ht : t.nonempty) : Hausdorff_edist s t ≤ diam (s ∪ t) :=
  by 
    rcases hs with ⟨x, xs⟩
    rcases ht with ⟨y, yt⟩
    refine' Hausdorff_edist_le_of_mem_edist _ _
    ·
      intro z hz 
      exact ⟨y, yt, edist_le_diam_of_mem (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩
    ·
      intro z hz 
      exact ⟨x, xs, edist_le_diam_of_mem (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩

/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Hausdorff_edist_triangle : Hausdorff_edist s u ≤ Hausdorff_edist s t+Hausdorff_edist t u :=
  by 
    rw [Hausdorff_edist_def]
    simp only [sup_le_iff, supr_le_iff]
    split 
    show ∀ x (_ : x ∈ s), inf_edist x u ≤ Hausdorff_edist s t+Hausdorff_edist t u 
    exact
      fun x xs =>
        calc inf_edist x u ≤ inf_edist x t+Hausdorff_edist t u := inf_edist_le_inf_edist_add_Hausdorff_edist 
          _ ≤ Hausdorff_edist s t+Hausdorff_edist t u := add_le_add_right (inf_edist_le_Hausdorff_edist_of_mem xs) _ 
          
    show ∀ x (_ : x ∈ u), inf_edist x s ≤ Hausdorff_edist s t+Hausdorff_edist t u 
    exact
      fun x xu =>
        calc inf_edist x s ≤ inf_edist x t+Hausdorff_edist t s := inf_edist_le_inf_edist_add_Hausdorff_edist 
          _ ≤ Hausdorff_edist u t+Hausdorff_edist t s := add_le_add_right (inf_edist_le_Hausdorff_edist_of_mem xu) _ 
          _ = Hausdorff_edist s t+Hausdorff_edist t u :=
          by 
            simp [Hausdorff_edist_comm, add_commₓ]
          

/-- Two sets are at zero Hausdorff edistance if and only if they have the same closure -/
theorem Hausdorff_edist_zero_iff_closure_eq_closure : Hausdorff_edist s t = 0 ↔ Closure s = Closure t :=
  calc Hausdorff_edist s t = 0 ↔ s ⊆ Closure t ∧ t ⊆ Closure s :=
    by 
      simp only [Hausdorff_edist_def, Ennreal.sup_eq_zero, Ennreal.supr_eq_zero, ←mem_closure_iff_inf_edist_zero,
        subset_def]
    _ ↔ Closure s = Closure t :=
    ⟨fun h => subset.antisymm (closure_minimal h.1 is_closed_closure) (closure_minimal h.2 is_closed_closure),
      fun h => ⟨h ▸ subset_closure, h.symm ▸ subset_closure⟩⟩
    

/-- The Hausdorff edistance between a set and its closure vanishes -/
@[simp]
theorem Hausdorff_edist_self_closure : Hausdorff_edist s (Closure s) = 0 :=
  by 
    rw [Hausdorff_edist_zero_iff_closure_eq_closure, closure_closure]

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem Hausdorff_edist_closure₁ : Hausdorff_edist (Closure s) t = Hausdorff_edist s t :=
  by 
    refine' le_antisymmₓ _ _
    ·
      calc _ ≤ Hausdorff_edist (Closure s) s+Hausdorff_edist s t := Hausdorff_edist_triangle _ = Hausdorff_edist s t :=
        by 
          simp [Hausdorff_edist_comm]
    ·
      calc _ ≤ Hausdorff_edist s (Closure s)+Hausdorff_edist (Closure s) t :=
        Hausdorff_edist_triangle _ = Hausdorff_edist (Closure s) t :=
        by 
          simp 

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem Hausdorff_edist_closure₂ : Hausdorff_edist s (Closure t) = Hausdorff_edist s t :=
  by 
    simp [@Hausdorff_edist_comm _ _ s _]

/-- The Hausdorff edistance between sets or their closures is the same -/
@[simp]
theorem Hausdorff_edist_closure : Hausdorff_edist (Closure s) (Closure t) = Hausdorff_edist s t :=
  by 
    simp 

/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide -/
theorem Hausdorff_edist_zero_iff_eq_of_closed (hs : IsClosed s) (ht : IsClosed t) : Hausdorff_edist s t = 0 ↔ s = t :=
  by 
    rw [Hausdorff_edist_zero_iff_closure_eq_closure, hs.closure_eq, ht.closure_eq]

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Haudorff edistance to the empty set is infinite -/
theorem Hausdorff_edist_empty (ne : s.nonempty) : «expr = »(Hausdorff_edist s «expr∅»(), «expr∞»()) :=
begin
  rcases [expr ne, "with", "⟨", ident x, ",", ident xs, "⟩"],
  have [] [":", expr «expr ≤ »(inf_edist x «expr∅»(), Hausdorff_edist s «expr∅»())] [":=", expr inf_edist_le_Hausdorff_edist_of_mem xs],
  simpa [] [] [] [] [] ["using", expr this]
end

/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty -/
theorem nonempty_of_Hausdorff_edist_ne_top (hs : s.nonempty) (fin : Hausdorff_edist s t ≠ ⊤) : t.nonempty :=
  t.eq_empty_or_nonempty.elim (fun ht => (Finₓ$ ht.symm ▸ Hausdorff_edist_empty hs).elim) id

theorem empty_or_nonempty_of_Hausdorff_edist_ne_top (fin : Hausdorff_edist s t ≠ ⊤) :
  s = ∅ ∧ t = ∅ ∨ s.nonempty ∧ t.nonempty :=
  by 
    cases' s.eq_empty_or_nonempty with hs hs
    ·
      cases' t.eq_empty_or_nonempty with ht ht
      ·
        exact Or.inl ⟨hs, ht⟩
      ·
        rw [Hausdorff_edist_comm] at fin 
        exact Or.inr ⟨nonempty_of_Hausdorff_edist_ne_top ht Finₓ, ht⟩
    ·
      exact Or.inr ⟨hs, nonempty_of_Hausdorff_edist_ne_top hs Finₓ⟩

end HausdorffEdist

end Emetric

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`Inf` and `Sup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/


namespace Metric

section 

variable{α : Type u}{β : Type v}[PseudoMetricSpace α][PseudoMetricSpace β]{s t u : Set α}{x y : α}{Φ : α → β}

open Emetric

/-! ### Distance of a point to a set as a function into `ℝ`. -/


/-- The minimal distance of a point to a set -/
def inf_dist (x : α) (s : Set α) : ℝ :=
  Ennreal.toReal (inf_edist x s)

/-- the minimal distance is always nonnegative -/
theorem inf_dist_nonneg : 0 ≤ inf_dist x s :=
  by 
    simp [inf_dist]

/-- the minimal distance to the empty set is 0 (if you want to have the more reasonable
value ∞ instead, use `inf_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem inf_dist_empty : inf_dist x ∅ = 0 :=
  by 
    simp [inf_dist]

/-- In a metric space, the minimal edistance to a nonempty set is finite -/
theorem inf_edist_ne_top (h : s.nonempty) : inf_edist x s ≠ ⊤ :=
  by 
    rcases h with ⟨y, hy⟩
    apply lt_top_iff_ne_top.1
    calc inf_edist x s ≤ edist x y := inf_edist_le_edist_of_mem hy _ < ⊤ := lt_top_iff_ne_top.2 (edist_ne_top _ _)

/-- The minimal distance of a point to a set containing it vanishes -/
theorem inf_dist_zero_of_mem (h : x ∈ s) : inf_dist x s = 0 :=
  by 
    simp [inf_edist_zero_of_mem h, inf_dist]

/-- The minimal distance to a singleton is the distance to the unique point in this singleton -/
@[simp]
theorem inf_dist_singleton : inf_dist x {y} = dist x y :=
  by 
    simp [inf_dist, inf_edist, dist_edist]

/-- The minimal distance to a set is bounded by the distance to any point in this set -/
theorem inf_dist_le_dist_of_mem (h : y ∈ s) : inf_dist x s ≤ dist x y :=
  by 
    rw [dist_edist, inf_dist, Ennreal.to_real_le_to_real (inf_edist_ne_top ⟨_, h⟩) (edist_ne_top _ _)]
    exact inf_edist_le_edist_of_mem h

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The minimal distance is monotonous with respect to inclusion -/
theorem inf_dist_le_inf_dist_of_subset
(h : «expr ⊆ »(s, t))
(hs : s.nonempty) : «expr ≤ »(inf_dist x t, inf_dist x s) :=
begin
  have [ident ht] [":", expr t.nonempty] [":=", expr hs.mono h],
  rw ["[", expr inf_dist, ",", expr inf_dist, ",", expr ennreal.to_real_le_to_real (inf_edist_ne_top ht) (inf_edist_ne_top hs), "]"] [],
  exact [expr inf_edist_le_inf_edist_of_subset h]
end

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the minimal distance to a set is `<r`, there exists a point in this set at distance `<r` -/
theorem exists_dist_lt_of_inf_dist_lt
{r : real}
(h : «expr < »(inf_dist x s, r))
(hs : s.nonempty) : «expr∃ , »((y «expr ∈ » s), «expr < »(dist x y, r)) :=
begin
  have [ident rpos] [":", expr «expr < »(0, r)] [":=", expr lt_of_le_of_lt inf_dist_nonneg h],
  have [] [":", expr «expr < »(inf_edist x s, ennreal.of_real r)] [],
  { rwa ["[", expr inf_dist, ",", "<-", expr ennreal.to_real_of_real (le_of_lt rpos), ",", expr ennreal.to_real_lt_to_real (inf_edist_ne_top hs), "]"] ["at", ident h],
    simp [] [] [] [] [] [] },
  rcases [expr exists_edist_lt_of_inf_edist_lt this, "with", "⟨", ident y, ",", ident ys, ",", ident hy, "⟩"],
  rw ["[", expr edist_dist, ",", expr ennreal.of_real_lt_of_real_iff rpos, "]"] ["at", ident hy],
  exact [expr ⟨y, ys, hy⟩]
end

/-- The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`, modulo
the distance between `x` and `y` -/
theorem inf_dist_le_inf_dist_add_dist : inf_dist x s ≤ inf_dist y s+dist x y :=
  by 
    cases' s.eq_empty_or_nonempty with hs hs
    ·
      ·
        simp [hs, dist_nonneg]
    ·
      rw [inf_dist, inf_dist, dist_edist, ←Ennreal.to_real_add (inf_edist_ne_top hs) (edist_ne_top _ _),
        Ennreal.to_real_le_to_real (inf_edist_ne_top hs)]
      ·
        apply inf_edist_le_inf_edist_add_edist
      ·
        simp [Ennreal.add_eq_top, inf_edist_ne_top hs, edist_ne_top]

theorem disjoint_closed_ball_of_lt_inf_dist {r : ℝ} (h : r < inf_dist x s) : Disjoint (closed_ball x r) s :=
  by 
    rw [disjoint_left]
    intro y hy h'y 
    apply lt_irreflₓ (inf_dist x s)
    calc inf_dist x s ≤ dist x y := inf_dist_le_dist_of_mem h'y _ ≤ r :=
      by 
        rwa [mem_closed_ball, dist_comm] at hy _ < inf_dist x s :=
      h

variable(s)

/-- The minimal distance to a set is Lipschitz in point with constant 1 -/
theorem lipschitz_inf_dist_pt : LipschitzWith 1 fun x => inf_dist x s :=
  LipschitzWith.of_le_add$ fun x y => inf_dist_le_inf_dist_add_dist

/-- The minimal distance to a set is uniformly continuous in point -/
theorem uniform_continuous_inf_dist_pt : UniformContinuous fun x => inf_dist x s :=
  (lipschitz_inf_dist_pt s).UniformContinuous

/-- The minimal distance to a set is continuous in point -/
@[continuity]
theorem continuous_inf_dist_pt : Continuous fun x => inf_dist x s :=
  (uniform_continuous_inf_dist_pt s).Continuous

variable{s}

/-- The minimal distance to a set and its closure coincide -/
theorem inf_dist_eq_closure : inf_dist x (Closure s) = inf_dist x s :=
  by 
    simp [inf_dist, inf_edist_closure]

/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes -/
theorem mem_closure_iff_inf_dist_zero (h : s.nonempty) : x ∈ Closure s ↔ inf_dist x s = 0 :=
  by 
    simp [mem_closure_iff_inf_edist_zero, inf_dist, Ennreal.to_real_eq_zero_iff, inf_edist_ne_top h]

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
theorem _root_.is_closed.mem_iff_inf_dist_zero
(h : is_closed s)
(hs : s.nonempty) : «expr ↔ »(«expr ∈ »(x, s), «expr = »(inf_dist x s, 0)) :=
begin
  have [] [] [":=", expr @mem_closure_iff_inf_dist_zero _ _ s x hs],
  rwa [expr h.closure_eq] ["at", ident this]
end

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
theorem _root_.is_closed.not_mem_iff_inf_dist_pos (h : IsClosed s) (hs : s.nonempty) : x ∉ s ↔ 0 < inf_dist x s :=
  by 
    rw [←not_iff_not]
    pushNeg 
    simp [h.mem_iff_inf_dist_zero hs, le_antisymm_iffₓ, inf_dist_nonneg]

/-- The infimum distance is invariant under isometries -/
theorem inf_dist_image (hΦ : Isometry Φ) : inf_dist (Φ x) (Φ '' t) = inf_dist x t :=
  by 
    simp [inf_dist, inf_edist_image hΦ]

/-! ### Distance of a point to a set as a function into `ℝ≥0`. -/


/-- The minimal distance of a point to a set as a `ℝ≥0` -/
def inf_nndist (x : α) (s : Set α) :  ℝ≥0  :=
  Ennreal.toNnreal (inf_edist x s)

@[simp]
theorem coe_inf_nndist : (inf_nndist x s : ℝ) = inf_dist x s :=
  rfl

/-- The minimal distance to a set (as `ℝ≥0`) is Lipschitz in point with constant 1 -/
theorem lipschitz_inf_nndist_pt (s : Set α) : LipschitzWith 1 fun x => inf_nndist x s :=
  LipschitzWith.of_le_add$ fun x y => inf_dist_le_inf_dist_add_dist

/-- The minimal distance to a set (as `ℝ≥0`) is uniformly continuous in point -/
theorem uniform_continuous_inf_nndist_pt (s : Set α) : UniformContinuous fun x => inf_nndist x s :=
  (lipschitz_inf_nndist_pt s).UniformContinuous

/-- The minimal distance to a set (as `ℝ≥0`) is continuous in point -/
theorem continuous_inf_nndist_pt (s : Set α) : Continuous fun x => inf_nndist x s :=
  (uniform_continuous_inf_nndist_pt s).Continuous

/-! ### The Hausdorff distance as a function into `ℝ`. -/


/-- The Hausdorff distance between two sets is the smallest nonnegative `r` such that each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is defined to
be `0`, arbitrarily -/
def Hausdorff_dist (s t : Set α) : ℝ :=
  Ennreal.toReal (Hausdorff_edist s t)

/-- The Hausdorff distance is nonnegative -/
theorem Hausdorff_dist_nonneg : 0 ≤ Hausdorff_dist s t :=
  by 
    simp [Hausdorff_dist]

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two sets are nonempty and bounded in a metric space, they are at finite Hausdorff
edistance. -/
theorem Hausdorff_edist_ne_top_of_nonempty_of_bounded
(hs : s.nonempty)
(ht : t.nonempty)
(bs : bounded s)
(bt : bounded t) : «expr ≠ »(Hausdorff_edist s t, «expr⊤»()) :=
begin
  rcases [expr hs, "with", "⟨", ident cs, ",", ident hcs, "⟩"],
  rcases [expr ht, "with", "⟨", ident ct, ",", ident hct, "⟩"],
  rcases [expr (bounded_iff_subset_ball ct).1 bs, "with", "⟨", ident rs, ",", ident hrs, "⟩"],
  rcases [expr (bounded_iff_subset_ball cs).1 bt, "with", "⟨", ident rt, ",", ident hrt, "⟩"],
  have [] [":", expr «expr ≤ »(Hausdorff_edist s t, ennreal.of_real (max rs rt))] [],
  { apply [expr Hausdorff_edist_le_of_mem_edist],
    { assume [binders (x xs)],
      existsi ["[", expr ct, ",", expr hct, "]"],
      have [] [":", expr «expr ≤ »(dist x ct, max rs rt)] [":=", expr le_trans (hrs xs) (le_max_left _ _)],
      rwa ["[", expr edist_dist, ",", expr ennreal.of_real_le_of_real_iff, "]"] [],
      exact [expr le_trans dist_nonneg this] },
    { assume [binders (x xt)],
      existsi ["[", expr cs, ",", expr hcs, "]"],
      have [] [":", expr «expr ≤ »(dist x cs, max rs rt)] [":=", expr le_trans (hrt xt) (le_max_right _ _)],
      rwa ["[", expr edist_dist, ",", expr ennreal.of_real_le_of_real_iff, "]"] [],
      exact [expr le_trans dist_nonneg this] } },
  exact [expr ne_top_of_le_ne_top ennreal.of_real_ne_top this]
end

/-- The Hausdorff distance between a set and itself is zero -/
@[simp]
theorem Hausdorff_dist_self_zero : Hausdorff_dist s s = 0 :=
  by 
    simp [Hausdorff_dist]

/-- The Hausdorff distance from `s` to `t` and from `t` to `s` coincide -/
theorem Hausdorff_dist_comm : Hausdorff_dist s t = Hausdorff_dist t s :=
  by 
    simp [Hausdorff_dist, Hausdorff_edist_comm]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem Hausdorff_dist_empty : Hausdorff_dist s ∅ = 0 :=
  by 
    cases' s.eq_empty_or_nonempty with h h
    ·
      simp [h]
    ·
      simp [Hausdorff_dist, Hausdorff_edist_empty h]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem Hausdorff_dist_empty' : Hausdorff_dist ∅ s = 0 :=
  by 
    simp [Hausdorff_dist_comm]

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set -/
theorem Hausdorff_dist_le_of_inf_dist
{r : exprℝ()}
(hr : «expr ≤ »(0, r))
(H1 : ∀ x «expr ∈ » s, «expr ≤ »(inf_dist x t, r))
(H2 : ∀ x «expr ∈ » t, «expr ≤ »(inf_dist x s, r)) : «expr ≤ »(Hausdorff_dist s t, r) :=
begin
  by_cases [expr h1, ":", expr «expr = »(Hausdorff_edist s t, «expr⊤»())],
  by rwa ["[", expr Hausdorff_dist, ",", expr h1, ",", expr ennreal.top_to_real, "]"] [],
  cases [expr s.eq_empty_or_nonempty] ["with", ident hs, ident hs],
  by rwa ["[", expr hs, ",", expr Hausdorff_dist_empty', "]"] [],
  cases [expr t.eq_empty_or_nonempty] ["with", ident ht, ident ht],
  by rwa ["[", expr ht, ",", expr Hausdorff_dist_empty, "]"] [],
  have [] [":", expr «expr ≤ »(Hausdorff_edist s t, ennreal.of_real r)] [],
  { apply [expr Hausdorff_edist_le_of_inf_edist _ _],
    { assume [binders (x hx)],
      have [ident I] [] [":=", expr H1 x hx],
      rwa ["[", expr inf_dist, ",", "<-", expr ennreal.to_real_of_real hr, ",", expr ennreal.to_real_le_to_real (inf_edist_ne_top ht) ennreal.of_real_ne_top, "]"] ["at", ident I] },
    { assume [binders (x hx)],
      have [ident I] [] [":=", expr H2 x hx],
      rwa ["[", expr inf_dist, ",", "<-", expr ennreal.to_real_of_real hr, ",", expr ennreal.to_real_le_to_real (inf_edist_ne_top hs) ennreal.of_real_ne_top, "]"] ["at", ident I] } },
  rwa ["[", expr Hausdorff_dist, ",", "<-", expr ennreal.to_real_of_real hr, ",", expr ennreal.to_real_le_to_real h1 ennreal.of_real_ne_top, "]"] []
end

/-- Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem Hausdorff_dist_le_of_mem_dist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x (_ : x ∈ s), ∃ (y : _)(_ : y ∈ t), dist x y ≤ r)
  (H2 : ∀ x (_ : x ∈ t), ∃ (y : _)(_ : y ∈ s), dist x y ≤ r) : Hausdorff_dist s t ≤ r :=
  by 
    apply Hausdorff_dist_le_of_inf_dist hr
    ·
      intro x xs 
      rcases H1 x xs with ⟨y, yt, hy⟩
      exact le_transₓ (inf_dist_le_dist_of_mem yt) hy
    ·
      intro x xt 
      rcases H2 x xt with ⟨y, ys, hy⟩
      exact le_transₓ (inf_dist_le_dist_of_mem ys) hy

/-- The Hausdorff distance is controlled by the diameter of the union -/
theorem Hausdorff_dist_le_diam (hs : s.nonempty) (bs : Bounded s) (ht : t.nonempty) (bt : Bounded t) :
  Hausdorff_dist s t ≤ diam (s ∪ t) :=
  by 
    rcases hs with ⟨x, xs⟩
    rcases ht with ⟨y, yt⟩
    refine' Hausdorff_dist_le_of_mem_dist diam_nonneg _ _
    ·
      exact
        fun z hz =>
          ⟨y, yt, dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩) (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩
    ·
      exact
        fun z hz =>
          ⟨x, xs, dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩) (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The distance to a set is controlled by the Hausdorff distance -/
theorem inf_dist_le_Hausdorff_dist_of_mem
(hx : «expr ∈ »(x, s))
(fin : «expr ≠ »(Hausdorff_edist s t, «expr⊤»())) : «expr ≤ »(inf_dist x t, Hausdorff_dist s t) :=
begin
  have [ident ht] [":", expr t.nonempty] [":=", expr nonempty_of_Hausdorff_edist_ne_top ⟨x, hx⟩ fin],
  rw ["[", expr Hausdorff_dist, ",", expr inf_dist, ",", expr ennreal.to_real_le_to_real (inf_edist_ne_top ht) fin, "]"] [],
  exact [expr inf_edist_le_Hausdorff_edist_of_mem hx]
end

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
theorem exists_dist_lt_of_Hausdorff_dist_lt
{r : exprℝ()}
(h : «expr ∈ »(x, s))
(H : «expr < »(Hausdorff_dist s t, r))
(fin : «expr ≠ »(Hausdorff_edist s t, «expr⊤»())) : «expr∃ , »((y «expr ∈ » t), «expr < »(dist x y, r)) :=
begin
  have [ident r0] [":", expr «expr < »(0, r)] [":=", expr lt_of_le_of_lt Hausdorff_dist_nonneg H],
  have [] [":", expr «expr < »(Hausdorff_edist s t, ennreal.of_real r)] [],
  by rwa ["[", expr Hausdorff_dist, ",", "<-", expr ennreal.to_real_of_real (le_of_lt r0), ",", expr ennreal.to_real_lt_to_real fin ennreal.of_real_ne_top, "]"] ["at", ident H],
  rcases [expr exists_edist_lt_of_Hausdorff_edist_lt h this, "with", "⟨", ident y, ",", ident hy, ",", ident yr, "⟩"],
  rw ["[", expr edist_dist, ",", expr ennreal.of_real_lt_of_real_iff r0, "]"] ["at", ident yr],
  exact [expr ⟨y, hy, yr⟩]
end

/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
theorem exists_dist_lt_of_Hausdorff_dist_lt' {r : ℝ} (h : y ∈ t) (H : Hausdorff_dist s t < r)
  (fin : Hausdorff_edist s t ≠ ⊤) : ∃ (x : _)(_ : x ∈ s), dist x y < r :=
  by 
    rw [Hausdorff_dist_comm] at H 
    rw [Hausdorff_edist_comm] at fin 
    simpa [dist_comm] using exists_dist_lt_of_Hausdorff_dist_lt h H Finₓ

/-- The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t` -/
theorem inf_dist_le_inf_dist_add_Hausdorff_dist (fin : Hausdorff_edist s t ≠ ⊤) :
  inf_dist x t ≤ inf_dist x s+Hausdorff_dist s t :=
  by 
    rcases empty_or_nonempty_of_Hausdorff_edist_ne_top Finₓ with (⟨hs, ht⟩ | ⟨hs, ht⟩)
    ·
      simp only [hs, ht, Hausdorff_dist_empty, inf_dist_empty, zero_addₓ]
    rw [inf_dist, inf_dist, Hausdorff_dist, ←Ennreal.to_real_add (inf_edist_ne_top hs) Finₓ,
      Ennreal.to_real_le_to_real (inf_edist_ne_top ht)]
    ·
      exact inf_edist_le_inf_edist_add_Hausdorff_edist
    ·
      exact Ennreal.add_ne_top.2 ⟨inf_edist_ne_top hs, Finₓ⟩

/-- The Hausdorff distance is invariant under isometries -/
theorem Hausdorff_dist_image (h : Isometry Φ) : Hausdorff_dist (Φ '' s) (Φ '' t) = Hausdorff_dist s t :=
  by 
    simp [Hausdorff_dist, Hausdorff_edist_image h]

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Hausdorff_dist_triangle
(fin : «expr ≠ »(Hausdorff_edist s t, «expr⊤»())) : «expr ≤ »(Hausdorff_dist s u, «expr + »(Hausdorff_dist s t, Hausdorff_dist t u)) :=
begin
  by_cases [expr «expr = »(Hausdorff_edist s u, «expr⊤»())],
  { calc
      «expr = »(Hausdorff_dist s u, «expr + »(0, 0)) : by simp [] [] [] ["[", expr Hausdorff_dist, ",", expr h, "]"] [] []
      «expr ≤ »(..., «expr + »(Hausdorff_dist s t, Hausdorff_dist t u)) : add_le_add Hausdorff_dist_nonneg Hausdorff_dist_nonneg },
  { have [ident Dtu] [":", expr «expr < »(Hausdorff_edist t u, «expr⊤»())] [":=", expr calc
       «expr ≤ »(Hausdorff_edist t u, «expr + »(Hausdorff_edist t s, Hausdorff_edist s u)) : Hausdorff_edist_triangle
       «expr = »(..., «expr + »(Hausdorff_edist s t, Hausdorff_edist s u)) : by simp [] [] [] ["[", expr Hausdorff_edist_comm, "]"] [] []
       «expr < »(..., «expr⊤»()) : by simp [] [] [] ["[", expr lt_top_iff_ne_top, ",", "*", "]"] [] []],
    rw ["[", expr Hausdorff_dist, ",", expr Hausdorff_dist, ",", expr Hausdorff_dist, ",", "<-", expr ennreal.to_real_add fin Dtu.ne, ",", expr ennreal.to_real_le_to_real h, "]"] [],
    { exact [expr Hausdorff_edist_triangle] },
    { simp [] [] [] ["[", expr ennreal.add_eq_top, ",", expr lt_top_iff_ne_top.1 Dtu, ",", expr fin, "]"] [] [] } }
end

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Hausdorff_dist_triangle'
(fin : «expr ≠ »(Hausdorff_edist t u, «expr⊤»())) : «expr ≤ »(Hausdorff_dist s u, «expr + »(Hausdorff_dist s t, Hausdorff_dist t u)) :=
begin
  rw [expr Hausdorff_edist_comm] ["at", ident fin],
  have [ident I] [":", expr «expr ≤ »(Hausdorff_dist u s, «expr + »(Hausdorff_dist u t, Hausdorff_dist t s))] [":=", expr Hausdorff_dist_triangle fin],
  simpa [] [] [] ["[", expr add_comm, ",", expr Hausdorff_dist_comm, "]"] [] ["using", expr I]
end

/-- The Hausdorff distance between a set and its closure vanish -/
@[simp]
theorem Hausdorff_dist_self_closure : Hausdorff_dist s (Closure s) = 0 :=
  by 
    simp [Hausdorff_dist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem Hausdorff_dist_closure₁ : Hausdorff_dist (Closure s) t = Hausdorff_dist s t :=
  by 
    simp [Hausdorff_dist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem Hausdorff_dist_closure₂ : Hausdorff_dist s (Closure t) = Hausdorff_dist s t :=
  by 
    simp [Hausdorff_dist]

/-- The Hausdorff distance between two sets and their closures coincide -/
@[simp]
theorem Hausdorff_dist_closure : Hausdorff_dist (Closure s) (Closure t) = Hausdorff_dist s t :=
  by 
    simp [Hausdorff_dist]

/-- Two sets are at zero Hausdorff distance if and only if they have the same closures -/
theorem Hausdorff_dist_zero_iff_closure_eq_closure (fin : Hausdorff_edist s t ≠ ⊤) :
  Hausdorff_dist s t = 0 ↔ Closure s = Closure t :=
  by 
    simp [Hausdorff_edist_zero_iff_closure_eq_closure.symm, Hausdorff_dist, Ennreal.to_real_eq_zero_iff, Finₓ]

/-- Two closed sets are at zero Hausdorff distance if and only if they coincide -/
theorem _root_.is_closed.Hausdorff_dist_zero_iff_eq (hs : IsClosed s) (ht : IsClosed t)
  (fin : Hausdorff_edist s t ≠ ⊤) : Hausdorff_dist s t = 0 ↔ s = t :=
  by 
    simp [(Hausdorff_edist_zero_iff_eq_of_closed hs ht).symm, Hausdorff_dist, Ennreal.to_real_eq_zero_iff, Finₓ]

end 

section Thickening

variable{α : Type u}[PseudoEmetricSpace α]

open Emetric

/-- The (open) `δ`-thickening `thickening δ E` of a subset `E` in a pseudo emetric space consists
of those points that are at distance less than `δ` from some point of `E`. -/
def thickening (δ : ℝ) (E : Set α) : Set α :=
  { x:α | inf_edist x E < Ennreal.ofReal δ }

/-- The (open) thickening equals the preimage of an open interval under `inf_edist`. -/
theorem thickening_eq_preimage_inf_edist (δ : ℝ) (E : Set α) :
  thickening δ E = (fun x => inf_edist x E) ⁻¹' Iio (Ennreal.ofReal δ) :=
  rfl

/-- The (open) thickening is an open set. -/
theorem is_open_thickening {δ : ℝ} {E : Set α} : IsOpen (thickening δ E) :=
  Continuous.is_open_preimage continuous_inf_edist _ is_open_Iio

/-- The (open) thickening of the empty set is empty. -/
@[simp]
theorem thickening_empty (δ : ℝ) : thickening δ (∅ : Set α) = ∅ :=
  by 
    simp only [thickening, set_of_false, inf_edist_empty, not_top_lt]

/-- The (open) thickening `thickening δ E` of a fixed subset `E` is an increasing function of the
thickening radius `δ`. -/
theorem thickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) : thickening δ₁ E ⊆ thickening δ₂ E :=
  preimage_mono (Iio_subset_Iio (Ennreal.of_real_le_of_real hle))

/-- The (open) thickening `thickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
theorem thickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) : thickening δ E₁ ⊆ thickening δ E₂ :=
  fun _ hx => lt_of_le_of_ltₓ (inf_edist_le_inf_edist_of_subset h) hx

variable{X : Type u}[MetricSpace X]

-- error in Topology.MetricSpace.HausdorffDistance: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A point in a metric space belongs to the (open) `δ`-thickening of a subset `E` if and only if
it is at distance less than `δ` from some point of `E`. -/
theorem mem_thickening_iff
{δ : exprℝ()}
(E : set X)
(x : X) : «expr ↔ »(«expr ∈ »(x, thickening δ E), «expr∃ , »((z «expr ∈ » E), «expr < »(dist x z, δ))) :=
begin
  unfold [ident thickening] [],
  simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_set_of_eq, "]"] [] [],
  split,
  { intros [ident h],
    rcases [expr exists_edist_lt_of_inf_edist_lt h, "with", "⟨", ident z, ",", "⟨", ident hzE, ",", ident hxz, "⟩", "⟩"],
    refine [expr ⟨z, hzE, _⟩],
    rw [expr dist_edist] [],
    apply [expr (@ennreal.of_real_lt_of_real_iff_of_nonneg (edist x z).to_real δ ennreal.to_real_nonneg).mp],
    rwa [expr ennreal.of_real_to_real (edist_lt_top x z).ne] [] },
  { intros [ident h],
    rcases [expr h, "with", "⟨", ident z, ",", "⟨", ident hzE, ",", ident hxz, "⟩", "⟩"],
    rw [expr dist_edist] ["at", ident hxz],
    apply [expr lt_of_le_of_lt (@inf_edist_le_edist_of_mem _ _ x _ _ hzE) _],
    have [ident key] [] [":=", expr (@ennreal.of_real_lt_of_real_iff_of_nonneg (edist x z).to_real δ ennreal.to_real_nonneg).mpr hxz],
    rwa [expr ennreal.of_real_to_real (edist_lt_top x z).ne] ["at", ident key] }
end

/-- The (open) `δ`-thickening `thickening δ E` of a subset `E` in a metric space equals the
union of balls of radius `δ` centered at points of `E`. -/
theorem thickening_eq_bUnion_ball {δ : ℝ} {E : Set X} : thickening δ E = ⋃(x : _)(_ : x ∈ E), ball x δ :=
  by 
    ext x 
    rw [mem_bUnion_iff]
    exact mem_thickening_iff E x

end Thickening

end Metric

