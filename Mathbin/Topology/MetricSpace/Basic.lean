import Mathbin.Data.Int.Interval 
import Mathbin.Topology.Algebra.Ordered.Compact 
import Mathbin.Topology.MetricSpace.EmetricSpace

/-!
# Metric spaces

This file defines metric spaces. Many definitions and theorems expected
on metric spaces are already introduced on uniform spaces and topological spaces.
For example: open and closed sets, compactness, completeness, continuity and uniform continuity

## Main definitions

* `has_dist α`: Endows a space `α` with a function `dist a b`.
* `pseudo_metric_space α`: A space endowed with a distance function, which can
  be zero even if the two elements are non-equal.
* `metric.ball x ε`: The set of all points `y` with `dist y x < ε`.
* `metric.bounded s`: Whether a subset of a `pseudo_metric_space` is bounded.
* `metric_space α`: A `pseudo_metric_space` with the guarantee `dist x y = 0 → x = y`.

Additional useful definitions:

* `nndist a b`: `dist` as a function to the non-negative reals.
* `metric.closed_ball x ε`: The set of all points `y` with `dist y x ≤ ε`.
* `metric.sphere x ε`: The set of all points `y` with `dist y x = ε`.
* `proper_space α`: A `pseudo_metric_space` where all closed balls are compact.
* `metric.diam s` : The `supr` of the distances of members of `s`.
  Defined in terms of `emetric.diam`, for better handling of the case when it should be infinite.

TODO (anyone): Add "Main results" section.

## Implementation notes

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory of `pseudo_metric_space`, where we don't require `dist x y = 0 → x = y` and we specialize
to `metric_space` at the end.

## Tags

metric, pseudo_metric, dist
-/


open Set Filter TopologicalSpace

open_locale uniformity TopologicalSpace BigOperators Filter Nnreal Ennreal

universe u v w

variable{α : Type u}{β : Type v}

-- error in Topology.MetricSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Construct a uniform structure core from a distance function and metric space axioms.
This is a technical construction that can be immediately used to construct a uniform structure
from a distance function and metric space axioms but is also useful when discussing
metrizable topologies, see `pseudo_metric_space.of_metrizable`. -/
def uniform_space.core_of_dist
{α : Type*}
(dist : α → α → exprℝ())
(dist_self : ∀ x : α, «expr = »(dist x x, 0))
(dist_comm : ∀ x y : α, «expr = »(dist x y, dist y x))
(dist_triangle : ∀ x y z : α, «expr ≤ »(dist x z, «expr + »(dist x y, dist y z))) : uniform_space.core α :=
{ uniformity := «expr⨅ , »((ε «expr > » 0), expr𝓟() {p : «expr × »(α, α) | «expr < »(dist p.1 p.2, ε)}),
  refl := «expr $ »(le_infi, assume
   ε, «expr $ »(le_infi, by simp [] [] [] ["[", expr set.subset_def, ",", expr id_rel, ",", expr dist_self, ",", expr («expr > »), "]"] [] [] { contextual := tt })),
  comp := «expr $ »(le_infi, assume
   ε, «expr $ »(le_infi, assume
    h, «expr $ »(lift'_le «expr $ »(mem_infi_of_mem «expr / »(ε, 2), mem_infi_of_mem (div_pos h zero_lt_two) (subset.refl _)), have ∀
     a
     b
     c : α, «expr < »(dist a c, «expr / »(ε, 2)) → «expr < »(dist c b, «expr / »(ε, 2)) → «expr < »(dist a b, ε), from assume
     a b c hac hcb, calc
       «expr ≤ »(dist a b, «expr + »(dist a c, dist c b)) : dist_triangle _ _ _
       «expr < »(..., «expr + »(«expr / »(ε, 2), «expr / »(ε, 2))) : add_lt_add hac hcb
       «expr = »(..., ε) : by rw ["[", expr div_add_div_same, ",", expr add_self_div_two, "]"] [],
     by simpa [] [] [] ["[", expr comp_rel, "]"] [] []))),
  symm := «expr $ »(tendsto_infi.2, assume
   ε, «expr $ »(tendsto_infi.2, assume
    h, «expr $ »(tendsto_infi' ε, «expr $ »(tendsto_infi' h, «expr $ »(tendsto_principal_principal.2, by simp [] [] [] ["[", expr dist_comm, "]"] [] []))))) }

/-- Construct a uniform structure from a distance function and metric space axioms -/
def uniformSpaceOfDist (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x) (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y+dist y z) :
  UniformSpace α :=
  UniformSpace.ofCore (UniformSpace.coreOfDist dist dist_self dist_comm dist_triangle)

/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
class HasDist(α : Type _) where 
  dist : α → α → ℝ

export HasDist(dist)

/-- This is an internal lemma used inside the default of `pseudo_metric_space.edist`. -/
private theorem pseudo_metric_space.dist_nonneg' {α} {x y : α} (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x) (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y+dist y z) :
  0 ≤ dist x y :=
  have  : (2*dist x y) ≥ 0 :=
    calc (2*dist x y) = dist x y+dist y x :=
      by 
        rw [dist_comm x y, two_mul]
      _ ≥ 0 :=
      by 
        rw [←dist_self x] <;> apply dist_triangle 
      
  nonneg_of_mul_nonneg_left this zero_lt_two

/-- This tactic is used to populate `pseudo_metric_space.edist_dist` when the default `edist` is
used. -/
protected unsafe def pseudo_metric_space.edist_dist_tac : tactic Unit :=
  tactic.intros >> sorry

/-- Metric space

Each metric space induces a canonical `uniform_space` and hence a canonical `topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `metric_space` structure, the uniformity fields are not necessary, they will be
filled in by default. In the same way, each metric space induces an emetric space structure.
It is included in the structure, but filled in by default.
-/
class PseudoMetricSpace(α : Type u) extends HasDist α : Type u where 
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x 
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y+dist y z 
  edist : α → α → ℝ≥0∞ := fun x y => @coeₓ ℝ≥0  _ _ ⟨dist x y, pseudo_metric_space.dist_nonneg' _ ‹_› ‹_› ‹_›⟩
  edist_dist : ∀ x y : α, edist x y = Ennreal.ofReal (dist x y) :=  by 
  runTac 
    pseudo_metric_space.edist_dist_tac 
  toUniformSpace : UniformSpace α := uniformSpaceOfDist dist dist_self dist_comm dist_triangle 
  uniformity_dist : 𝓤 α = ⨅(ε : _)(_ : ε > 0), 𝓟 { p : α × α | dist p.1 p.2 < ε } :=  by 
  runTac 
    control_laws_tac

variable[PseudoMetricSpace α]

instance (priority := 100)MetricSpace.toUniformSpace' : UniformSpace α :=
  PseudoMetricSpace.toUniformSpace

instance (priority := 200)PseudoMetricSpace.toHasEdist : HasEdist α :=
  ⟨PseudoMetricSpace.edist⟩

/-- Construct a pseudo-metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def PseudoMetricSpace.ofMetrizable {α : Type _} [TopologicalSpace α] (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y+dist y z)
  (H : ∀ s : Set α, IsOpen s ↔ ∀ x _ : x ∈ s, ∃ (ε : _)(_ : ε > 0), ∀ y, dist x y < ε → y ∈ s) : PseudoMetricSpace α :=
  { dist, dist_self, dist_comm, dist_triangle,
    toUniformSpace :=
      { UniformSpace.coreOfDist dist dist_self dist_comm dist_triangle with
        is_open_uniformity :=
          by 
            dsimp only [UniformSpace.coreOfDist]
            intro s 
            change IsOpen s ↔ _ 
            rw [H s]
            apply forall_congrₓ 
            intro x 
            apply forall_congrₓ 
            intro x_in 
            erw [(has_basis_binfi_principal _ nonempty_Ioi).mem_iff]
            ·
              apply exists_congr 
              intro ε 
              apply exists_congr 
              intro ε_pos 
              simp only [Prod.forall, set_of_subset_set_of]
              split 
              ·
                rintro h _ y H rfl 
                exact h y H
              ·
                intro h y hxy 
                exact h _ _ hxy rfl
            ·
              exact
                fun r hr : 0 < r p hp : 0 < p =>
                  ⟨min r p, lt_minₓ hr hp, fun x hx : dist _ _ < _ => lt_of_lt_of_leₓ hx (min_le_leftₓ r p),
                    fun x hx : dist _ _ < _ => lt_of_lt_of_leₓ hx (min_le_rightₓ r p)⟩
            ·
              infer_instance },
    uniformity_dist := rfl }

@[simp]
theorem dist_self (x : α) : dist x x = 0 :=
  PseudoMetricSpace.dist_self x

theorem dist_comm (x y : α) : dist x y = dist y x :=
  PseudoMetricSpace.dist_comm x y

theorem edist_dist (x y : α) : edist x y = Ennreal.ofReal (dist x y) :=
  PseudoMetricSpace.edist_dist x y

theorem dist_triangle (x y z : α) : dist x z ≤ dist x y+dist y z :=
  PseudoMetricSpace.dist_triangle x y z

theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x+dist z y :=
  by 
    rw [dist_comm z] <;> apply dist_triangle

theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z+dist y z :=
  by 
    rw [dist_comm y] <;> apply dist_triangle

theorem dist_triangle4 (x y z w : α) : dist x w ≤ (dist x y+dist y z)+dist z w :=
  calc dist x w ≤ dist x z+dist z w := dist_triangle x z w 
    _ ≤ (dist x y+dist y z)+dist z w := add_le_add_right (dist_triangle x y z) _
    

theorem dist_triangle4_left (x₁ y₁ x₂ y₂ : α) : dist x₂ y₂ ≤ dist x₁ y₁+dist x₁ x₂+dist y₁ y₂ :=
  by 
    rw [add_left_commₓ, dist_comm x₁, ←add_assocₓ]
    apply dist_triangle4

theorem dist_triangle4_right (x₁ y₁ x₂ y₂ : α) : dist x₁ y₁ ≤ (dist x₁ x₂+dist y₁ y₂)+dist x₂ y₂ :=
  by 
    rw [add_right_commₓ, dist_comm y₁]
    apply dist_triangle4

/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
theorem dist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
  dist (f m) (f n) ≤ ∑i in Finset.ico m n, dist (f i) (f (i+1)) :=
  by 
    revert n 
    apply Nat.le_induction
    ·
      simp only [Finset.sum_empty, Finset.Ico_self, dist_self]
    ·
      intro n hn hrec 
      calc dist (f m) (f (n+1)) ≤ dist (f m) (f n)+dist _ _ := dist_triangle _ _ _ _ ≤ (∑i in Finset.ico m n, _)+_ :=
        add_le_add hrec (le_reflₓ _)_ = ∑i in Finset.ico m (n+1), _ :=
        by 
          rw [Nat.Ico_succ_right_eq_insert_Ico hn, Finset.sum_insert, add_commₓ] <;> simp 

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
theorem dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) : dist (f 0) (f n) ≤ ∑i in Finset.range n, dist (f i) (f (i+1)) :=
  Nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_dist f (Nat.zero_leₓ n)

/-- A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ}
  (hd : ∀ {k}, m ≤ k → k < n → dist (f k) (f (k+1)) ≤ d k) : dist (f m) (f n) ≤ ∑i in Finset.ico m n, d i :=
  le_transₓ (dist_le_Ico_sum_dist f hmn)$
    Finset.sum_le_sum$ fun k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ} (hd : ∀ {k}, k < n → dist (f k) (f (k+1)) ≤ d k) :
  dist (f 0) (f n) ≤ ∑i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_of_dist_le (zero_le n) fun _ _ => hd

theorem swap_dist : Function.swap (@dist α _) = dist :=
  by 
    funext x y <;> exact dist_comm _ _

theorem abs_dist_sub_le (x y z : α) : |dist x z - dist y z| ≤ dist x y :=
  abs_sub_le_iff.2 ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _), sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩

theorem dist_nonneg {x y : α} : 0 ≤ dist x y :=
  pseudo_metric_space.dist_nonneg' dist dist_self dist_comm dist_triangle

@[simp]
theorem abs_dist {a b : α} : |dist a b| = dist a b :=
  abs_of_nonneg dist_nonneg

/-- A version of `has_dist` that takes value in `ℝ≥0`. -/
class HasNndist(α : Type _) where 
  nndist : α → α →  ℝ≥0 

export HasNndist(nndist)

/-- Distance as a nonnegative real number. -/
instance (priority := 100)PseudoMetricSpace.toHasNndist : HasNndist α :=
  ⟨fun a b => ⟨dist a b, dist_nonneg⟩⟩

/--Express `nndist` in terms of `edist`-/
theorem nndist_edist (x y : α) : nndist x y = (edist x y).toNnreal :=
  by 
    simp [nndist, edist_dist, Real.toNnreal, max_eq_leftₓ dist_nonneg, Ennreal.ofReal]

/--Express `edist` in terms of `nndist`-/
theorem edist_nndist (x y : α) : edist x y = «expr↑ » (nndist x y) :=
  by 
    simpa only [edist_dist, Ennreal.of_real_eq_coe_nnreal dist_nonneg]

@[simp, normCast]
theorem coe_nnreal_ennreal_nndist (x y : α) : «expr↑ » (nndist x y) = edist x y :=
  (edist_nndist x y).symm

@[simp, normCast]
theorem edist_lt_coe {x y : α} {c :  ℝ≥0 } : edist x y < c ↔ nndist x y < c :=
  by 
    rw [edist_nndist, Ennreal.coe_lt_coe]

@[simp, normCast]
theorem edist_le_coe {x y : α} {c :  ℝ≥0 } : edist x y ≤ c ↔ nndist x y ≤ c :=
  by 
    rw [edist_nndist, Ennreal.coe_le_coe]

/--In a pseudometric space, the extended distance is always finite-/
theorem edist_lt_top {α : Type _} [PseudoMetricSpace α] (x y : α) : edist x y < ⊤ :=
  (edist_dist x y).symm ▸ Ennreal.of_real_lt_top

/--In a pseudometric space, the extended distance is always finite-/
theorem edist_ne_top (x y : α) : edist x y ≠ ⊤ :=
  (edist_lt_top x y).Ne

/--`nndist x x` vanishes-/
@[simp]
theorem nndist_self (a : α) : nndist a a = 0 :=
  (Nnreal.coe_eq_zero _).1 (dist_self a)

/--Express `dist` in terms of `nndist`-/
theorem dist_nndist (x y : α) : dist x y = «expr↑ » (nndist x y) :=
  rfl

@[simp, normCast]
theorem coe_nndist (x y : α) : «expr↑ » (nndist x y) = dist x y :=
  (dist_nndist x y).symm

@[simp, normCast]
theorem dist_lt_coe {x y : α} {c :  ℝ≥0 } : dist x y < c ↔ nndist x y < c :=
  Iff.rfl

@[simp, normCast]
theorem dist_le_coe {x y : α} {c :  ℝ≥0 } : dist x y ≤ c ↔ nndist x y ≤ c :=
  Iff.rfl

/--Express `nndist` in terms of `dist`-/
theorem nndist_dist (x y : α) : nndist x y = Real.toNnreal (dist x y) :=
  by 
    rw [dist_nndist, Real.to_nnreal_coe]

theorem nndist_comm (x y : α) : nndist x y = nndist y x :=
  by 
    simpa only [dist_nndist, Nnreal.coe_eq] using dist_comm x y

/--Triangle inequality for the nonnegative distance-/
theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y+nndist y z :=
  dist_triangle _ _ _

theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x+nndist z y :=
  dist_triangle_left _ _ _

theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z+nndist y z :=
  dist_triangle_right _ _ _

/--Express `dist` in terms of `edist`-/
theorem dist_edist (x y : α) : dist x y = (edist x y).toReal :=
  by 
    rw [edist_dist, Ennreal.to_real_of_real dist_nonneg]

namespace Metric

variable{x y z : α}{ε ε₁ ε₂ : ℝ}{s : Set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε :=
  Iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε :=
  by 
    rw [dist_comm] <;> rfl

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  dist_nonneg.trans_lt hy

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
  show dist x x < ε by 
    rw [dist_self] <;> assumption

@[simp]
theorem nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε :=
  ⟨fun ⟨x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩

@[simp]
theorem ball_eq_empty : ball x ε = ∅ ↔ ε ≤ 0 :=
  by 
    rw [←not_nonempty_iff_eq_empty, nonempty_ball, not_ltₓ]

@[simp]
theorem ball_zero : ball x 0 = ∅ :=
  by 
    rw [ball_eq_empty]

theorem ball_eq_ball (ε : ℝ) (x : α) : UniformSpace.Ball x { p | dist p.2 p.1 < ε } = Metric.Ball x ε :=
  rfl

theorem ball_eq_ball' (ε : ℝ) (x : α) : UniformSpace.Ball x { p | dist p.1 p.2 < ε } = Metric.Ball x ε :=
  by 
    ext 
    simp [dist_comm, UniformSpace.Ball]

@[simp]
theorem Union_ball_nat (x : α) : (⋃n : ℕ, ball x n) = univ :=
  Union_eq_univ_iff.2$ fun y => exists_nat_gt (dist y x)

@[simp]
theorem Union_ball_nat_succ (x : α) : (⋃n : ℕ, ball x (n+1)) = univ :=
  Union_eq_univ_iff.2$ fun y => (exists_nat_gt (dist y x)).imp$ fun n hn => hn.trans (lt_add_one _)

/-- `closed_ball x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closed_ball (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }

@[simp]
theorem mem_closed_ball : y ∈ closed_ball x ε ↔ dist y x ≤ ε :=
  Iff.rfl

/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
def sphere (x : α) (ε : ℝ) :=
  { y | dist y x = ε }

@[simp]
theorem mem_sphere : y ∈ sphere x ε ↔ dist y x = ε :=
  Iff.rfl

theorem mem_closed_ball' : y ∈ closed_ball x ε ↔ dist x y ≤ ε :=
  by 
    rw [dist_comm]
    rfl

theorem mem_closed_ball_self (h : 0 ≤ ε) : x ∈ closed_ball x ε :=
  show dist x x ≤ ε by 
    rw [dist_self] <;> assumption

@[simp]
theorem nonempty_closed_ball : (closed_ball x ε).Nonempty ↔ 0 ≤ ε :=
  ⟨fun ⟨x, hx⟩ => dist_nonneg.trans hx, fun h => ⟨x, mem_closed_ball_self h⟩⟩

@[simp]
theorem closed_ball_eq_empty : closed_ball x ε = ∅ ↔ ε < 0 :=
  by 
    rw [←not_nonempty_iff_eq_empty, nonempty_closed_ball, not_leₓ]

theorem ball_subset_closed_ball : ball x ε ⊆ closed_ball x ε :=
  fun y hy : _ < _ => le_of_ltₓ hy

theorem sphere_subset_closed_ball : sphere x ε ⊆ closed_ball x ε :=
  fun y => le_of_eqₓ

theorem ball_disjoint_ball (x y : α) (rx ry : ℝ) (h : (rx+ry) ≤ dist x y) : Disjoint (ball x rx) (ball y ry) :=
  by 
    rw [disjoint_left]
    intro a ax ay 
    apply lt_irreflₓ (dist x y)
    calc dist x y ≤ dist x a+dist a y := dist_triangle _ _ _ _ < rx+ry :=
      add_lt_add (mem_ball'.1 ax) (mem_ball.1 ay)_ ≤ dist x y := h

theorem sphere_disjoint_ball : Disjoint (sphere x ε) (ball x ε) :=
  fun y ⟨hy₁, hy₂⟩ => absurd hy₁$ ne_of_ltₓ hy₂

@[simp]
theorem ball_union_sphere : ball x ε ∪ sphere x ε = closed_ball x ε :=
  Set.ext$ fun y => (@le_iff_lt_or_eqₓ ℝ _ _ _).symm

@[simp]
theorem sphere_union_ball : sphere x ε ∪ ball x ε = closed_ball x ε :=
  by 
    rw [union_comm, ball_union_sphere]

@[simp]
theorem closed_ball_diff_sphere : closed_ball x ε \ sphere x ε = ball x ε :=
  by 
    rw [←ball_union_sphere, Set.union_diff_cancel_right sphere_disjoint_ball.symm]

@[simp]
theorem closed_ball_diff_ball : closed_ball x ε \ ball x ε = sphere x ε :=
  by 
    rw [←ball_union_sphere, Set.union_diff_cancel_left sphere_disjoint_ball.symm]

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
  by 
    simp [dist_comm]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
  fun y yx : _ < ε₁ => lt_of_lt_of_leₓ yx h

theorem ball_subset_ball' (h : (ε₁+dist x y) ≤ ε₂) : ball x ε₁ ⊆ ball y ε₂ :=
  fun z hz =>
    calc dist z y ≤ dist z x+dist x y := dist_triangle _ _ _ 
      _ < ε₁+dist x y := add_lt_add_right hz _ 
      _ ≤ ε₂ := h
      

theorem closed_ball_subset_closed_ball (h : ε₁ ≤ ε₂) : closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
  fun y yx : _ ≤ ε₁ => le_transₓ yx h

theorem closed_ball_subset_closed_ball' (h : (ε₁+dist x y) ≤ ε₂) : closed_ball x ε₁ ⊆ closed_ball y ε₂ :=
  fun z hz =>
    calc dist z y ≤ dist z x+dist x y := dist_triangle _ _ _ 
      _ ≤ ε₁+dist x y := add_le_add_right hz _ 
      _ ≤ ε₂ := h
      

theorem closed_ball_subset_ball (h : ε₁ < ε₂) : closed_ball x ε₁ ⊆ ball x ε₂ :=
  fun y yh : dist y x ≤ ε₁ => lt_of_le_of_ltₓ yh h

theorem dist_le_add_of_nonempty_closed_ball_inter_closed_ball (h : (closed_ball x ε₁ ∩ closed_ball y ε₂).Nonempty) :
  dist x y ≤ ε₁+ε₂ :=
  let ⟨z, hz⟩ := h 
  calc dist x y ≤ dist z x+dist z y := dist_triangle_left _ _ _ 
    _ ≤ ε₁+ε₂ := add_le_add hz.1 hz.2
    

theorem dist_lt_add_of_nonempty_closed_ball_inter_ball (h : (closed_ball x ε₁ ∩ ball y ε₂).Nonempty) :
  dist x y < ε₁+ε₂ :=
  let ⟨z, hz⟩ := h 
  calc dist x y ≤ dist z x+dist z y := dist_triangle_left _ _ _ 
    _ < ε₁+ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2
    

theorem dist_lt_add_of_nonempty_ball_inter_closed_ball (h : (ball x ε₁ ∩ closed_ball y ε₂).Nonempty) :
  dist x y < ε₁+ε₂ :=
  by 
    rw [inter_comm] at h 
    rw [add_commₓ, dist_comm]
    exact dist_lt_add_of_nonempty_closed_ball_inter_ball h

theorem dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ ∩ ball y ε₂).Nonempty) : dist x y < ε₁+ε₂ :=
  dist_lt_add_of_nonempty_closed_ball_inter_ball$ h.mono (inter_subset_inter ball_subset_closed_ball subset.rfl)

@[simp]
theorem Union_closed_ball_nat (x : α) : (⋃n : ℕ, closed_ball x n) = univ :=
  Union_eq_univ_iff.2$ fun y => exists_nat_ge (dist y x)

theorem ball_disjoint (h : (ε₁+ε₂) ≤ dist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ :=
  eq_empty_iff_forall_not_mem.2$
    fun z ⟨h₁, h₂⟩ => not_lt_of_le (dist_triangle_left x y z) (lt_of_lt_of_leₓ (add_lt_add h₁ h₂) h)

theorem ball_disjoint_same (h : ε ≤ dist x y / 2) : ball x ε ∩ ball y ε = ∅ :=
  ball_disjoint$
    by 
      rwa [←two_mul, ←le_div_iff' (@zero_lt_two ℝ _ _)]

theorem ball_subset (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ :=
  fun z zx =>
    by 
      rw [←add_sub_cancel'_right ε₁ ε₂] <;> exact lt_of_le_of_ltₓ (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)

theorem ball_half_subset y (h : y ∈ ball x (ε / 2)) : ball y (ε / 2) ⊆ ball x ε :=
  ball_subset$
    by 
      rw [sub_self_div_two] <;> exact le_of_ltₓ h

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ (ε' : _)(_ : ε' > 0), ball y ε' ⊆ ball x ε :=
  ⟨_, sub_pos.2 h,
    ball_subset$
      by 
        rw [sub_sub_self]⟩

theorem uniformity_basis_dist : (𝓤 α).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε } :=
  by 
    rw [←pseudo_metric_space.uniformity_dist.symm]
    refine' has_basis_binfi_principal _ nonempty_Ioi 
    exact
      fun r hr : 0 < r p hp : 0 < p =>
        ⟨min r p, lt_minₓ hr hp, fun x hx : dist _ _ < _ => lt_of_lt_of_leₓ hx (min_le_leftₓ r p),
          fun x hx : dist _ _ < _ => lt_of_lt_of_leₓ hx (min_le_rightₓ r p)⟩

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_dist`, `uniformity_basis_dist_inv_nat_succ`,
and `uniformity_basis_dist_inv_nat_pos`. -/
protected theorem mk_uniformity_basis {β : Type _} {p : β → Prop} {f : β → ℝ} (hf₀ : ∀ i, p i → 0 < f i)
  (hf : ∀ ⦃ε⦄, 0 < ε → ∃ (i : _)(hi : p i), f i ≤ ε) : (𝓤 α).HasBasis p fun i => { p : α × α | dist p.1 p.2 < f i } :=
  by 
    refine' ⟨fun s => uniformity_basis_dist.mem_iff.trans _⟩
    split 
    ·
      rintro ⟨ε, ε₀, hε⟩
      obtain ⟨i, hi, H⟩ : ∃ (i : _)(hi : p i), f i ≤ ε 
      exact hf ε₀ 
      exact ⟨i, hi, fun x hx : _ < _ => hε$ lt_of_lt_of_leₓ hx H⟩
    ·
      exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

theorem uniformity_basis_dist_inv_nat_succ :
  (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 < 1 / «expr↑ » n+1 } :=
  Metric.mk_uniformity_basis (fun n _ => div_pos zero_lt_one$ Nat.cast_add_one_pos n)
    fun ε ε0 => (exists_nat_one_div_lt ε0).imp$ fun n hn => ⟨trivialₓ, le_of_ltₓ hn⟩

theorem uniformity_basis_dist_inv_nat_pos :
  (𝓤 α).HasBasis (fun n : ℕ => 0 < n) fun n : ℕ => { p : α × α | dist p.1 p.2 < 1 / «expr↑ » n } :=
  Metric.mk_uniformity_basis (fun n hn => div_pos zero_lt_one$ Nat.cast_pos.2 hn)
    fun ε ε0 =>
      let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
      ⟨n+1, Nat.succ_posₓ n, hn.le⟩

theorem uniformity_basis_dist_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
  (𝓤 α).HasBasis (fun n : ℕ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 < r ^ n } :=
  Metric.mk_uniformity_basis (fun n hn => pow_pos h0 _)
    fun ε ε0 =>
      let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
      ⟨n, trivialₓ, hn.le⟩

theorem uniformity_basis_dist_lt {R : ℝ} (hR : 0 < R) :
  (𝓤 α).HasBasis (fun r : ℝ => 0 < r ∧ r < R) fun r => { p : α × α | dist p.1 p.2 < r } :=
  (Metric.mk_uniformity_basis fun r => And.left)$
    fun r hr => ⟨min r (R / 2), ⟨lt_minₓ hr (half_pos hR), min_lt_iff.2$ Or.inr (half_lt_self hR)⟩, min_le_leftₓ _ _⟩

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed neighborhoods of the diagonal of sizes `{f i | p i}`
form a basis of `𝓤 α`.

Currently we have only one specific basis `uniformity_basis_dist_le` based on this constructor.
More can be easily added if needed in the future. -/
protected theorem mk_uniformity_basis_le {β : Type _} {p : β → Prop} {f : β → ℝ} (hf₀ : ∀ x, p x → 0 < f x)
  (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) : (𝓤 α).HasBasis p fun x => { p : α × α | dist p.1 p.2 ≤ f x } :=
  by 
    refine' ⟨fun s => uniformity_basis_dist.mem_iff.trans _⟩
    split 
    ·
      rintro ⟨ε, ε₀, hε⟩
      rcases exists_between ε₀ with ⟨ε', hε'⟩
      rcases hf ε' hε'.1 with ⟨i, hi, H⟩
      exact ⟨i, hi, fun x hx : _ ≤ _ => hε$ lt_of_le_of_ltₓ (le_transₓ hx H) hε'.2⟩
    ·
      exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx : _ < _ => H (le_of_ltₓ hx)⟩

/-- Contant size closed neighborhoods of the diagonal form a basis
of the uniformity filter. -/
theorem uniformity_basis_dist_le : (𝓤 α).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 ≤ ε } :=
  Metric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_reflₓ ε⟩

theorem uniformity_basis_dist_le_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
  (𝓤 α).HasBasis (fun n : ℕ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 ≤ r ^ n } :=
  Metric.mk_uniformity_basis_le (fun n hn => pow_pos h0 _)
    fun ε ε0 =>
      let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
      ⟨n, trivialₓ, hn.le⟩

theorem mem_uniformity_dist {s : Set (α × α)} :
  s ∈ 𝓤 α ↔ ∃ (ε : _)(_ : ε > 0), ∀ {a b : α}, dist a b < ε → (a, b) ∈ s :=
  uniformity_basis_dist.mem_uniformity_iff

/-- A constant size neighborhood of the diagonal is an entourage. -/
theorem dist_mem_uniformity {ε : ℝ} (ε0 : 0 < ε) : { p : α × α | dist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_dist.2 ⟨ε, ε0, fun a b => id⟩

theorem uniform_continuous_iff [PseudoMetricSpace β] {f : α → β} :
  UniformContinuous f ↔ ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε :=
  uniformity_basis_dist.uniform_continuous_iff uniformity_basis_dist

theorem uniform_continuous_on_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
  UniformContinuousOn f s ↔
    ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ x y _ : x ∈ s _ : y ∈ s, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformity_basis_dist.uniform_continuous_on_iff Metric.uniformity_basis_dist

theorem uniform_continuous_on_iff_le [PseudoMetricSpace β] {f : α → β} {s : Set α} :
  UniformContinuousOn f s ↔
    ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ x y _ : x ∈ s _ : y ∈ s, dist x y ≤ δ → dist (f x) (f y) ≤ ε :=
  Metric.uniformity_basis_dist_le.uniform_continuous_on_iff Metric.uniformity_basis_dist_le

theorem uniform_embedding_iff [PseudoMetricSpace β] {f : α → β} :
  UniformEmbedding f ↔
    Function.Injective f ∧
      UniformContinuous f ∧ ∀ δ _ : δ > 0, ∃ (ε : _)(_ : ε > 0), ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  uniform_embedding_def'.trans$
    and_congr Iff.rfl$
      and_congr Iff.rfl
        ⟨fun H δ δ0 =>
            let ⟨t, tu, ht⟩ := H _ (dist_mem_uniformity δ0)
            let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 tu
            ⟨ε, ε0, fun a b h => ht _ _ (hε h)⟩,
          fun H s su =>
            let ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 su 
            let ⟨ε, ε0, hε⟩ := H _ δ0
            ⟨_, dist_mem_uniformity ε0, fun a b h => hδ (hε h)⟩⟩

/-- If a map between pseudometric spaces is a uniform embedding then the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniform_embedding [PseudoMetricSpace β] {f : α → β} :
  UniformEmbedding f →
    (∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
      ∀ δ _ : δ > 0, ∃ (ε : _)(_ : ε > 0), ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  by 
    intro h 
    exact ⟨uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1, (uniform_embedding_iff.1 h).2.2⟩

theorem totally_bounded_iff {s : Set α} :
  TotallyBounded s ↔ ∀ ε _ : ε > 0, ∃ t : Set α, finite t ∧ s ⊆ ⋃(y : _)(_ : y ∈ t), ball y ε :=
  ⟨fun H ε ε0 => H _ (dist_mem_uniformity ε0),
    fun H r ru =>
      let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru 
      let ⟨t, ft, h⟩ := H ε ε0
      ⟨t, ft, subset.trans h$ Union_subset_Union$ fun y => Union_subset_Union$ fun yt z => hε⟩⟩

/-- A pseudometric space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
theorem totally_bounded_of_finite_discretization {s : Set α}
  (H : ∀ ε _ : ε > (0 : ℝ), ∃ (β : Type u)(_ : Fintype β)(F : s → β), ∀ x y, F x = F y → dist (x : α) y < ε) :
  TotallyBounded s :=
  by 
    cases' s.eq_empty_or_nonempty with hs hs
    ·
      rw [hs]
      exact totally_bounded_empty 
    rcases hs with ⟨x0, hx0⟩
    haveI  : Inhabited s := ⟨⟨x0, hx0⟩⟩
    refine' totally_bounded_iff.2 fun ε ε0 => _ 
    rcases H ε ε0 with ⟨β, fβ, F, hF⟩
    resetI 
    let Finv := Function.invFun F 
    refine' ⟨range (Subtype.val ∘ Finv), finite_range _, fun x xs => _⟩
    let x' := Finv (F ⟨x, xs⟩)
    have  : F x' = F ⟨x, xs⟩ := Function.inv_fun_eq ⟨⟨x, xs⟩, rfl⟩
    simp only [Set.mem_Union, Set.mem_range]
    exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩

theorem finite_approx_of_totally_bounded {s : Set α} (hs : TotallyBounded s) :
  ∀ ε _ : ε > 0, ∃ (t : _)(_ : t ⊆ s), finite t ∧ s ⊆ ⋃(y : _)(_ : y ∈ t), ball y ε :=
  by 
    intro ε ε_pos 
    rw [totally_bounded_iff_subset] at hs 
    exact hs _ (dist_mem_uniformity ε_pos)

/-- Expressing locally uniform convergence on a set using `dist`. -/
theorem tendsto_locally_uniformly_on_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α} {p : Filter ι}
  {s : Set β} :
  TendstoLocallyUniformlyOn F f p s ↔
    ∀ ε _ : ε > 0, ∀ x _ : x ∈ s, ∃ (t : _)(_ : t ∈ 𝓝[s] x), ∀ᶠn in p, ∀ y _ : y ∈ t, dist (f y) (F n y) < ε :=
  by 
    refine' ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu x hx => _⟩
    rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
    rcases H ε εpos x hx with ⟨t, ht, Ht⟩
    exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/-- Expressing uniform convergence on a set using `dist`. -/
theorem tendsto_uniformly_on_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
  TendstoUniformlyOn F f p s ↔ ∀ ε _ : ε > 0, ∀ᶠn in p, ∀ x _ : x ∈ s, dist (f x) (F n x) < ε :=
  by 
    refine' ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => _⟩
    rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
    exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/-- Expressing locally uniform convergence using `dist`. -/
theorem tendsto_locally_uniformly_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α} {p : Filter ι} :
  TendstoLocallyUniformly F f p ↔
    ∀ ε _ : ε > 0, ∀ x : β, ∃ (t : _)(_ : t ∈ 𝓝 x), ∀ᶠn in p, ∀ y _ : y ∈ t, dist (f y) (F n y) < ε :=
  by 
    simp only [←tendsto_locally_uniformly_on_univ, tendsto_locally_uniformly_on_iff, nhds_within_univ, mem_univ,
      forall_const, exists_prop]

/-- Expressing uniform convergence using `dist`. -/
theorem tendsto_uniformly_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} :
  TendstoUniformly F f p ↔ ∀ ε _ : ε > 0, ∀ᶠn in p, ∀ x, dist (f x) (F n x) < ε :=
  by 
    rw [←tendsto_uniformly_on_univ, tendsto_uniformly_on_iff]
    simp 

protected theorem cauchy_iff {f : Filter α} :
  Cauchy f ↔ ne_bot f ∧ ∀ ε _ : ε > 0, ∃ (t : _)(_ : t ∈ f), ∀ x y _ : x ∈ t _ : y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff

theorem nhds_basis_ball : (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) (ball x) :=
  nhds_basis_uniformity uniformity_basis_dist

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ (ε : _)(_ : ε > 0), ball x ε ⊆ s :=
  nhds_basis_ball.mem_iff

theorem eventually_nhds_iff {p : α → Prop} : (∀ᶠy in 𝓝 x, p y) ↔ ∃ (ε : _)(_ : ε > 0), ∀ ⦃y⦄, dist y x < ε → p y :=
  mem_nhds_iff

theorem eventually_nhds_iff_ball {p : α → Prop} : (∀ᶠy in 𝓝 x, p y) ↔ ∃ (ε : _)(_ : ε > 0), ∀ y _ : y ∈ ball x ε, p y :=
  mem_nhds_iff

theorem nhds_basis_closed_ball : (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) (closed_ball x) :=
  nhds_basis_uniformity uniformity_basis_dist_le

theorem nhds_basis_ball_inv_nat_succ : (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => ball x (1 / «expr↑ » n+1) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ

theorem nhds_basis_ball_inv_nat_pos : (𝓝 x).HasBasis (fun n => 0 < n) fun n : ℕ => ball x (1 / «expr↑ » n) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos

theorem nhds_basis_ball_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
  (𝓝 x).HasBasis (fun n => True) fun n : ℕ => ball x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_pow h0 h1)

theorem nhds_basis_closed_ball_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
  (𝓝 x).HasBasis (fun n => True) fun n : ℕ => closed_ball x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

theorem is_open_iff : IsOpen s ↔ ∀ x _ : x ∈ s, ∃ (ε : _)(_ : ε > 0), ball x ε ⊆ s :=
  by 
    simp only [is_open_iff_mem_nhds, mem_nhds_iff]

theorem is_open_ball : IsOpen (ball x ε) :=
  is_open_iff.2$ fun y => exists_ball_subset_ball

theorem ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
  IsOpen.mem_nhds is_open_ball (mem_ball_self ε0)

theorem closed_ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : closed_ball x ε ∈ 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closed_ball

theorem nhds_within_basis_ball {s : Set α} : (𝓝[s] x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => ball x ε ∩ s :=
  nhds_within_has_basis nhds_basis_ball s

theorem mem_nhds_within_iff {t : Set α} : s ∈ 𝓝[t] x ↔ ∃ (ε : _)(_ : ε > 0), ball x ε ∩ t ⊆ s :=
  nhds_within_basis_ball.mem_iff

theorem tendsto_nhds_within_nhds_within [PseudoMetricSpace β] {t : Set β} {f : α → β} {a b} :
  tendsto f (𝓝[s] a) (𝓝[t] b) ↔
    ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {x : α}, x ∈ s → dist x a < δ → f x ∈ t ∧ dist (f x) b < ε :=
  (nhds_within_basis_ball.tendsto_iff nhds_within_basis_ball).trans$
    by 
      simp only [inter_comm, mem_inter_iff, and_imp, mem_ball]

theorem tendsto_nhds_within_nhds [PseudoMetricSpace β] {f : α → β} {a b} :
  tendsto f (𝓝[s] a) (𝓝 b) ↔ ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {x : α}, x ∈ s → dist x a < δ → dist (f x) b < ε :=
  by 
    rw [←nhds_within_univ b, tendsto_nhds_within_nhds_within]
    simp only [mem_univ, true_andₓ]

theorem tendsto_nhds_nhds [PseudoMetricSpace β] {f : α → β} {a b} :
  tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {x : α}, dist x a < δ → dist (f x) b < ε :=
  nhds_basis_ball.tendsto_iff nhds_basis_ball

theorem continuous_at_iff [PseudoMetricSpace β] {f : α → β} {a : α} :
  ContinuousAt f a ↔ ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {x : α}, dist x a < δ → dist (f x) (f a) < ε :=
  by 
    rw [ContinuousAt, tendsto_nhds_nhds]

theorem continuous_within_at_iff [PseudoMetricSpace β] {f : α → β} {a : α} {s : Set α} :
  ContinuousWithinAt f s a ↔
    ∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {x : α}, x ∈ s → dist x a < δ → dist (f x) (f a) < ε :=
  by 
    rw [ContinuousWithinAt, tendsto_nhds_within_nhds]

theorem continuous_on_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
  ContinuousOn f s ↔
    ∀ b _ : b ∈ s ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ a _ : a ∈ s, dist a b < δ → dist (f a) (f b) < ε :=
  by 
    simp [ContinuousOn, continuous_within_at_iff]

theorem continuous_iff [PseudoMetricSpace β] {f : α → β} :
  Continuous f ↔ ∀ b ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ a, dist a b < δ → dist (f a) (f b) < ε :=
  continuous_iff_continuous_at.trans$ forall_congrₓ$ fun b => tendsto_nhds_nhds

theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
  tendsto u f (𝓝 a) ↔ ∀ ε _ : ε > 0, ∀ᶠx in f, dist (u x) a < ε :=
  nhds_basis_ball.tendsto_right_iff

theorem continuous_at_iff' [TopologicalSpace β] {f : β → α} {b : β} :
  ContinuousAt f b ↔ ∀ ε _ : ε > 0, ∀ᶠx in 𝓝 b, dist (f x) (f b) < ε :=
  by 
    rw [ContinuousAt, tendsto_nhds]

theorem continuous_within_at_iff' [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
  ContinuousWithinAt f s b ↔ ∀ ε _ : ε > 0, ∀ᶠx in 𝓝[s] b, dist (f x) (f b) < ε :=
  by 
    rw [ContinuousWithinAt, tendsto_nhds]

theorem continuous_on_iff' [TopologicalSpace β] {f : β → α} {s : Set β} :
  ContinuousOn f s ↔ ∀ b _ : b ∈ s ε _ : ε > 0, ∀ᶠx in 𝓝[s] b, dist (f x) (f b) < ε :=
  by 
    simp [ContinuousOn, continuous_within_at_iff']

theorem continuous_iff' [TopologicalSpace β] {f : β → α} :
  Continuous f ↔ ∀ a ε _ : ε > 0, ∀ᶠx in 𝓝 a, dist (f x) (f a) < ε :=
  continuous_iff_continuous_at.trans$ forall_congrₓ$ fun b => tendsto_nhds

theorem tendsto_at_top [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
  tendsto u at_top (𝓝 a) ↔ ∀ ε _ : ε > 0, ∃ N, ∀ n _ : n ≥ N, dist (u n) a < ε :=
  (at_top_basis.tendsto_iff nhds_basis_ball).trans$
    by 
      simp only [exists_prop, true_andₓ]
      rfl

/--
A variant of `tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem tendsto_at_top' [Nonempty β] [SemilatticeSup β] [NoTopOrder β] {u : β → α} {a : α} :
  tendsto u at_top (𝓝 a) ↔ ∀ ε _ : ε > 0, ∃ N, ∀ n _ : n > N, dist (u n) a < ε :=
  (at_top_basis_Ioi.tendsto_iff nhds_basis_ball).trans$
    by 
      simp only [exists_prop, true_andₓ]
      rfl

theorem is_open_singleton_iff {α : Type _} [PseudoMetricSpace α] {x : α} :
  IsOpen ({x} : Set α) ↔ ∃ (ε : _)(_ : ε > 0), ∀ y, dist y x < ε → y = x :=
  by 
    simp [is_open_iff, subset_singleton_iff, mem_ball]

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is an open ball
centered at `x` and intersecting `s` only at `x`. -/
theorem exists_ball_inter_eq_singleton_of_mem_discrete [DiscreteTopology s] {x : α} (hx : x ∈ s) :
  ∃ (ε : _)(_ : ε > 0), Metric.Ball x ε ∩ s = {x} :=
  nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hx

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is a closed ball
of positive radius centered at `x` and intersecting `s` only at `x`. -/
theorem exists_closed_ball_inter_eq_singleton_of_discrete [DiscreteTopology s] {x : α} (hx : x ∈ s) :
  ∃ (ε : _)(_ : ε > 0), Metric.ClosedBall x ε ∩ s = {x} :=
  nhds_basis_closed_ball.exists_inter_eq_singleton_of_mem_discrete hx

end Metric

open Metric

/-- Expressing the uniformity in terms of `edist` -/
protected theorem PseudoMetric.uniformity_basis_edist :
  (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p | edist p.1 p.2 < ε } :=
  ⟨by 
      intro t 
      refine' mem_uniformity_dist.trans ⟨_, _⟩ <;> rintro ⟨ε, ε0, Hε⟩
      ·
        use Ennreal.ofReal ε, Ennreal.of_real_pos.2 ε0 
        rintro ⟨a, b⟩
        simp only [edist_dist, Ennreal.of_real_lt_of_real_iff ε0]
        exact Hε
      ·
        rcases Ennreal.lt_iff_exists_real_btwn.1 ε0 with ⟨ε', _, ε0', hε⟩
        rw [Ennreal.of_real_pos] at ε0' 
        refine' ⟨ε', ε0', fun a b h => Hε (lt_transₓ _ hε)⟩
        rwa [edist_dist, Ennreal.of_real_lt_of_real_iff ε0']⟩

theorem Metric.uniformity_edist : 𝓤 α = ⨅(ε : _)(_ : ε > 0), 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  PseudoMetric.uniformity_basis_edist.eq_binfi

/-- A pseudometric space induces a pseudoemetric space -/
instance (priority := 100)PseudoMetricSpace.toPseudoEmetricSpace : PseudoEmetricSpace α :=
  { ‹PseudoMetricSpace α› with edist := edist,
    edist_self :=
      by 
        simp [edist_dist],
    edist_comm :=
      by 
        simp only [edist_dist, dist_comm] <;> simp ,
    edist_triangle :=
      fun x y z =>
        by 
          simp only [edist_dist, ←Ennreal.of_real_add, dist_nonneg]
          rw [Ennreal.of_real_le_of_real_iff _]
          ·
            exact dist_triangle _ _ _
          ·
            simpa using add_le_add (dist_nonneg : 0 ≤ dist x y) dist_nonneg,
    uniformity_edist := Metric.uniformity_edist }

/-- In a pseudometric space, an open ball of infinite radius is the whole space -/
theorem Metric.eball_top_eq_univ (x : α) : Emetric.Ball x ∞ = Set.Univ :=
  Set.eq_univ_iff_forall.mpr fun y => edist_lt_top y x

/-- Balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_ball {x : α} {ε : ℝ} : Emetric.Ball x (Ennreal.ofReal ε) = ball x ε :=
  by 
    ext y 
    simp only [Emetric.mem_ball, mem_ball, edist_dist]
    exact Ennreal.of_real_lt_of_real_iff_of_nonneg dist_nonneg

/-- Balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_ball_nnreal {x : α} {ε :  ℝ≥0 } : Emetric.Ball x ε = ball x ε :=
  by 
    convert Metric.emetric_ball 
    simp 

/-- Closed balls defined using the distance or the edistance coincide -/
theorem Metric.emetric_closed_ball {x : α} {ε : ℝ} (h : 0 ≤ ε) :
  Emetric.ClosedBall x (Ennreal.ofReal ε) = closed_ball x ε :=
  by 
    ext y <;> simp [edist_dist] <;> rw [Ennreal.of_real_le_of_real_iff h]

/-- Closed balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_closed_ball_nnreal {x : α} {ε :  ℝ≥0 } : Emetric.ClosedBall x ε = closed_ball x ε :=
  by 
    convert Metric.emetric_closed_ball ε.2
    simp 

@[simp]
theorem Metric.emetric_ball_top (x : α) : Emetric.Ball x ⊤ = univ :=
  eq_univ_of_forall$ fun y => edist_lt_top _ _

/-- Build a new pseudometric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def PseudoMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
  (H : @uniformity _ U = @uniformity _ PseudoEmetricSpace.toUniformSpace') : PseudoMetricSpace α :=
  { dist := @dist _ m.to_has_dist, dist_self := dist_self, dist_comm := dist_comm, dist_triangle := dist_triangle,
    edist := edist, edist_dist := edist_dist, toUniformSpace := U,
    uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist }

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the pseudoemetric space. In this definition, the
distance is given separately, to be able to prescribe some expression which is not defeq to the
push-forward of the edistance to reals. -/
def PseudoEmetricSpace.toPseudoMetricSpaceOfDist {α : Type u} [e : PseudoEmetricSpace α] (dist : α → α → ℝ)
  (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤) (h : ∀ x y, dist x y = Ennreal.toReal (edist x y)) : PseudoMetricSpace α :=
  let m : PseudoMetricSpace α :=
    { dist,
      dist_self :=
        fun x =>
          by 
            simp [h],
      dist_comm :=
        fun x y =>
          by 
            simp [h, PseudoEmetricSpace.edist_comm],
      dist_triangle :=
        fun x y z =>
          by 
            simp only [h]
            rw [←Ennreal.to_real_add (edist_ne_top _ _) (edist_ne_top _ _),
              Ennreal.to_real_le_to_real (edist_ne_top _ _)]
            ·
              exact edist_triangle _ _ _
            ·
              simp [Ennreal.add_eq_top, edist_ne_top],
      edist := fun x y => edist x y,
      edist_dist :=
        fun x y =>
          by 
            simp [h, Ennreal.of_real_to_real, edist_ne_top] }
  m.replace_uniformity$
    by 
      rw [uniformity_pseudoedist, Metric.uniformity_edist]
      rfl

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the emetric space. -/
def PseudoEmetricSpace.toPseudoMetricSpace {α : Type u} [e : PseudoEmetricSpace α] (h : ∀ x y : α, edist x y ≠ ⊤) :
  PseudoMetricSpace α :=
  PseudoEmetricSpace.toPseudoMetricSpaceOfDist (fun x y => Ennreal.toReal (edist x y)) h fun x y => rfl

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `dist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem Metric.complete_of_convergent_controlled_sequences (B : ℕ → Real) (hB : ∀ n, 0 < B n)
  (H : ∀ u : ℕ → α, (∀ N n m : ℕ, N ≤ n → N ≤ m → dist (u n) (u m) < B N) → ∃ x, tendsto u at_top (𝓝 x)) :
  CompleteSpace α :=
  by 
    apply Emetric.complete_of_convergent_controlled_sequences fun n => Ennreal.ofReal (B n)
    ·
      simp [hB]
    ·
      intro u Hu 
      apply H 
      intro N n m hn hm 
      rw [←Ennreal.of_real_lt_of_real_iff (hB N), ←edist_dist]
      exact Hu N n m hn hm

theorem Metric.complete_of_cauchy_seq_tendsto :
  (∀ u : ℕ → α, CauchySeq u → ∃ a, tendsto u at_top (𝓝 a)) → CompleteSpace α :=
  Emetric.complete_of_cauchy_seq_tendsto

section Real

/-- Instantiate the reals as a pseudometric space. -/
noncomputable instance Real.pseudoMetricSpace : PseudoMetricSpace ℝ :=
  { dist := fun x y => |x - y|,
    dist_self :=
      by 
        simp [abs_zero],
    dist_comm := fun x y => abs_sub_comm _ _, dist_triangle := fun x y z => abs_sub_le _ _ _ }

theorem Real.dist_eq (x y : ℝ) : dist x y = |x - y| :=
  rfl

theorem Real.nndist_eq (x y : ℝ) : nndist x y = Real.nnabs (x - y) :=
  rfl

theorem Real.nndist_eq' (x y : ℝ) : nndist x y = Real.nnabs (y - x) :=
  nndist_comm _ _

theorem Real.dist_0_eq_abs (x : ℝ) : dist x 0 = |x| :=
  by 
    simp [Real.dist_eq]

theorem Real.dist_left_le_of_mem_interval {x y z : ℝ} (h : y ∈ interval x z) : dist x y ≤ dist x z :=
  by 
    simpa only [dist_comm x] using abs_sub_left_of_mem_interval h

theorem Real.dist_right_le_of_mem_interval {x y z : ℝ} (h : y ∈ interval x z) : dist y z ≤ dist x z :=
  by 
    simpa only [dist_comm _ z] using abs_sub_right_of_mem_interval h

theorem Real.dist_le_of_mem_interval {x y x' y' : ℝ} (hx : x ∈ interval x' y') (hy : y ∈ interval x' y') :
  dist x y ≤ dist x' y' :=
  abs_sub_le_of_subinterval$
    interval_subset_interval
      (by 
        rwa [interval_swap])
      (by 
        rwa [interval_swap])

theorem Real.dist_le_of_mem_Icc {x y x' y' : ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') : dist x y ≤ y' - x' :=
  by 
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2$ hx.1.trans hx.2), neg_sub] using
      Real.dist_le_of_mem_interval (Icc_subset_interval hx) (Icc_subset_interval hy)

theorem Real.dist_le_of_mem_Icc_01 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) : dist x y ≤ 1 :=
  by 
    simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy

instance  : OrderTopology ℝ :=
  order_topology_of_nhds_abs$
    fun x =>
      by 
        simp only [nhds_basis_ball.eq_binfi, ball, Real.dist_eq, abs_sub_comm]

theorem Real.ball_eq (x r : ℝ) : ball x r = Ioo (x - r) (x+r) :=
  Set.ext$
    fun y =>
      by 
        rw [mem_ball, dist_comm, Real.dist_eq, abs_sub_lt_iff, mem_Ioo, ←sub_lt_iff_lt_add', sub_lt]

theorem Real.closed_ball_eq {x r : ℝ} : closed_ball x r = Icc (x - r) (x+r) :=
  by 
    ext y <;> rw [mem_closed_ball, dist_comm, Real.dist_eq, abs_sub_le_iff, mem_Icc, ←sub_le_iff_le_add', sub_le]

section MetricOrdered

variable[ConditionallyCompleteLinearOrder α][OrderTopology α]

theorem totally_bounded_Icc (a b : α) : TotallyBounded (Icc a b) :=
  is_compact_Icc.TotallyBounded

theorem totally_bounded_Ico (a b : α) : TotallyBounded (Ico a b) :=
  totally_bounded_subset Ico_subset_Icc_self (totally_bounded_Icc a b)

theorem totally_bounded_Ioc (a b : α) : TotallyBounded (Ioc a b) :=
  totally_bounded_subset Ioc_subset_Icc_self (totally_bounded_Icc a b)

theorem totally_bounded_Ioo (a b : α) : TotallyBounded (Ioo a b) :=
  totally_bounded_subset Ioo_subset_Icc_self (totally_bounded_Icc a b)

end MetricOrdered

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
theorem squeeze_zero' {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ᶠt in t₀, 0 ≤ f t) (hft : ∀ᶠt in t₀, f t ≤ g t)
  (g0 : tendsto g t₀ (nhds 0)) : tendsto f t₀ (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and  `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
theorem squeeze_zero {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t)
  (g0 : tendsto g t₀ (𝓝 0)) : tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (eventually_of_forall hf) (eventually_of_forall hft) g0

theorem Metric.uniformity_eq_comap_nhds_zero : 𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : ℝ)) :=
  by 
    ext s 
    simp [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff, subset_def, Real.dist_0_eq_abs]

theorem cauchy_seq_iff_tendsto_dist_at_top_0 [Nonempty β] [SemilatticeSup β] {u : β → α} :
  CauchySeq u ↔ tendsto (fun n : β × β => dist (u n.1) (u n.2)) at_top (𝓝 0) :=
  by 
    rw [cauchy_seq_iff_tendsto, Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff, Prod.map_defₓ]

theorem tendsto_uniformity_iff_dist_tendsto_zero {ι : Type _} {f : ι → α × α} {p : Filter ι} :
  tendsto f p (𝓤 α) ↔ tendsto (fun x => dist (f x).1 (f x).2) p (𝓝 0) :=
  by 
    rw [Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff]

theorem Filter.Tendsto.congr_dist {ι : Type _} {f₁ f₂ : ι → α} {p : Filter ι} {a : α} (h₁ : tendsto f₁ p (𝓝 a))
  (h : tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : tendsto f₂ p (𝓝 a) :=
  h₁.congr_uniformity$ tendsto_uniformity_iff_dist_tendsto_zero.2 h

alias Filter.Tendsto.congr_dist ← tendsto_of_tendsto_of_dist

theorem tendsto_iff_of_dist {ι : Type _} {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
  (h : tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : tendsto f₁ p (𝓝 a) ↔ tendsto f₂ p (𝓝 a) :=
  Uniform.tendsto_congr$ tendsto_uniformity_iff_dist_tendsto_zero.2 h

end Real

section CauchySeq

variable[Nonempty β][SemilatticeSup β]

/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
@[nolint ge_or_gt]
theorem Metric.cauchy_seq_iff {u : β → α} :
  CauchySeq u ↔ ∀ ε _ : ε > 0, ∃ N, ∀ m n _ : m ≥ N _ : n ≥ N, dist (u m) (u n) < ε :=
  uniformity_basis_dist.cauchy_seq_iff

/-- A variation around the pseudometric characterization of Cauchy sequences -/
theorem Metric.cauchy_seq_iff' {u : β → α} : CauchySeq u ↔ ∀ ε _ : ε > 0, ∃ N, ∀ n _ : n ≥ N, dist (u n) (u N) < ε :=
  uniformity_basis_dist.cauchy_seq_iff'

/-- If the distance between `s n` and `s m`, `n, m ≥ N` is bounded above by `b N`
and `b` converges to zero, then `s` is a Cauchy sequence.  -/
theorem cauchy_seq_of_le_tendsto_0 {s : β → α} (b : β → ℝ) (h : ∀ n m N : β, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N)
  (h₀ : tendsto b at_top (nhds 0)) : CauchySeq s :=
  Metric.cauchy_seq_iff.2$
    fun ε ε0 =>
      (Metric.tendsto_at_top.1 h₀ ε ε0).imp$
        fun N hN m n hm hn =>
          calc dist (s m) (s n) ≤ b N := h m n N hm hn 
            _ ≤ |b N| := le_abs_self _ 
            _ = dist (b N) 0 :=
            by 
              rw [Real.dist_0_eq_abs] <;> rfl 
            _ < ε := hN _ (le_reflₓ N)
            

/-- A Cauchy sequence on the natural numbers is bounded. -/
theorem cauchy_seq_bdd {u : ℕ → α} (hu : CauchySeq u) : ∃ (R : _)(_ : R > 0), ∀ m n, dist (u m) (u n) < R :=
  by 
    rcases Metric.cauchy_seq_iff'.1 hu 1 zero_lt_one with ⟨N, hN⟩
    suffices  : ∃ (R : _)(_ : R > 0), ∀ n, dist (u n) (u N) < R
    ·
      rcases this with ⟨R, R0, H⟩
      exact ⟨_, add_pos R0 R0, fun m n => lt_of_le_of_ltₓ (dist_triangle_right _ _ _) (add_lt_add (H m) (H n))⟩
    let R := Finset.sup (Finset.range N) fun n => nndist (u n) (u N)
    refine' ⟨«expr↑ » R+1, add_pos_of_nonneg_of_pos R.2 zero_lt_one, fun n => _⟩
    cases le_or_ltₓ N n
    ·
      exact lt_of_lt_of_leₓ (hN _ h) (le_add_of_nonneg_left R.2)
    ·
      have  : _ ≤ R := Finset.le_sup (Finset.mem_range.2 h)
      exact lt_of_le_of_ltₓ this (lt_add_of_pos_right _ zero_lt_one)

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem cauchy_seq_iff_le_tendsto_0 {s : ℕ → α} :
  CauchySeq s ↔
    ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ (∀ n m N : ℕ, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) ∧ tendsto b at_top (𝓝 0) :=
  ⟨fun hs =>
      by 
        let S := fun N => (fun p : ℕ × ℕ => dist (s p.1) (s p.2)) '' { p | p.1 ≥ N ∧ p.2 ≥ N }
        have hS : ∀ N, ∃ x, ∀ y _ : y ∈ S N, y ≤ x
        ·
          rcases cauchy_seq_bdd hs with ⟨R, R0, hR⟩
          refine' fun N => ⟨R, _⟩
          rintro _ ⟨⟨m, n⟩, _, rfl⟩
          exact le_of_ltₓ (hR m n)
        have bdd : BddAbove (range fun p : ℕ × ℕ => dist (s p.1) (s p.2))
        ·
          rcases cauchy_seq_bdd hs with ⟨R, R0, hR⟩
          use R 
          rintro _ ⟨⟨m, n⟩, rfl⟩
          exact le_of_ltₓ (hR m n)
        have ub : ∀ m n N, N ≤ m → N ≤ n → dist (s m) (s n) ≤ Sup (S N) :=
          fun m n N hm hn => le_cSup (hS N) ⟨⟨_, _⟩, ⟨hm, hn⟩, rfl⟩
        have S0m : ∀ n, (0 : ℝ) ∈ S n := fun n => ⟨⟨n, n⟩, ⟨le_reflₓ _, le_reflₓ _⟩, dist_self _⟩
        have S0 := fun n => le_cSup (hS n) (S0m n)
        refine' ⟨fun N => Sup (S N), S0, ub, Metric.tendsto_at_top.2 fun ε ε0 => _⟩
        refine' (Metric.cauchy_seq_iff.1 hs (ε / 2) (half_pos ε0)).imp fun N hN n hn => _ 
        rw [Real.dist_0_eq_abs, abs_of_nonneg (S0 n)]
        refine' lt_of_le_of_ltₓ (cSup_le ⟨_, S0m _⟩ _) (half_lt_self ε0)
        rintro _ ⟨⟨m', n'⟩, ⟨hm', hn'⟩, rfl⟩
        exact le_of_ltₓ (hN _ _ (le_transₓ hn hm') (le_transₓ hn hn')),
    fun ⟨b, _, b_bound, b_lim⟩ => cauchy_seq_of_le_tendsto_0 b b_bound b_lim⟩

end CauchySeq

/-- Pseudometric space structure pulled back by a function. -/
def PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) : PseudoMetricSpace α :=
  { dist := fun x y => dist (f x) (f y), dist_self := fun x => dist_self _, dist_comm := fun x y => dist_comm _ _,
    dist_triangle := fun x y z => dist_triangle _ _ _, edist := fun x y => edist (f x) (f y),
    edist_dist := fun x y => edist_dist _ _, toUniformSpace := UniformSpace.comap f m.to_uniform_space,
    uniformity_dist :=
      by 
        apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ fun x y => dist (f x) (f y)
        refine' fun s => mem_comap.trans _ 
        split  <;> intro H
        ·
          rcases H with ⟨r, ru, rs⟩
          rcases mem_uniformity_dist.1 ru with ⟨ε, ε0, hε⟩
          refine' ⟨ε, ε0, fun a b h => rs (hε _)⟩
          exact h
        ·
          rcases H with ⟨ε, ε0, hε⟩
          exact ⟨_, dist_mem_uniformity ε0, fun ⟨a, b⟩ => hε⟩ }

/-- Pull back a pseudometric space structure by a uniform inducing map. This is a version of
`pseudo_metric_space.induced` useful in case if the domain already has a `uniform_space`
structure. -/
def UniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [PseudoMetricSpace β] (f : α → β)
  (h : UniformInducing f) : PseudoMetricSpace α :=
  (PseudoMetricSpace.induced f ‹_›).replaceUniformity h.comap_uniformity.symm

instance Subtype.psudoMetricSpace {α : Type _} {p : α → Prop} [t : PseudoMetricSpace α] :
  PseudoMetricSpace (Subtype p) :=
  PseudoMetricSpace.induced coeₓ t

theorem Subtype.pseudo_dist_eq {p : α → Prop} (x y : Subtype p) : dist x y = dist (x : α) y :=
  rfl

section Nnreal

noncomputable instance  : PseudoMetricSpace ℝ≥0  :=
  by 
    unfold Nnreal <;> infer_instance

theorem Nnreal.dist_eq (a b :  ℝ≥0 ) : dist a b = |(a : ℝ) - b| :=
  rfl

theorem Nnreal.nndist_eq (a b :  ℝ≥0 ) : nndist a b = max (a - b) (b - a) :=
  by 
    wlog h : a ≤ b
    ·
      apply Nnreal.coe_eq.1
      rw [tsub_eq_zero_iff_le.2 h, max_eq_rightₓ (zero_le$ b - a), ←dist_nndist, Nnreal.dist_eq, Nnreal.coe_sub h,
        abs_eq_max_neg, neg_sub]
      apply max_eq_rightₓ 
      linarith [Nnreal.coe_le_coe.2 h]
    rwa [nndist_comm, max_commₓ]

end Nnreal

section Prod

noncomputable instance Prod.pseudoMetricSpaceMax [PseudoMetricSpace β] : PseudoMetricSpace (α × β) :=
  { dist := fun x y => max (dist x.1 y.1) (dist x.2 y.2),
    dist_self :=
      fun x =>
        by 
          simp ,
    dist_comm :=
      fun x y =>
        by 
          simp [dist_comm],
    dist_triangle :=
      fun x y z =>
        max_leₓ (le_transₓ (dist_triangle _ _ _) (add_le_add (le_max_leftₓ _ _) (le_max_leftₓ _ _)))
          (le_transₓ (dist_triangle _ _ _) (add_le_add (le_max_rightₓ _ _) (le_max_rightₓ _ _))),
    edist := fun x y => max (edist x.1 y.1) (edist x.2 y.2),
    edist_dist :=
      fun x y =>
        by 
          have  : Monotone Ennreal.ofReal := fun x y h => Ennreal.of_real_le_of_real h 
          rw [edist_dist, edist_dist, ←this.map_max],
    uniformity_dist :=
      by 
        refine' uniformity_prod.trans _ 
        simp only [uniformity_basis_dist.eq_binfi, comap_infi]
        rw [←infi_inf_eq]
        congr 
        funext 
        rw [←infi_inf_eq]
        congr 
        funext 
        simp [inf_principal, ext_iff, max_lt_iff],
    toUniformSpace := Prod.uniformSpace }

theorem Prod.dist_eq [PseudoMetricSpace β] {x y : α × β} : dist x y = max (dist x.1 y.1) (dist x.2 y.2) :=
  rfl

theorem ball_prod_same [PseudoMetricSpace β] (x : α) (y : β) (r : ℝ) : (ball x r).Prod (ball y r) = ball (x, y) r :=
  ext$
    fun z =>
      by 
        simp [Prod.dist_eq]

theorem closed_ball_prod_same [PseudoMetricSpace β] (x : α) (y : β) (r : ℝ) :
  (closed_ball x r).Prod (closed_ball y r) = closed_ball (x, y) r :=
  ext$
    fun z =>
      by 
        simp [Prod.dist_eq]

end Prod

theorem uniform_continuous_dist : UniformContinuous fun p : α × α => dist p.1 p.2 :=
  Metric.uniform_continuous_iff.2
    fun ε ε0 =>
      ⟨ε / 2, half_pos ε0,
        by 
          suffices 
          ·
            intro p q h 
            cases' p with p₁ p₂ 
            cases' q with q₁ q₂ 
            cases' max_lt_iff.1 h with h₁ h₂ 
            clear h 
            dsimp  at h₁ h₂⊢
            rw [Real.dist_eq]
            refine' abs_sub_lt_iff.2 ⟨_, _⟩
            ·
              revert p₁ p₂ q₁ q₂ h₁ h₂ 
              exact this
            ·
              apply this <;> rwa [dist_comm]
          intro p₁ p₂ q₁ q₂ h₁ h₂ 
          have  :=
            add_lt_add (abs_sub_lt_iff.1 (lt_of_le_of_ltₓ (abs_dist_sub_le p₁ q₁ p₂) h₁)).1
              (abs_sub_lt_iff.1 (lt_of_le_of_ltₓ (abs_dist_sub_le p₂ q₂ q₁) h₂)).1
          rwa [add_halves, dist_comm p₂, sub_add_sub_cancel, dist_comm q₂] at this⟩

theorem UniformContinuous.dist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f) (hg : UniformContinuous g) :
  UniformContinuous fun b => dist (f b) (g b) :=
  uniform_continuous_dist.comp (hf.prod_mk hg)

@[continuity]
theorem continuous_dist : Continuous fun p : α × α => dist p.1 p.2 :=
  uniform_continuous_dist.Continuous

@[continuity]
theorem Continuous.dist [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
  Continuous fun b => dist (f b) (g b) :=
  continuous_dist.comp (hf.prod_mk hg : _)

theorem Filter.Tendsto.dist {f g : β → α} {x : Filter β} {a b : α} (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (fun x => dist (f x) (g x)) x (𝓝 (dist a b)) :=
  (continuous_dist.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)

theorem nhds_comap_dist (a : α) : ((𝓝 (0 : ℝ)).comap fun a' => dist a' a) = 𝓝 a :=
  by 
    simp only [@nhds_eq_comap_uniformity α, Metric.uniformity_eq_comap_nhds_zero, comap_comap, · ∘ ·, dist_comm]

theorem tendsto_iff_dist_tendsto_zero {f : β → α} {x : Filter β} {a : α} :
  tendsto f x (𝓝 a) ↔ tendsto (fun b => dist (f b) a) x (𝓝 0) :=
  by 
    rw [←nhds_comap_dist a, tendsto_comap_iff]

theorem uniform_continuous_nndist : UniformContinuous fun p : α × α => nndist p.1 p.2 :=
  uniform_continuous_subtype_mk uniform_continuous_dist _

theorem UniformContinuous.nndist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f) (hg : UniformContinuous g) :
  UniformContinuous fun b => nndist (f b) (g b) :=
  uniform_continuous_nndist.comp (hf.prod_mk hg)

theorem continuous_nndist : Continuous fun p : α × α => nndist p.1 p.2 :=
  uniform_continuous_nndist.Continuous

theorem Continuous.nndist [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
  Continuous fun b => nndist (f b) (g b) :=
  continuous_nndist.comp (hf.prod_mk hg : _)

theorem Filter.Tendsto.nndist {f g : β → α} {x : Filter β} {a b : α} (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (fun x => nndist (f x) (g x)) x (𝓝 (nndist a b)) :=
  (continuous_nndist.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)

namespace Metric

variable{x y z : α}{ε ε₁ ε₂ : ℝ}{s : Set α}

theorem is_closed_ball : IsClosed (closed_ball x ε) :=
  is_closed_le (continuous_id.dist continuous_const) continuous_const

theorem is_closed_sphere : IsClosed (sphere x ε) :=
  is_closed_eq (continuous_id.dist continuous_const) continuous_const

@[simp]
theorem closure_closed_ball : Closure (closed_ball x ε) = closed_ball x ε :=
  is_closed_ball.closure_eq

theorem closure_ball_subset_closed_ball : Closure (ball x ε) ⊆ closed_ball x ε :=
  closure_minimal ball_subset_closed_ball is_closed_ball

theorem frontier_ball_subset_sphere : Frontier (ball x ε) ⊆ sphere x ε :=
  frontier_lt_subset_eq (continuous_id.dist continuous_const) continuous_const

theorem frontier_closed_ball_subset_sphere : Frontier (closed_ball x ε) ⊆ sphere x ε :=
  frontier_le_subset_eq (continuous_id.dist continuous_const) continuous_const

theorem ball_subset_interior_closed_ball : ball x ε ⊆ Interior (closed_ball x ε) :=
  interior_maximal ball_subset_closed_ball is_open_ball

/-- ε-characterization of the closure in pseudometric spaces-/
theorem mem_closure_iff {α : Type u} [PseudoMetricSpace α] {s : Set α} {a : α} :
  a ∈ Closure s ↔ ∀ ε _ : ε > 0, ∃ (b : _)(_ : b ∈ s), dist a b < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_ball).trans$
    by 
      simp only [mem_ball, dist_comm]

theorem mem_closure_range_iff {α : Type u} [PseudoMetricSpace α] {e : β → α} {a : α} :
  a ∈ Closure (range e) ↔ ∀ ε _ : ε > 0, ∃ k : β, dist a (e k) < ε :=
  by 
    simp only [mem_closure_iff, exists_range_iff]

theorem mem_closure_range_iff_nat {α : Type u} [PseudoMetricSpace α] {e : β → α} {a : α} :
  a ∈ Closure (range e) ↔ ∀ n : ℕ, ∃ k : β, dist a (e k) < 1 / (n : ℝ)+1 :=
  (mem_closure_iff_nhds_basis nhds_basis_ball_inv_nat_succ).trans$
    by 
      simp only [mem_ball, dist_comm, exists_range_iff, forall_const]

theorem mem_of_closed' {α : Type u} [PseudoMetricSpace α] {s : Set α} (hs : IsClosed s) {a : α} :
  a ∈ s ↔ ∀ ε _ : ε > 0, ∃ (b : _)(_ : b ∈ s), dist a b < ε :=
  by 
    simpa only [hs.closure_eq] using @mem_closure_iff _ _ s a

end Metric

section Pi

open Finset

variable{π : β → Type _}[Fintype β][∀ b, PseudoMetricSpace (π b)]

/-- A finite product of pseudometric spaces is a pseudometric space, with the sup distance. -/
noncomputable instance pseudoMetricSpacePi : PseudoMetricSpace (∀ b, π b) :=
  by 
    refine'
      PseudoEmetricSpace.toPseudoMetricSpaceOfDist (fun f g => ((sup univ fun b => nndist (f b) (g b) :  ℝ≥0 ) : ℝ)) _
        _ 
    show ∀ x y : ∀ b : β, π b, edist x y ≠ ⊤
    ·
      intro x y 
      rw [←lt_top_iff_ne_top]
      have  : (⊥ : ℝ≥0∞) < ⊤ := Ennreal.coe_lt_top 
      simp [edist_pi_def, Finset.sup_lt_iff this, edist_lt_top]
    show
      ∀ x y : ∀ b : β, π b,
        «expr↑ » (sup univ fun b : β => nndist (x b) (y b)) = Ennreal.toReal (sup univ fun b : β => edist (x b) (y b))
    ·
      intro x y 
      simp only [edist_nndist]
      normCast

theorem nndist_pi_def (f g : ∀ b, π b) : nndist f g = sup univ fun b => nndist (f b) (g b) :=
  Subtype.eta _ _

theorem dist_pi_def (f g : ∀ b, π b) : dist f g = (sup univ fun b => nndist (f b) (g b) :  ℝ≥0 ) :=
  rfl

@[simp]
theorem dist_pi_const [Nonempty β] (a b : α) : (dist (fun x : β => a) fun _ => b) = dist a b :=
  by 
    simpa only [dist_edist] using congr_argₓ Ennreal.toReal (edist_pi_const a b)

@[simp]
theorem nndist_pi_const [Nonempty β] (a b : α) : (nndist (fun x : β => a) fun _ => b) = nndist a b :=
  Nnreal.eq$ dist_pi_const a b

theorem dist_pi_lt_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 < r) : dist f g < r ↔ ∀ b, dist (f b) (g b) < r :=
  by 
    lift r to  ℝ≥0  using hr.le 
    simp [dist_pi_def, Finset.sup_lt_iff (show ⊥ < r from hr)]

theorem dist_pi_le_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 ≤ r) : dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r :=
  by 
    lift r to  ℝ≥0  using hr 
    simp [nndist_pi_def]

theorem nndist_le_pi_nndist (f g : ∀ b, π b) (b : β) : nndist (f b) (g b) ≤ nndist f g :=
  by 
    rw [nndist_pi_def]
    exact Finset.le_sup (Finset.mem_univ b)

theorem dist_le_pi_dist (f g : ∀ b, π b) (b : β) : dist (f b) (g b) ≤ dist f g :=
  by 
    simp only [dist_nndist, Nnreal.coe_le_coe, nndist_le_pi_nndist f g b]

/-- An open ball in a product space is a product of open balls. See also `metric.ball_pi'`
for a version assuming `nonempty β` instead of `0 < r`. -/
theorem ball_pi (x : ∀ b, π b) {r : ℝ} (hr : 0 < r) : ball x r = Set.Pi univ fun b => ball (x b) r :=
  by 
    ext p 
    simp [dist_pi_lt_iff hr]

/-- An open ball in a product space is a product of open balls. See also `metric.ball_pi`
for a version assuming `0 < r` instead of `nonempty β`. -/
theorem ball_pi' [Nonempty β] (x : ∀ b, π b) (r : ℝ) : ball x r = Set.Pi univ fun b => ball (x b) r :=
  (lt_or_leₓ 0 r).elim (ball_pi x)$
    fun hr =>
      by 
        simp [ball_eq_empty.2 hr]

/-- A closed ball in a product space is a product of closed balls. See also `metric.closed_ball_pi'`
for a version assuming `nonempty β` instead of `0 ≤ r`. -/
theorem closed_ball_pi (x : ∀ b, π b) {r : ℝ} (hr : 0 ≤ r) :
  closed_ball x r = Set.Pi univ fun b => closed_ball (x b) r :=
  by 
    ext p 
    simp [dist_pi_le_iff hr]

/-- A closed ball in a product space is a product of closed balls. See also `metric.closed_ball_pi`
for a version assuming `0 ≤ r` instead of `nonempty β`. -/
theorem closed_ball_pi' [Nonempty β] (x : ∀ b, π b) (r : ℝ) :
  closed_ball x r = Set.Pi univ fun b => closed_ball (x b) r :=
  (le_or_ltₓ 0 r).elim (closed_ball_pi x)$
    fun hr =>
      by 
        simp [closed_ball_eq_empty.2 hr]

-- error in Topology.MetricSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem real.dist_le_of_mem_pi_Icc
{x y x' y' : β → exprℝ()}
(hx : «expr ∈ »(x, Icc x' y'))
(hy : «expr ∈ »(y, Icc x' y')) : «expr ≤ »(dist x y, dist x' y') :=
begin
  refine [expr (dist_pi_le_iff dist_nonneg).2 (λ
    b, (real.dist_le_of_mem_interval _ _).trans (dist_le_pi_dist _ _ b))]; refine [expr Icc_subset_interval _],
  exacts ["[", expr ⟨hx.1 _, hx.2 _⟩, ",", expr ⟨hy.1 _, hy.2 _⟩, "]"]
end

end Pi

section Compact

/-- Any compact set in a pseudometric space can be covered by finitely many balls of a given
positive radius -/
theorem finite_cover_balls_of_compact {α : Type u} [PseudoMetricSpace α] {s : Set α} (hs : IsCompact s) {e : ℝ}
  (he : 0 < e) : ∃ (t : _)(_ : t ⊆ s), finite t ∧ s ⊆ ⋃(x : _)(_ : x ∈ t), ball x e :=
  by 
    apply hs.elim_finite_subcover_image
    ·
      simp [is_open_ball]
    ·
      intro x xs 
      simp 
      exact
        ⟨x,
          ⟨xs,
            by 
              simpa⟩⟩

alias finite_cover_balls_of_compact ← IsCompact.finite_cover_balls

end Compact

section ProperSpace

open Metric

/-- A pseudometric space is proper if all closed balls are compact. -/
class ProperSpace(α : Type u)[PseudoMetricSpace α] : Prop where 
  is_compact_closed_ball : ∀ x : α, ∀ r, IsCompact (closed_ball x r)

/-- In a proper pseudometric space, all spheres are compact. -/
theorem is_compact_sphere {α : Type _} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) : IsCompact (sphere x r) :=
  compact_of_is_closed_subset (ProperSpace.is_compact_closed_ball x r) is_closed_sphere sphere_subset_closed_ball

/-- In a proper pseudometric space, any sphere is a `compact_space` when considered as a subtype. -/
instance  {α : Type _} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) : CompactSpace (sphere x r) :=
  is_compact_iff_compact_space.mp (is_compact_sphere _ _)

/-- A proper pseudo metric space is sigma compact, and therefore second countable. -/
instance (priority := 100)second_countable_of_proper [ProperSpace α] : second_countable_topology α :=
  by 
    suffices  : SigmaCompactSpace α
    ·
      exactI Emetric.second_countable_of_sigma_compact α 
    rcases em (Nonempty α) with (⟨⟨x⟩⟩ | hn)
    ·
      exact ⟨⟨fun n => closed_ball x n, fun n => ProperSpace.is_compact_closed_ball _ _, Union_closed_ball_nat _⟩⟩
    ·
      exact ⟨⟨fun n => ∅, fun n => is_compact_empty, Union_eq_univ_iff.2$ fun x => (hn ⟨x⟩).elim⟩⟩

theorem tendsto_dist_right_cocompact_at_top [ProperSpace α] (x : α) :
  tendsto (fun y => dist y x) (cocompact α) at_top :=
  (has_basis_cocompact.tendsto_iff at_top_basis).2$
    fun r hr =>
      ⟨closed_ball x r, ProperSpace.is_compact_closed_ball x r, fun y hy => (not_leₓ.1$ mt mem_closed_ball.2 hy).le⟩

theorem tendsto_dist_left_cocompact_at_top [ProperSpace α] (x : α) : tendsto (dist x) (cocompact α) at_top :=
  by 
    simpa only [dist_comm] using tendsto_dist_right_cocompact_at_top x

/-- If all closed balls of large enough radius are compact, then the space is proper. Especially
useful when the lower bound for the radius is 0. -/
theorem proper_space_of_compact_closed_ball_of_le (R : ℝ) (h : ∀ x : α, ∀ r, R ≤ r → IsCompact (closed_ball x r)) :
  ProperSpace α :=
  ⟨by 
      intro x r 
      byCases' hr : R ≤ r
      ·
        exact h x r hr
      ·
        have  : closed_ball x r = closed_ball x R ∩ closed_ball x r
        ·
          symm 
          apply inter_eq_self_of_subset_right 
          exact closed_ball_subset_closed_ball (le_of_ltₓ (not_leₓ.1 hr))
        rw [this]
        exact (h x R (le_reflₓ _)).inter_right is_closed_ball⟩

instance (priority := 100)proper_of_compact [CompactSpace α] : ProperSpace α :=
  ⟨fun x r => is_closed_ball.IsCompact⟩

/-- A proper space is locally compact -/
instance (priority := 100)locally_compact_of_proper [ProperSpace α] : LocallyCompactSpace α :=
  (locally_compact_space_of_has_basis fun x => nhds_basis_closed_ball)$
    fun x ε ε0 => ProperSpace.is_compact_closed_ball _ _

/-- A proper space is complete -/
instance (priority := 100)complete_of_proper [ProperSpace α] : CompleteSpace α :=
  ⟨by 
      intro f hf 
      obtain ⟨t, t_fset, ht⟩ : ∃ (t : _)(_ : t ∈ f), ∀ x y _ : x ∈ t _ : y ∈ t, dist x y < 1 :=
        (Metric.cauchy_iff.1 hf).2 1 zero_lt_one 
      rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩
      have  : closed_ball x 1 ∈ f := mem_of_superset t_fset fun y yt => (ht y x yt xt).le 
      rcases(compact_iff_totally_bounded_complete.1 (ProperSpace.is_compact_closed_ball x 1)).2 f hf
          (le_principal_iff.2 this) with
        ⟨y, -, hy⟩
      exact ⟨y, hy⟩⟩

/-- A finite product of proper spaces is proper. -/
instance pi_proper_space {π : β → Type _} [Fintype β] [∀ b, PseudoMetricSpace (π b)] [h : ∀ b, ProperSpace (π b)] :
  ProperSpace (∀ b, π b) :=
  by 
    refine' proper_space_of_compact_closed_ball_of_le 0 fun x r hr => _ 
    rw [closed_ball_pi _ hr]
    apply is_compact_univ_pi fun b => _ 
    apply (h b).is_compact_closed_ball

variable[ProperSpace α]{x : α}{r : ℝ}{s : Set α}

/-- If a nonempty ball in a proper space includes a closed set `s`, then there exists a nonempty
ball with the same center and a strictly smaller radius that includes `s`. -/
theorem exists_pos_lt_subset_ball (hr : 0 < r) (hs : IsClosed s) (h : s ⊆ ball x r) :
  ∃ (r' : _)(_ : r' ∈ Ioo 0 r), s ⊆ ball x r' :=
  by 
    unfreezingI 
      rcases eq_empty_or_nonempty s with (rfl | hne)
    ·
      exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩
    have  : IsCompact s 
    exact
      compact_of_is_closed_subset (ProperSpace.is_compact_closed_ball x r) hs (subset.trans h ball_subset_closed_ball)
    obtain ⟨y, hys, hy⟩ : ∃ (y : _)(_ : y ∈ s), s ⊆ closed_ball x (dist y x)
    exact this.exists_forall_ge hne (continuous_id.dist continuous_const).ContinuousOn 
    have hyr : dist y x < r 
    exact h hys 
    rcases exists_between hyr with ⟨r', hyr', hrr'⟩
    exact ⟨r', ⟨dist_nonneg.trans_lt hyr', hrr'⟩, subset.trans hy$ closed_ball_subset_ball hyr'⟩

/-- If a ball in a proper space includes a closed set `s`, then there exists a ball with the same
center and a strictly smaller radius that includes `s`. -/
theorem exists_lt_subset_ball (hs : IsClosed s) (h : s ⊆ ball x r) : ∃ (r' : _)(_ : r' < r), s ⊆ ball x r' :=
  by 
    cases' le_or_ltₓ r 0 with hr hr
    ·
      rw [ball_eq_empty.2 hr, subset_empty_iff] at h 
      unfreezingI 
        subst s 
      exact (no_bot r).imp fun r' hr' => ⟨hr', empty_subset _⟩
    ·
      exact (exists_pos_lt_subset_ball hr hs h).imp fun r' hr' => ⟨hr'.fst.2, hr'.snd⟩

end ProperSpace

namespace Metric

section SecondCountable

open TopologicalSpace

/-- A pseudometric space is second countable if, for every `ε > 0`, there is a countable set which
is `ε`-dense. -/
theorem second_countable_of_almost_dense_set
  (H : ∀ ε _ : ε > (0 : ℝ), ∃ s : Set α, countable s ∧ ∀ x, ∃ (y : _)(_ : y ∈ s), dist x y ≤ ε) :
  second_countable_topology α :=
  by 
    refine' Emetric.second_countable_of_almost_dense_set fun ε ε0 => _ 
    rcases Ennreal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩
    choose s hsc y hys hyx using
      H ε'
        (by 
          exactModCast ε'0)
    refine' ⟨s, hsc, bUnion_eq_univ_iff.2 fun x => ⟨y x, hys _, le_transₓ _ ε'ε.le⟩⟩
    exactModCast hyx x

end SecondCountable

end Metric

theorem lebesgue_number_lemma_of_metric {s : Set α} {ι} {c : ι → Set α} (hs : IsCompact s) (hc₁ : ∀ i, IsOpen (c i))
  (hc₂ : s ⊆ ⋃i, c i) : ∃ (δ : _)(_ : δ > 0), ∀ x _ : x ∈ s, ∃ i, ball x δ ⊆ c i :=
  let ⟨n, en, hn⟩ := lebesgue_number_lemma hs hc₁ hc₂ 
  let ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 en
  ⟨δ, δ0,
    fun x hx =>
      let ⟨i, hi⟩ := hn x hx
      ⟨i, fun y hy => hi (hδ (mem_ball'.mp hy))⟩⟩

theorem lebesgue_number_lemma_of_metric_sUnion {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
  (hc₁ : ∀ t _ : t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀c) :
  ∃ (δ : _)(_ : δ > 0), ∀ x _ : x ∈ s, ∃ (t : _)(_ : t ∈ c), ball x δ ⊆ t :=
  by 
    rw [sUnion_eq_Union] at hc₂ <;>
      simpa using
        lebesgue_number_lemma_of_metric hs
          (by 
            simpa)
          hc₂

namespace Metric

/-- Boundedness of a subset of a pseudometric space. We formulate the definition to work
even in the empty space. -/
def Bounded (s : Set α) : Prop :=
  ∃ C, ∀ x y _ : x ∈ s _ : y ∈ s, dist x y ≤ C

section Bounded

variable{x : α}{s t : Set α}{r : ℝ}

@[simp]
theorem bounded_empty : Bounded (∅ : Set α) :=
  ⟨0,
    by 
      simp ⟩

theorem bounded_iff_mem_bounded : Bounded s ↔ ∀ x _ : x ∈ s, Bounded s :=
  ⟨fun h _ _ => h, fun H => s.eq_empty_or_nonempty.elim (fun hs => hs.symm ▸ bounded_empty) fun ⟨x, hx⟩ => H x hx⟩

/-- Subsets of a bounded set are also bounded -/
theorem bounded.mono (incl : s ⊆ t) : Bounded t → Bounded s :=
  Exists.impₓ$ fun C hC x y hx hy => hC x y (incl hx) (incl hy)

/-- Closed balls are bounded -/
theorem bounded_closed_ball : Bounded (closed_ball x r) :=
  ⟨r+r,
    fun y z hy hz =>
      by 
        simp only [mem_closed_ball] at *
        calc dist y z ≤ dist y x+dist z x := dist_triangle_right _ _ _ _ ≤ r+r := add_le_add hy hz⟩

/-- Open balls are bounded -/
theorem bounded_ball : Bounded (ball x r) :=
  bounded_closed_ball.mono ball_subset_closed_ball

/-- Given a point, a bounded subset is included in some ball around this point -/
theorem bounded_iff_subset_ball (c : α) : Bounded s ↔ ∃ r, s ⊆ closed_ball c r :=
  by 
    split  <;> rintro ⟨C, hC⟩
    ·
      cases' s.eq_empty_or_nonempty with h h
      ·
        subst s 
        exact
          ⟨0,
            by 
              simp ⟩
      ·
        rcases h with ⟨x, hx⟩
        exact
          ⟨C+dist x c,
            fun y hy =>
              calc dist y c ≤ dist y x+dist x c := dist_triangle _ _ _ 
                _ ≤ C+dist x c := add_le_add_right (hC y x hy hx) _
                ⟩
    ·
      exact bounded_closed_ball.mono hC

theorem bounded.subset_ball (h : Bounded s) (c : α) : ∃ r, s ⊆ closed_ball c r :=
  (bounded_iff_subset_ball c).1 h

theorem bounded_closure_of_bounded (h : Bounded s) : Bounded (Closure s) :=
  let ⟨C, h⟩ := h
  ⟨C, fun a b ha hb => (is_closed_le' C).closure_subset$ map_mem_closure2 continuous_dist ha hb h⟩

alias bounded_closure_of_bounded ← Metric.Bounded.closure

@[simp]
theorem bounded_closure_iff : Bounded (Closure s) ↔ Bounded s :=
  ⟨fun h => h.mono subset_closure, fun h => h.closure⟩

/-- The union of two bounded sets is bounded iff each of the sets is bounded -/
@[simp]
theorem bounded_union : Bounded (s ∪ t) ↔ Bounded s ∧ Bounded t :=
  ⟨fun h =>
      ⟨h.mono
          (by 
            simp ),
        h.mono
          (by 
            simp )⟩,
    by 
      rintro ⟨hs, ht⟩
      refine' bounded_iff_mem_bounded.2 fun x _ => _ 
      rw [bounded_iff_subset_ball x] at hs ht⊢
      rcases hs with ⟨Cs, hCs⟩
      rcases ht with ⟨Ct, hCt⟩
      exact
        ⟨max Cs Ct,
          union_subset (subset.trans hCs$ closed_ball_subset_closed_ball$ le_max_leftₓ _ _)
            (subset.trans hCt$ closed_ball_subset_closed_ball$ le_max_rightₓ _ _)⟩⟩

/-- A finite union of bounded sets is bounded -/
theorem bounded_bUnion {I : Set β} {s : β → Set α} (H : finite I) :
  Bounded (⋃(i : _)(_ : i ∈ I), s i) ↔ ∀ i _ : i ∈ I, Bounded (s i) :=
  finite.induction_on H
      (by 
        simp )$
    fun x I _ _ IH =>
      by 
        simp [or_imp_distrib, forall_and_distrib, IH]

/-- A totally bounded set is bounded -/
theorem _root_.totally_bounded.bounded {s : Set α} (h : TotallyBounded s) : Bounded s :=
  let ⟨t, fint, subs⟩ := (totally_bounded_iff.mp h) 1 zero_lt_one 
  bounded.mono subs$ (bounded_bUnion fint).2$ fun i hi => bounded_ball

/-- A compact set is bounded -/
theorem _root_.is_compact.bounded {s : Set α} (h : IsCompact s) : Bounded s :=
  h.totally_bounded.bounded

/-- A finite set is bounded -/
theorem bounded_of_finite {s : Set α} (h : finite s) : Bounded s :=
  h.is_compact.bounded

alias bounded_of_finite ← Set.Finite.bounded

/-- A singleton is bounded -/
theorem bounded_singleton {x : α} : Bounded ({x} : Set α) :=
  bounded_of_finite$ finite_singleton _

/-- Characterization of the boundedness of the range of a function -/
theorem bounded_range_iff {f : β → α} : Bounded (range f) ↔ ∃ C, ∀ x y, dist (f x) (f y) ≤ C :=
  exists_congr$
    fun C =>
      ⟨fun H x y => H _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
        by 
          rintro H _ _ ⟨x, rfl⟩ ⟨y, rfl⟩ <;> exact H x y⟩

/-- In a compact space, all sets are bounded -/
theorem bounded_of_compact_space [CompactSpace α] : Bounded s :=
  compact_univ.Bounded.mono (subset_univ _)

theorem is_compact_of_is_closed_bounded [ProperSpace α] (hc : IsClosed s) (hb : Bounded s) : IsCompact s :=
  by 
    unfreezingI 
      rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    ·
      exact is_compact_empty
    ·
      rcases hb.subset_ball x with ⟨r, hr⟩
      exact compact_of_is_closed_subset (ProperSpace.is_compact_closed_ball x r) hc hr

/-- The Heine–Borel theorem:
In a proper space, a set is compact if and only if it is closed and bounded -/
theorem compact_iff_closed_bounded [T2Space α] [ProperSpace α] : IsCompact s ↔ IsClosed s ∧ Bounded s :=
  ⟨fun h => ⟨h.is_closed, h.bounded⟩, fun h => is_compact_of_is_closed_bounded h.1 h.2⟩

theorem compact_space_iff_bounded_univ [ProperSpace α] : CompactSpace α ↔ Bounded (univ : Set α) :=
  ⟨@bounded_of_compact_space α _ _, fun hb => ⟨is_compact_of_is_closed_bounded is_closed_univ hb⟩⟩

section ConditionallyCompleteLinearOrder

variable[ConditionallyCompleteLinearOrder α][OrderTopology α]

theorem bounded_Icc (a b : α) : Bounded (Icc a b) :=
  (totally_bounded_Icc a b).Bounded

theorem bounded_Ico (a b : α) : Bounded (Ico a b) :=
  (totally_bounded_Ico a b).Bounded

theorem bounded_Ioc (a b : α) : Bounded (Ioc a b) :=
  (totally_bounded_Ioc a b).Bounded

theorem bounded_Ioo (a b : α) : Bounded (Ioo a b) :=
  (totally_bounded_Ioo a b).Bounded

/-- In a pseudo metric space with a conditionally complete linear order such that the order and the
    metric structure give the same topology, any order-bounded set is metric-bounded. -/
theorem bounded_of_bdd_above_of_bdd_below {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s) : Bounded s :=
  let ⟨u, hu⟩ := h₁ 
  let ⟨l, hl⟩ := h₂ 
  bounded.mono (fun x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩) (bounded_Icc l u)

end ConditionallyCompleteLinearOrder

end Bounded

section Diam

variable{s : Set α}{x y z : α}

/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the emetric.diameter -/
noncomputable def diam (s : Set α) : ℝ :=
  Ennreal.toReal (Emetric.diam s)

/-- The diameter of a set is always nonnegative -/
theorem diam_nonneg : 0 ≤ diam s :=
  Ennreal.to_real_nonneg

theorem diam_subsingleton (hs : s.subsingleton) : diam s = 0 :=
  by 
    simp only [diam, Emetric.diam_subsingleton hs, Ennreal.zero_to_real]

/-- The empty set has zero diameter -/
@[simp]
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty

/-- A singleton has zero diameter -/
@[simp]
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton

theorem diam_pair : diam ({x, y} : Set α) = dist x y :=
  by 
    simp only [diam, Emetric.diam_pair, dist_edist]

theorem diam_triple : Metric.diam ({x, y, z} : Set α) = max (max (dist x y) (dist x z)) (dist y z) :=
  by 
    simp only [Metric.diam, Emetric.diam_triple, dist_edist]
    rw [Ennreal.to_real_max, Ennreal.to_real_max] <;> applyRules [ne_of_ltₓ, edist_lt_top, max_ltₓ]

/-- If the distance between any two points in a set is bounded by some constant `C`,
then `ennreal.of_real C`  bounds the emetric diameter of this set. -/
theorem ediam_le_of_forall_dist_le {C : ℝ} (h : ∀ x _ : x ∈ s y _ : y ∈ s, dist x y ≤ C) :
  Emetric.diam s ≤ Ennreal.ofReal C :=
  Emetric.diam_le$ fun x hx y hy => (edist_dist x y).symm ▸ Ennreal.of_real_le_of_real (h x hx y hy)

/-- If the distance between any two points in a set is bounded by some non-negative constant,
this constant bounds the diameter. -/
theorem diam_le_of_forall_dist_le {C : ℝ} (h₀ : 0 ≤ C) (h : ∀ x _ : x ∈ s y _ : y ∈ s, dist x y ≤ C) : diam s ≤ C :=
  Ennreal.to_real_le_of_le_of_real h₀ (ediam_le_of_forall_dist_le h)

/-- If the distance between any two points in a nonempty set is bounded by some constant,
this constant bounds the diameter. -/
theorem diam_le_of_forall_dist_le_of_nonempty (hs : s.nonempty) {C : ℝ} (h : ∀ x _ : x ∈ s y _ : y ∈ s, dist x y ≤ C) :
  diam s ≤ C :=
  have h₀ : 0 ≤ C :=
    let ⟨x, hx⟩ := hs 
    le_transₓ dist_nonneg (h x hx x hx)
  diam_le_of_forall_dist_le h₀ h

/-- The distance between two points in a set is controlled by the diameter of the set. -/
theorem dist_le_diam_of_mem' (h : Emetric.diam s ≠ ⊤) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s :=
  by 
    rw [diam, dist_edist]
    rw [Ennreal.to_real_le_to_real (edist_ne_top _ _) h]
    exact Emetric.edist_le_diam_of_mem hx hy

/-- Characterize the boundedness of a set in terms of the finiteness of its emetric.diameter. -/
theorem bounded_iff_ediam_ne_top : Bounded s ↔ Emetric.diam s ≠ ⊤ :=
  Iff.intro
    (fun ⟨C, hC⟩ =>
      ne_top_of_le_ne_top Ennreal.of_real_ne_top (ediam_le_of_forall_dist_le$ fun x hx y hy => hC x y hx hy))
    fun h => ⟨diam s, fun x y hx hy => dist_le_diam_of_mem' h hx hy⟩

theorem bounded.ediam_ne_top (h : Bounded s) : Emetric.diam s ≠ ⊤ :=
  bounded_iff_ediam_ne_top.1 h

theorem ediam_univ_eq_top_iff_noncompact [ProperSpace α] : Emetric.diam (univ : Set α) = ∞ ↔ NoncompactSpace α :=
  by 
    rw [←not_compact_space_iff, compact_space_iff_bounded_univ, bounded_iff_ediam_ne_top, not_not]

@[simp]
theorem ediam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] : Emetric.diam (univ : Set α) = ∞ :=
  ediam_univ_eq_top_iff_noncompact.mpr ‹_›

@[simp]
theorem diam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] : diam (univ : Set α) = 0 :=
  by 
    simp [diam]

/-- The distance between two points in a set is controlled by the diameter of the set. -/
theorem dist_le_diam_of_mem (h : Bounded s) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s :=
  dist_le_diam_of_mem' h.ediam_ne_top hx hy

theorem ediam_of_unbounded (h : ¬Bounded s) : Emetric.diam s = ∞ :=
  by 
    rwa [bounded_iff_ediam_ne_top, not_not] at h

/-- An unbounded set has zero diameter. If you would prefer to get the value ∞, use `emetric.diam`.
This lemma makes it possible to avoid side conditions in some situations -/
theorem diam_eq_zero_of_unbounded (h : ¬Bounded s) : diam s = 0 :=
  by 
    rw [diam, ediam_of_unbounded h, Ennreal.top_to_real]

/-- If `s ⊆ t`, then the diameter of `s` is bounded by that of `t`, provided `t` is bounded. -/
theorem diam_mono {s t : Set α} (h : s ⊆ t) (ht : Bounded t) : diam s ≤ diam t :=
  by 
    unfold diam 
    rw [Ennreal.to_real_le_to_real (bounded.mono h ht).ediam_ne_top ht.ediam_ne_top]
    exact Emetric.diam_mono h

-- error in Topology.MetricSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- The diameter of a union is controlled by the sum of the diameters, and the distance between
any two points in each of the sets. This lemma is true without any side condition, since it is
obviously true if `s ∪ t` is unbounded. -/
theorem diam_union
{t : set α}
(xs : «expr ∈ »(x, s))
(yt : «expr ∈ »(y, t)) : «expr ≤ »(diam «expr ∪ »(s, t), «expr + »(«expr + »(diam s, dist x y), diam t)) :=
begin
  by_cases [expr H, ":", expr bounded «expr ∪ »(s, t)],
  { have [ident hs] [":", expr bounded s] [],
    from [expr H.mono (subset_union_left _ _)],
    have [ident ht] [":", expr bounded t] [],
    from [expr H.mono (subset_union_right _ _)],
    rw ["[", expr bounded_iff_ediam_ne_top, "]"] ["at", ident H, ident hs, ident ht],
    rw ["[", expr dist_edist, ",", expr diam, ",", expr diam, ",", expr diam, ",", "<-", expr ennreal.to_real_add, ",", "<-", expr ennreal.to_real_add, ",", expr ennreal.to_real_le_to_real, "]"] []; repeat { apply [expr ennreal.add_ne_top.2]; split }; try { assumption }; try { apply [expr edist_ne_top] },
    exact [expr emetric.diam_union xs yt] },
  { rw ["[", expr diam_eq_zero_of_unbounded H, "]"] [],
    apply_rules ["[", expr add_nonneg, ",", expr diam_nonneg, ",", expr dist_nonneg, "]"] }
end

/-- If two sets intersect, the diameter of the union is bounded by the sum of the diameters. -/
theorem diam_union' {t : Set α} (h : (s ∩ t).Nonempty) : diam (s ∪ t) ≤ diam s+diam t :=
  by 
    rcases h with ⟨x, ⟨xs, xt⟩⟩
    simpa using diam_union xs xt

/-- The diameter of a closed ball of radius `r` is at most `2 r`. -/
theorem diam_closed_ball {r : ℝ} (h : 0 ≤ r) : diam (closed_ball x r) ≤ 2*r :=
  diam_le_of_forall_dist_le (mul_nonneg (le_of_ltₓ zero_lt_two) h)$
    fun a ha b hb =>
      calc dist a b ≤ dist a x+dist b x := dist_triangle_right _ _ _ 
        _ ≤ r+r := add_le_add ha hb 
        _ = 2*r :=
        by 
          simp [mul_two, mul_commₓ]
        

/-- The diameter of a ball of radius `r` is at most `2 r`. -/
theorem diam_ball {r : ℝ} (h : 0 ≤ r) : diam (ball x r) ≤ 2*r :=
  le_transₓ (diam_mono ball_subset_closed_ball bounded_closed_ball) (diam_closed_ball h)

end Diam

end Metric

theorem comap_dist_right_at_top_le_cocompact (x : α) : comap (fun y => dist y x) at_top ≤ cocompact α :=
  by 
    refine' filter.has_basis_cocompact.ge_iff.2 fun s hs => mem_comap.2 _ 
    rcases hs.bounded.subset_ball x with ⟨r, hr⟩
    exact ⟨Ioi r, Ioi_mem_at_top r, fun y hy hys => (mem_closed_ball.1$ hr hys).not_lt hy⟩

theorem comap_dist_left_at_top_le_cocompact (x : α) : comap (dist x) at_top ≤ cocompact α :=
  by 
    simpa only [dist_comm _ x] using comap_dist_right_at_top_le_cocompact x

theorem comap_dist_right_at_top_eq_cocompact [ProperSpace α] (x : α) : comap (fun y => dist y x) at_top = cocompact α :=
  (comap_dist_right_at_top_le_cocompact x).antisymm$ (tendsto_dist_right_cocompact_at_top x).le_comap

theorem comap_dist_left_at_top_eq_cocompact [ProperSpace α] (x : α) : comap (dist x) at_top = cocompact α :=
  (comap_dist_left_at_top_le_cocompact x).antisymm$ (tendsto_dist_left_cocompact_at_top x).le_comap

theorem tendsto_cocompact_of_tendsto_dist_comp_at_top {f : β → α} {l : Filter β} (x : α)
  (h : tendsto (fun y => dist (f y) x) l at_top) : tendsto f l (cocompact α) :=
  by 
    refine' tendsto.mono_right _ (comap_dist_right_at_top_le_cocompact x)
    rwa [tendsto_comap_iff]

namespace Int

open Metric

/-- Under the coercion from `ℤ` to `ℝ`, inverse images of compact sets are finite. -/
theorem tendsto_coe_cofinite : tendsto (coeₓ : ℤ → ℝ) cofinite (cocompact ℝ) :=
  by 
    refine' tendsto_cocompact_of_tendsto_dist_comp_at_top (0 : ℝ) _ 
    simp only [Filter.tendsto_at_top, eventually_cofinite, not_leₓ, ←mem_ball]
    change ∀ r : ℝ, finite (coeₓ ⁻¹' ball (0 : ℝ) r)
    simp [Real.ball_eq, Set.finite_Ioo]

end Int

/-- We now define `metric_space`, extending `pseudo_metric_space`. -/
class MetricSpace(α : Type u) extends PseudoMetricSpace α : Type u where 
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y

/-- Construct a metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def MetricSpace.ofMetrizable {α : Type _} [TopologicalSpace α] (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x) (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y+dist y z)
  (H : ∀ s : Set α, IsOpen s ↔ ∀ x _ : x ∈ s, ∃ (ε : _)(_ : ε > 0), ∀ y, dist x y < ε → y ∈ s)
  (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofMetrizable dist dist_self dist_comm dist_triangle H with eq_of_dist_eq_zero }

variable{γ : Type w}[MetricSpace γ]

theorem eq_of_dist_eq_zero {x y : γ} : dist x y = 0 → x = y :=
  MetricSpace.eq_of_dist_eq_zero

@[simp]
theorem dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y :=
  Iff.intro eq_of_dist_eq_zero fun this : x = y => this ▸ dist_self _

@[simp]
theorem zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y :=
  by 
    rw [eq_comm, dist_eq_zero]

theorem dist_ne_zero {x y : γ} : dist x y ≠ 0 ↔ x ≠ y :=
  by 
    simpa only [not_iff_not] using dist_eq_zero

@[simp]
theorem dist_le_zero {x y : γ} : dist x y ≤ 0 ↔ x = y :=
  by 
    simpa [le_antisymm_iffₓ, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp]
theorem dist_pos {x y : γ} : 0 < dist x y ↔ x ≠ y :=
  by 
    simpa only [not_leₓ] using not_congr dist_le_zero

theorem eq_of_forall_dist_le {x y : γ} (h : ∀ ε _ : ε > 0, dist x y ≤ ε) : x = y :=
  eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

/--Deduce the equality of points with the vanishing of the nonnegative distance-/
theorem eq_of_nndist_eq_zero {x y : γ} : nndist x y = 0 → x = y :=
  by 
    simp only [←Nnreal.eq_iff, ←dist_nndist, imp_self, Nnreal.coe_zero, dist_eq_zero]

/--Characterize the equality of points with the vanishing of the nonnegative distance-/
@[simp]
theorem nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y :=
  by 
    simp only [←Nnreal.eq_iff, ←dist_nndist, imp_self, Nnreal.coe_zero, dist_eq_zero]

@[simp]
theorem zero_eq_nndist {x y : γ} : 0 = nndist x y ↔ x = y :=
  by 
    simp only [←Nnreal.eq_iff, ←dist_nndist, imp_self, Nnreal.coe_zero, zero_eq_dist]

namespace Metric

variable{x : γ}{s : Set γ}

@[simp]
theorem closed_ball_zero : closed_ball x 0 = {x} :=
  Set.ext$ fun y => dist_le_zero

/-- A map between metric spaces is a uniform embedding if and only if the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniform_embedding_iff' [MetricSpace β] {f : γ → β} :
  UniformEmbedding f ↔
    (∀ ε _ : ε > 0, ∃ (δ : _)(_ : δ > 0), ∀ {a b : γ}, dist a b < δ → dist (f a) (f b) < ε) ∧
      ∀ δ _ : δ > 0, ∃ (ε : _)(_ : ε > 0), ∀ {a b : γ}, dist (f a) (f b) < ε → dist a b < δ :=
  by 
    split 
    ·
      intro h 
      exact ⟨uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1, (uniform_embedding_iff.1 h).2.2⟩
    ·
      rintro ⟨h₁, h₂⟩
      refine' uniform_embedding_iff.2 ⟨_, uniform_continuous_iff.2 h₁, h₂⟩
      intro x y hxy 
      have  : dist x y ≤ 0
      ·
        refine' le_of_forall_lt' fun δ δpos => _ 
        rcases h₂ δ δpos with ⟨ε, εpos, hε⟩
        have  : dist (f x) (f y) < ε
        ·
          simpa [hxy]
        exact hε this 
      simpa using this

instance (priority := 100)metric_space.to_separated : SeparatedSpace γ :=
  separated_def.2$ fun x y h => eq_of_forall_dist_le$ fun ε ε0 => le_of_ltₓ (h _ (dist_mem_uniformity ε0))

/-- If a  `pseudo_metric_space` is separated, then it is a `metric_space`. -/
def of_t2_pseudo_metric_space {α : Type _} [PseudoMetricSpace α] (h : SeparatedSpace α) : MetricSpace α :=
  { ‹PseudoMetricSpace α› with
    eq_of_dist_eq_zero :=
      fun x y hdist =>
        by 
          refine' separated_def.1 h x y fun s hs => _ 
          obtain ⟨ε, hε, H⟩ := mem_uniformity_dist.1 hs 
          exact
            H
              (show dist x y < ε by 
                rwa [hdist]) }

/-- A metric space induces an emetric space -/
instance (priority := 100)metric_space.to_emetric_space : EmetricSpace γ :=
  { PseudoMetricSpace.toPseudoEmetricSpace with
    eq_of_edist_eq_zero :=
      fun x y h =>
        by 
          simpa [edist_dist] using h }

theorem is_closed_of_pairwise_le_dist {s : Set γ} {ε : ℝ} (hε : 0 < ε) (hs : s.pairwise fun x y => ε ≤ dist x y) :
  IsClosed s :=
  is_closed_of_spaced_out (dist_mem_uniformity hε)$
    by 
      simpa using hs

theorem closed_embedding_of_pairwise_le_dist {α : Type _} [TopologicalSpace α] [DiscreteTopology α] {ε : ℝ} (hε : 0 < ε)
  {f : α → γ} (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) : ClosedEmbedding f :=
  closed_embedding_of_spaced_out (dist_mem_uniformity hε)$
    by 
      simpa using hf

/-- If `f : β → α` sends any two distinct points to points at distance at least `ε > 0`, then
`f` is a uniform embedding with respect to the discrete uniformity on `β`. -/
theorem uniform_embedding_bot_of_pairwise_le_dist {β : Type _} {ε : ℝ} (hε : 0 < ε) {f : β → α}
  (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
  @UniformEmbedding _ _ ⊥
    (by 
      infer_instance)
    f :=
  uniform_embedding_of_spaced_out (dist_mem_uniformity hε)$
    by 
      simpa using hf

end Metric

/-- Build a new metric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
  (H : @uniformity _ U = @uniformity _ EmetricSpace.toUniformSpace') : MetricSpace γ :=
  { PseudoMetricSpace.replaceUniformity m.to_pseudo_metric_space H with eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _ }

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. In this definition, the distance
is given separately, to be able to prescribe some expression which is not defeq to the push-forward
of the edistance to reals. -/
def EmetricSpace.toMetricSpaceOfDist {α : Type u} [e : EmetricSpace α] (dist : α → α → ℝ)
  (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤) (h : ∀ x y, dist x y = Ennreal.toReal (edist x y)) : MetricSpace α :=
  { PseudoEmetricSpace.toPseudoMetricSpaceOfDist dist edist_ne_top h with dist,
    eq_of_dist_eq_zero :=
      fun x y hxy =>
        by 
          simpa [h, Ennreal.to_real_eq_zero_iff, edist_ne_top x y] using hxy }

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. -/
def EmetricSpace.toMetricSpace {α : Type u} [e : EmetricSpace α] (h : ∀ x y : α, edist x y ≠ ⊤) : MetricSpace α :=
  EmetricSpace.toMetricSpaceOfDist (fun x y => Ennreal.toReal (edist x y)) h fun x y => rfl

/-- Metric space structure pulled back by an injective function. Injectivity is necessary to
ensure that `dist x y = 0` only if `x = y`. -/
def MetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : MetricSpace β) : MetricSpace γ :=
  { PseudoMetricSpace.induced f m.to_pseudo_metric_space with eq_of_dist_eq_zero := fun x y h => hf (dist_eq_zero.1 h) }

/-- Pull back a metric space structure by a uniform embedding. This is a version of
`metric_space.induced` useful in case if the domain already has a `uniform_space` structure. -/
def UniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [MetricSpace β] (f : α → β) (h : UniformEmbedding f) :
  MetricSpace α :=
  (MetricSpace.induced f h.inj ‹_›).replaceUniformity h.comap_uniformity.symm

instance Subtype.metricSpace {α : Type _} {p : α → Prop} [t : MetricSpace α] : MetricSpace (Subtype p) :=
  MetricSpace.induced coeₓ (fun x y => Subtype.ext) t

theorem Subtype.dist_eq {p : α → Prop} (x y : Subtype p) : dist x y = dist (x : α) y :=
  rfl

instance  : MetricSpace Empty :=
  { dist := fun _ _ => 0, dist_self := fun _ => rfl, dist_comm := fun _ _ => rfl,
    eq_of_dist_eq_zero := fun _ _ _ => Subsingleton.elimₓ _ _,
    dist_triangle :=
      fun _ _ _ =>
        show (0 : ℝ) ≤ 0+0 by 
          rw [add_zeroₓ] }

instance  : MetricSpace PUnit :=
  { dist := fun _ _ => 0, dist_self := fun _ => rfl, dist_comm := fun _ _ => rfl,
    eq_of_dist_eq_zero := fun _ _ _ => Subsingleton.elimₓ _ _,
    dist_triangle :=
      fun _ _ _ =>
        show (0 : ℝ) ≤ 0+0 by 
          rw [add_zeroₓ] }

section Real

/-- Instantiate the reals as a metric space. -/
noncomputable instance Real.metricSpace : MetricSpace ℝ :=
  { Real.pseudoMetricSpace with
    eq_of_dist_eq_zero :=
      fun x y h =>
        by 
          simpa [dist, sub_eq_zero] using h }

end Real

section Nnreal

noncomputable instance  : MetricSpace ℝ≥0  :=
  Subtype.metricSpace

end Nnreal

section Prod

noncomputable instance Prod.metricSpaceMax [MetricSpace β] : MetricSpace (γ × β) :=
  { Prod.pseudoMetricSpaceMax with
    eq_of_dist_eq_zero :=
      fun x y h =>
        by 
          cases' max_le_iff.1 (le_of_eqₓ h) with h₁ h₂ 
          exact Prod.ext_iff.2 ⟨dist_le_zero.1 h₁, dist_le_zero.1 h₂⟩ }

end Prod

section Pi

open Finset

variable{π : β → Type _}[Fintype β][∀ b, MetricSpace (π b)]

/-- A finite product of metric spaces is a metric space, with the sup distance. -/
noncomputable instance metricSpacePi : MetricSpace (∀ b, π b) :=
  { pseudoMetricSpacePi with
    eq_of_dist_eq_zero :=
      fun f g eq0 =>
        by 
          have eq1 : edist f g = 0 :=
            by 
              simp only [edist_dist, eq0, Ennreal.of_real_zero]
          have eq2 : (sup univ fun b : β => edist (f b) (g b)) ≤ 0 := le_of_eqₓ eq1 
          simp only [Finset.sup_le_iff] at eq2 
          exact funext$ fun b => edist_le_zero.1$ eq2 b$ mem_univ b }

end Pi

namespace Metric

section SecondCountable

open TopologicalSpace

/-- A metric space is second countable if one can reconstruct up to any `ε>0` any element of the
space from countably many data. -/
theorem second_countable_of_countable_discretization {α : Type u} [MetricSpace α]
  (H : ∀ ε _ : ε > (0 : ℝ), ∃ (β : Type _)(_ : Encodable β)(F : α → β), ∀ x y, F x = F y → dist x y ≤ ε) :
  second_countable_topology α :=
  by 
    cases' (univ : Set α).eq_empty_or_nonempty with hs hs
    ·
      haveI  : CompactSpace α :=
        ⟨by 
            rw [hs] <;> exact is_compact_empty⟩
      ·
        infer_instance 
    rcases hs with ⟨x0, hx0⟩
    letI this : Inhabited α := ⟨x0⟩
    refine' second_countable_of_almost_dense_set fun ε ε0 => _ 
    rcases H ε ε0 with ⟨β, fβ, F, hF⟩
    resetI 
    let Finv := Function.invFun F 
    refine' ⟨range Finv, ⟨countable_range _, fun x => _⟩⟩
    let x' := Finv (F x)
    have  : F x' = F x := Function.inv_fun_eq ⟨x, rfl⟩
    exact ⟨x', mem_range_self _, hF _ _ this.symm⟩

end SecondCountable

end Metric

section EqRel

-- error in Topology.MetricSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- The canonical equivalence relation on a pseudometric space. -/
def pseudo_metric.dist_setoid (α : Type u) [pseudo_metric_space α] : setoid α :=
setoid.mk (λ
 x
 y, «expr = »(dist x y, 0)) (begin
   unfold [ident equivalence] [],
   repeat { split },
   { exact [expr pseudo_metric_space.dist_self] },
   { assume [binders (x y h)],
     rwa [expr pseudo_metric_space.dist_comm] [] },
   { assume [binders (x y z hxy hyz)],
     refine [expr le_antisymm _ dist_nonneg],
     calc
       «expr ≤ »(dist x z, «expr + »(dist x y, dist y z)) : pseudo_metric_space.dist_triangle _ _ _
       «expr = »(..., «expr + »(0, 0)) : by rw ["[", expr hxy, ",", expr hyz, "]"] []
       «expr = »(..., 0) : by simp [] [] [] [] [] [] }
 end)

attribute [local instance] PseudoMetric.distSetoid

/-- The canonical quotient of a pseudometric space, identifying points at distance `0`. -/
@[reducible]
def PseudoMetricQuot (α : Type u) [PseudoMetricSpace α] : Type _ :=
  Quotientₓ (PseudoMetric.distSetoid α)

instance hasDistMetricQuot {α : Type u} [PseudoMetricSpace α] : HasDist (PseudoMetricQuot α) :=
  { dist :=
      Quotientₓ.lift₂ (fun p q : α => dist p q)
        (by 
          intro x y x' y' hxx' hyy' 
          have Hxx' : dist x x' = 0 := hxx' 
          have Hyy' : dist y y' = 0 := hyy' 
          have A : dist x y ≤ dist x' y' :=
            calc dist x y ≤ dist x x'+dist x' y := PseudoMetricSpace.dist_triangle _ _ _ 
              _ = dist x' y :=
              by 
                simp [Hxx']
              _ ≤ dist x' y'+dist y' y := PseudoMetricSpace.dist_triangle _ _ _ 
              _ = dist x' y' :=
              by 
                simp [PseudoMetricSpace.dist_comm, Hyy']
              
          have B : dist x' y' ≤ dist x y :=
            calc dist x' y' ≤ dist x' x+dist x y' := PseudoMetricSpace.dist_triangle _ _ _ 
              _ = dist x y' :=
              by 
                simp [PseudoMetricSpace.dist_comm, Hxx']
              _ ≤ dist x y+dist y y' := PseudoMetricSpace.dist_triangle _ _ _ 
              _ = dist x y :=
              by 
                simp [Hyy']
              
          exact le_antisymmₓ A B) }

theorem pseudo_metric_quot_dist_eq {α : Type u} [PseudoMetricSpace α] (p q : α) :
  dist («expr⟦ ⟧» p) («expr⟦ ⟧» q) = dist p q :=
  rfl

instance metricSpaceQuot {α : Type u} [PseudoMetricSpace α] : MetricSpace (PseudoMetricQuot α) :=
  { dist_self :=
      by 
        refine' Quotientₓ.ind fun y => _ 
        exact PseudoMetricSpace.dist_self _,
    eq_of_dist_eq_zero :=
      fun xc yc =>
        by 
          exact Quotientₓ.induction_on₂ xc yc fun x y H => Quotientₓ.sound H,
    dist_comm := fun xc yc => Quotientₓ.induction_on₂ xc yc fun x y => PseudoMetricSpace.dist_comm _ _,
    dist_triangle :=
      fun xc yc zc => Quotientₓ.induction_on₃ xc yc zc fun x y z => PseudoMetricSpace.dist_triangle _ _ _ }

end EqRel

