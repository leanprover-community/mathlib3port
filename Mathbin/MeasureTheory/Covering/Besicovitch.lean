import Mathbin.Topology.MetricSpace.Basic 
import Mathbin.SetTheory.CardinalOrdinal 
import Mathbin.MeasureTheory.Integral.Lebesgue 
import Mathbin.MeasureTheory.Covering.VitaliFamily

/-!
# Besicovitch covering theorems

The topological Besicovitch covering theorem ensures that, in a nice metric space, there exists a
number `N` such that, from any family of balls with bounded radii, one can extract `N` families,
each made of disjoint balls, covering together all the centers of the initial family.

By "nice metric space", we mean a technical property stated as follows: there exists no satellite
configuration of `N+1` points (with a given parameter `τ > 1`). Such a configuration is a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This property is for instance
satisfied by finite-dimensional real vector spaces.

In this file, we prove the topological Besicovitch covering theorem,
in `besicovitch.exist_disjoint_covering_families`.

The measurable Besicovitch theorem ensures that, in the same class of metric spaces, if at every
point one considers a class of balls of arbitrarily small radii, called admissible balls, then
one can cover almost all the space by a family of disjoint admissible balls.
It is deduced from the topological Besicovitch theorem, and proved
in `besicovitch.exists_disjoint_closed_ball_covering_ae`.

## Main definitions and results

* `satellite_config α N τ` is the type of all satellite configurations of `N+1` points
  in the metric space `α`, with parameter `τ`.
* `has_besicovitch_covering` is a class recording that there exist `N` and `τ > 1` such that
  there is no satellite configuration of `N+1` points with parameter `τ`.
* `exist_disjoint_covering_families` is the topological Besicovitch covering theorem: from any
  family of balls one can extract finitely many disjoint subfamilies covering the same set.
* `exists_disjoint_closed_ball_covering` is the measurable Besicovitch covering theorem: from any
  family of balls with arbitrarily small radii at every point, one can extract countably many
  disjoint balls covering almost all the space. While the value of `N` is relevant for the precise
  statement of the topological Besicovitch theorem, it becomes irrelevant for the measurable one.
  Therefore, this statement is expressed using the `Prop`-valued
  typeclass `has_besicovitch_covering`.

## Implementation

#### Sketch of proof of the topological Besicovitch theorem:

We choose balls in a greedy way. First choose a ball with maximal radius (or rather, since there
is no guarantee the maximal radius is realized, a ball with radius within a factor `τ` of the
supremum). Then, remove all balls whose center is covered by the first ball, and choose among the
remaining ones a ball with radius close to maximum. Go on forever until there is no available
center (this is a transfinite induction in general).

Then define inductively a coloring of the balls. A ball will be of color `i` if it intersects
already chosen balls of color `0`, ..., `i - 1`, but none of color `i`. In this way, balls of the
same color form a disjoint family, and the space is covered by the families of the different colors.

The nontrivial part is to show that at most `N` colors are used. If one needs `N+1` colors, consider
the first time this happens. Then the corresponding ball intersects `N` balls of the different
colors. Moreover, the inductive construction ensures that the radii of all the balls are controlled:
they form a satellite configuration with `N+1` balls (essentially by definition of satellite
configurations). Since we assume that there are no such configurations, this is a contradiction.

#### Sketch of proof of the measurable Besicovitch theorem:

From the topological Besicovitch theorem, one can find a disjoint countable family of balls
covering a proportion `> 1/(N+1)` of the space. Taking a large enough finite subset of these balls,
one gets the same property for finitely many balls. Their union is closed. Therefore, any point in
the complement has around it an admissible ball not intersecting these finitely many balls. Applying
again the topological Besicovitch theorem, one extracts from these a disjoint countable subfamily
covering a proportion `> 1/(N+1)` of the remaining points, and then even a disjoint finite
subfamily. Then one goes on again and again, covering at each step a positive proportion of the
remaining points, while remaining disjoint from the already chosen balls. The union of all these
balls is the desired almost everywhere covering.
-/


noncomputable theory

universe u

open Metric Set Filter Finₓ MeasureTheory TopologicalSpace

open_locale TopologicalSpace Classical BigOperators Ennreal MeasureTheory Nnreal

/-!
### Satellite configurations
-/


/-- A satellite configuration is a configuration of `N+1` points that shows up in the inductive
construction for the Besicovitch covering theorem. It depends on some parameter `τ ≥ 1`.

This is a family of balls (indexed by `i : fin N.succ`, with center `c i` and radius `r i`) such
that the last ball intersects all the other balls (condition `inter`),
and given any two balls there is an order between them, ensuring that the first ball does not
contain the center of the other one, and the radius of the second ball can not be larger than
the radius of the first ball (up to a factor `τ`). This order corresponds to the order of choice
in the inductive construction: otherwise, the second ball would have been chosen before.
This is the condition `h`.

Finally, the last ball is chosen after all the other ones, meaning that `h` can be strengthened
by keeping only one side of the alternative in `hlast`.
-/
structure Besicovitch.SatelliteConfig(α : Type _)[MetricSpace α](N : ℕ)(τ : ℝ) where 
  c : Finₓ N.succ → α 
  R : Finₓ N.succ → ℝ 
  rpos : ∀ i, 0 < r i 
  h : ∀ i j, i ≠ j → (r i ≤ dist (c i) (c j) ∧ r j ≤ τ*r i) ∨ r j ≤ dist (c j) (c i) ∧ r i ≤ τ*r j 
  hlast : ∀ i _ : i < last N, r i ≤ dist (c i) (c (last N)) ∧ r (last N) ≤ τ*r i 
  inter : ∀ i _ : i < last N, dist (c i) (c (last N)) ≤ r i+r (last N)

/-- A metric space has the Besicovitch covering property if there exist `N` and `τ > 1` such that
there are no satellite configuration of parameter `τ` with `N+1` points. This is the condition that
guarantees that the measurable Besicovitch covering theorem holds. It is satified by
finite-dimensional real vector spaces. -/
class HasBesicovitchCovering(α : Type _)[MetricSpace α] : Prop where 
  no_satellite_config : ∃ (N : ℕ)(τ : ℝ), 1 < τ ∧ IsEmpty (Besicovitch.SatelliteConfig α N τ)

/-- There is always a satellite configuration with a single point. -/
instance  {α : Type _} {τ : ℝ} [Inhabited α] [MetricSpace α] : Inhabited (Besicovitch.SatelliteConfig α 0 τ) :=
  ⟨{ c := fun i => default α, R := fun i => 1, rpos := fun i => zero_lt_one,
      h := fun i j hij => (hij (Subsingleton.elimₓ i j)).elim,
      hlast :=
        fun i hi =>
          by 
            rw [Subsingleton.elimₓ i (last 0)] at hi 
            exact (lt_irreflₓ _ hi).elim,
      inter :=
        fun i hi =>
          by 
            rw [Subsingleton.elimₓ i (last 0)] at hi 
            exact (lt_irreflₓ _ hi).elim }⟩

namespace Besicovitch

namespace SatelliteConfig

variable{α : Type _}[MetricSpace α]{N : ℕ}{τ : ℝ}(a : satellite_config α N τ)

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inter' (i : fin N.succ) : «expr ≤ »(dist (a.c i) (a.c (last N)), «expr + »(a.r i, a.r (last N))) :=
begin
  rcases [expr lt_or_le i (last N), "with", ident H, "|", ident H],
  { exact [expr a.inter i H] },
  { have [ident I] [":", expr «expr = »(i, last N)] [":=", expr top_le_iff.1 H],
    have [] [] [":=", expr (a.rpos (last N)).le],
    simp [] [] ["only"] ["[", expr I, ",", expr add_nonneg this this, ",", expr dist_self, "]"] [] [] }
end

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem hlast' (i : fin N.succ) (h : «expr ≤ »(1, τ)) : «expr ≤ »(a.r (last N), «expr * »(τ, a.r i)) :=
begin
  rcases [expr lt_or_le i (last N), "with", ident H, "|", ident H],
  { exact [expr (a.hlast i H).2] },
  { have [] [":", expr «expr = »(i, last N)] [":=", expr top_le_iff.1 H],
    rw [expr this] [],
    exact [expr le_mul_of_one_le_left (a.rpos _).le h] }
end

end SatelliteConfig

/-! ### Extracting disjoint subfamilies from a ball covering -/


/-- A ball package is a family of balls in a metric space with positive bounded radii. -/
structure ball_package(β : Type _)(α : Type _) where 
  c : β → α 
  R : β → ℝ 
  rpos : ∀ b, 0 < r b 
  rBound : ℝ 
  r_le : ∀ b, r b ≤ r_bound

/-- The ball package made of unit balls. -/
def unit_ball_package (α : Type _) : ball_package α α :=
  { c := id, R := fun _ => 1, rpos := fun _ => zero_lt_one, rBound := 1, r_le := fun _ => le_rfl }

instance  (α : Type _) : Inhabited (ball_package α α) :=
  ⟨unit_ball_package α⟩

/-- A Besicovitch tau-package is a family of balls in a metric space with positive bounded radii,
together with enough data to proceed with the Besicovitch greedy algorithm. We register this in
a single structure to make sure that all our constructions in this algorithm only depend on
one variable. -/
structure tau_package(β : Type _)(α : Type _) extends ball_package β α where 
  τ : ℝ 
  one_lt_tau : 1 < τ

instance  (α : Type _) : Inhabited (tau_package α α) :=
  ⟨{ unit_ball_package α with τ := 2, one_lt_tau := one_lt_two }⟩

variable{α : Type _}[MetricSpace α]{β : Type u}

namespace TauPackage

variable[Nonempty β](p : tau_package β α)

include p

/-- Choose inductively large balls with centers that are not contained in the union of already
chosen balls. This is a transfinite induction. -/
noncomputable def index : Ordinal.{u} → β
| i =>
  let Z := ⋃j : { j // j < i }, ball (p.c (index j)) (p.r (index j))
  let R := supr fun b : { b : β // p.c b ∉ Z } => p.r b 
  Classical.epsilon fun b : β => p.c b ∉ Z ∧ R ≤ p.τ*p.r b

/-- The set of points that are covered by the union of balls selected at steps `< i`. -/
def Union_up_to (i : Ordinal.{u}) : Set α :=
  ⋃j : { j // j < i }, ball (p.c (p.index j)) (p.r (p.index j))

theorem monotone_Union_up_to : Monotone p.Union_up_to :=
  by 
    intro i j hij 
    simp only [Union_up_to]
    apply Union_subset_Union2 
    intro r 
    exact ⟨⟨r, r.2.trans_le hij⟩, subset.refl _⟩

/-- Supremum of the radii of balls whose centers are not yet covered at step `i`. -/
def R (i : Ordinal.{u}) : ℝ :=
  supr fun b : { b : β // p.c b ∉ p.Union_up_to i } => p.r b

/-- Group the balls into disjoint families, by assigning to a ball the smallest color for which
it does not intersect any already chosen ball of this color. -/
noncomputable def color : Ordinal.{u} → ℕ
| i =>
  let A : Set ℕ :=
    ⋃(j : { j // j < i })(hj :
      (closed_ball (p.c (p.index j)) (p.r (p.index j)) ∩ closed_ball (p.c (p.index i)) (p.r (p.index i))).Nonempty),
      {color j}
  Inf (univ \ A)

/-- `p.last_step` is the first ordinal where the construction stops making sense, i.e., `f` returns
garbage since there is no point left to be chosen. We will only use ordinals before this step. -/
def last_step : Ordinal.{u} :=
  Inf { i | ¬∃ b : β, p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ*p.r b }

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem last_step_nonempty : {i | «expr¬ »(«expr∃ , »((b : β), «expr ∧ »(«expr ∉ »(p.c b, p.Union_up_to i), «expr ≤ »(p.R i, «expr * »(p.τ, p.r b)))))}.nonempty :=
begin
  by_contra [],
  suffices [ident H] [":", expr function.injective p.index],
  from [expr not_injective_of_ordinal p.index H],
  assume [binders (x y hxy)],
  wlog [ident x_le_y] [":", expr «expr ≤ »(x, y)] [":=", expr le_total x y] ["using", "[", ident x, ident y, ",", ident y, ident x, "]"],
  rcases [expr eq_or_lt_of_le x_le_y, "with", ident rfl, "|", ident H],
  { refl },
  simp [] [] ["only"] ["[", expr nonempty_def, ",", expr not_exists, ",", expr exists_prop, ",", expr not_and, ",", expr not_lt, ",", expr not_le, ",", expr mem_set_of_eq, ",", expr not_forall, "]"] [] ["at", ident h],
  specialize [expr h y],
  have [ident A] [":", expr «expr ∉ »(p.c (p.index y), p.Union_up_to y)] [],
  { have [] [":", expr «expr = »(p.index y, classical.epsilon (λ
       b : β, «expr ∧ »(«expr ∉ »(p.c b, p.Union_up_to y), «expr ≤ »(p.R y, «expr * »(p.τ, p.r b)))))] [],
    by { rw ["[", expr tau_package.index, "]"] [],
      refl },
    rw [expr this] [],
    exact [expr (classical.epsilon_spec h).1] },
  simp [] [] ["only"] ["[", expr Union_up_to, ",", expr not_exists, ",", expr exists_prop, ",", expr mem_Union, ",", expr mem_closed_ball, ",", expr not_and, ",", expr not_le, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] ["at", ident A],
  specialize [expr A x H],
  simp [] [] [] ["[", expr hxy, "]"] [] ["at", ident A],
  exact [expr (lt_irrefl _ ((p.rpos (p.index y)).trans_le A)).elim]
end

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Every point is covered by chosen balls, before `p.last_step`. -/
theorem mem_Union_up_to_last_step (x : β) : «expr ∈ »(p.c x, p.Union_up_to p.last_step) :=
begin
  have [ident A] [":", expr ∀
   z : β, «expr ∨ »(«expr ∈ »(p.c z, p.Union_up_to p.last_step), «expr < »(«expr * »(p.τ, p.r z), p.R p.last_step))] [],
  { have [] [":", expr «expr ∈ »(p.last_step, {i | «expr¬ »(«expr∃ , »((b : β), «expr ∧ »(«expr ∉ »(p.c b, p.Union_up_to i), «expr ≤ »(p.R i, «expr * »(p.τ, p.r b)))))})] [":=", expr Inf_mem p.last_step_nonempty],
    simpa [] [] ["only"] ["[", expr not_exists, ",", expr mem_set_of_eq, ",", expr not_and_distrib, ",", expr not_le, ",", expr not_not_mem, "]"] [] [] },
  by_contra [],
  rcases [expr A x, "with", ident H, "|", ident H],
  { exact [expr h H] },
  have [ident Rpos] [":", expr «expr < »(0, p.R p.last_step)] [],
  { apply [expr lt_trans (mul_pos (_root_.zero_lt_one.trans p.one_lt_tau) (p.rpos _)) H] },
  have [ident B] [":", expr «expr < »(«expr * »(«expr ⁻¹»(p.τ), p.R p.last_step), p.R p.last_step)] [],
  { conv_rhs [] [] { rw ["<-", expr one_mul (p.R p.last_step)] },
    exact [expr mul_lt_mul (inv_lt_one p.one_lt_tau) le_rfl Rpos zero_le_one] },
  obtain ["⟨", ident y, ",", ident hy1, ",", ident hy2, "⟩", ":", expr «expr∃ , »((y : β), «expr ∧ »(«expr ∉ »(p.c y, p.Union_up_to p.last_step), «expr < »(«expr * »(«expr ⁻¹»(p.τ), p.R p.last_step), p.r y)))],
  { simpa [] [] ["only"] ["[", expr exists_prop, ",", expr mem_range, ",", expr exists_exists_and_eq_and, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] ["using", expr exists_lt_of_lt_cSup _ B],
    rw ["[", "<-", expr image_univ, ",", expr nonempty_image_iff, "]"] [],
    exact [expr ⟨⟨_, h⟩, mem_univ _⟩] },
  rcases [expr A y, "with", ident Hy, "|", ident Hy],
  { exact [expr hy1 Hy] },
  { rw ["<-", expr div_eq_inv_mul] ["at", ident hy2],
    have [] [] [":=", expr (div_le_iff' (_root_.zero_lt_one.trans p.one_lt_tau)).1 hy2.le],
    exact [expr lt_irrefl _ (Hy.trans_le this)] }
end

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If there are no configurations of satellites with `N+1` points, one never uses more than `N`
distinct families in the Besicovitch inductive construction. -/
theorem color_lt
{i : ordinal.{u}}
(hi : «expr < »(i, p.last_step))
{N : exprℕ()}
(hN : is_empty (satellite_config α N p.τ)) : «expr < »(p.color i, N) :=
begin
  induction [expr i] ["using", ident ordinal.induction] ["with", ident i, ident IH] [],
  let [ident A] [":", expr set exprℕ()] [":=", expr «expr⋃ , »((j : {j // «expr < »(j, i)})
    (hj : «expr ∩ »(closed_ball (p.c (p.index j)) (p.r (p.index j)), closed_ball (p.c (p.index i)) (p.r (p.index i))).nonempty), {p.color j})],
  have [ident color_i] [":", expr «expr = »(p.color i, Inf «expr \ »(univ, A))] [],
  by rw ["[", expr color, "]"] [],
  rw [expr color_i] [],
  have [ident N_mem] [":", expr «expr ∈ »(N, «expr \ »(univ, A))] [],
  { simp [] [] ["only"] ["[", expr not_exists, ",", expr true_and, ",", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, ",", expr mem_closed_ball, ",", expr not_and, ",", expr mem_univ, ",", expr mem_diff, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] [],
    assume [binders (j ji hj)],
    exact [expr (IH j ji (ji.trans hi)).ne'] },
  suffices [] [":", expr «expr ≠ »(Inf «expr \ »(univ, A), N)],
  { rcases [expr (cInf_le (order_bot.bdd_below «expr \ »(univ, A)) N_mem).lt_or_eq, "with", ident H, "|", ident H],
    { exact [expr H] },
    { exact [expr (this H).elim] } },
  assume [binders (Inf_eq_N)],
  have [] [":", expr ∀
   k, «expr < »(k, N) → «expr∃ , »((j), «expr ∧ »(«expr < »(j, i), «expr ∧ »(«expr ∩ »(closed_ball (p.c (p.index j)) (p.r (p.index j)), closed_ball (p.c (p.index i)) (p.r (p.index i))).nonempty, «expr = »(k, p.color j))))] [],
  { assume [binders (k hk)],
    rw ["<-", expr Inf_eq_N] ["at", ident hk],
    have [] [":", expr «expr ∈ »(k, A)] [],
    by simpa [] [] ["only"] ["[", expr true_and, ",", expr mem_univ, ",", expr not_not, ",", expr mem_diff, "]"] [] ["using", expr nat.not_mem_of_lt_Inf hk],
    simp [] [] [] [] [] ["at", ident this],
    simpa [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, ",", expr mem_closed_ball, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] [] },
  choose ["!"] [ident g] [ident hg] ["using", expr this],
  let [ident G] [":", expr exprℕ() → ordinal] [":=", expr λ n, if «expr = »(n, N) then i else g n],
  have [ident color_G] [":", expr ∀ n, «expr ≤ »(n, N) → «expr = »(p.color (G n), n)] [],
  { assume [binders (n hn)],
    unfreezingI { rcases [expr hn.eq_or_lt, "with", ident rfl, "|", ident H] },
    { simp [] [] ["only"] ["[", expr G, "]"] [] [],
      simp [] [] ["only"] ["[", expr color_i, ",", expr Inf_eq_N, ",", expr if_true, ",", expr eq_self_iff_true, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr G, "]"] [] [],
      simp [] [] ["only"] ["[", expr H.ne, ",", expr (hg n H).right.right.symm, ",", expr if_false, "]"] [] [] } },
  have [ident G_lt_last] [":", expr ∀ n, «expr ≤ »(n, N) → «expr < »(G n, p.last_step)] [],
  { assume [binders (n hn)],
    unfreezingI { rcases [expr hn.eq_or_lt, "with", ident rfl, "|", ident H] },
    { simp [] [] ["only"] ["[", expr G, "]"] [] [],
      simp [] [] ["only"] ["[", expr hi, ",", expr if_true, ",", expr eq_self_iff_true, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr G, "]"] [] [],
      simp [] [] ["only"] ["[", expr H.ne, ",", expr (hg n H).left.trans hi, ",", expr if_false, "]"] [] [] } },
  have [ident fGn] [":", expr ∀
   n, «expr ≤ »(n, N) → «expr ∧ »(«expr ∉ »(p.c (p.index (G n)), p.Union_up_to (G n)), «expr ≤ »(p.R (G n), «expr * »(p.τ, p.r (p.index (G n)))))] [],
  { assume [binders (n hn)],
    have [] [":", expr «expr = »(p.index (G n), classical.epsilon (λ
       t, «expr ∧ »(«expr ∉ »(p.c t, p.Union_up_to (G n)), «expr ≤ »(p.R (G n), «expr * »(p.τ, p.r t)))))] [],
    by { rw [expr index] [],
      refl },
    rw [expr this] [],
    have [] [":", expr «expr∃ , »((t), «expr ∧ »(«expr ∉ »(p.c t, p.Union_up_to (G n)), «expr ≤ »(p.R (G n), «expr * »(p.τ, p.r t))))] [],
    by simpa [] [] ["only"] ["[", expr not_exists, ",", expr exists_prop, ",", expr not_and, ",", expr not_lt, ",", expr not_le, ",", expr mem_set_of_eq, ",", expr not_forall, "]"] [] ["using", expr not_mem_of_lt_cInf (G_lt_last n hn) (order_bot.bdd_below _)],
    exact [expr classical.epsilon_spec this] },
  have [ident Gab] [":", expr ∀
   a
   b : fin (nat.succ N), «expr < »(G a, G b) → «expr ∧ »(«expr ≤ »(p.r (p.index (G a)), dist (p.c (p.index (G a))) (p.c (p.index (G b)))), «expr ≤ »(p.r (p.index (G b)), «expr * »(p.τ, p.r (p.index (G a)))))] [],
  { assume [binders (a b G_lt)],
    have [ident ha] [":", expr «expr ≤ »((a : exprℕ()), N)] [":=", expr nat.lt_succ_iff.1 a.2],
    have [ident hb] [":", expr «expr ≤ »((b : exprℕ()), N)] [":=", expr nat.lt_succ_iff.1 b.2],
    split,
    { have [] [] [":=", expr (fGn b hb).1],
      simp [] [] ["only"] ["[", expr Union_up_to, ",", expr not_exists, ",", expr exists_prop, ",", expr mem_Union, ",", expr mem_closed_ball, ",", expr not_and, ",", expr not_le, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] ["at", ident this],
      simpa [] [] ["only"] ["[", expr dist_comm, ",", expr mem_ball, ",", expr not_lt, "]"] [] ["using", expr this (G a) G_lt] },
    { apply [expr le_trans _ (fGn a ha).2],
      have [ident B] [":", expr «expr ∉ »(p.c (p.index (G b)), p.Union_up_to (G a))] [],
      { assume [binders (H)],
        exact [expr (fGn b hb).1 (p.monotone_Union_up_to G_lt.le H)] },
      let [ident b'] [":", expr {t // «expr ∉ »(p.c t, p.Union_up_to (G a))}] [":=", expr ⟨p.index (G b), B⟩],
      apply [expr @le_csupr _ _ _ (λ t : {t // «expr ∉ »(p.c t, p.Union_up_to (G a))}, p.r t) _ b'],
      refine [expr ⟨p.r_bound, λ t ht, _⟩],
      simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_range, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] ["at", ident ht],
      rcases [expr ht, "with", "⟨", ident u, ",", ident hu, "⟩"],
      rw ["<-", expr hu.2] [],
      exact [expr p.r_le _] } },
  let [ident sc] [":", expr satellite_config α N p.τ] [":=", expr { c := λ k, p.c (p.index (G k)),
     r := λ k, p.r (p.index (G k)),
     rpos := λ k, p.rpos (p.index (G k)),
     h := begin
       assume [binders (a b a_ne_b)],
       wlog [ident G_le] [":", expr «expr ≤ »(G a, G b)] [":=", expr le_total (G a) (G b)] ["using", "[", ident a, ident b, ",", ident b, ident a, "]"] tactic.skip,
       { have [ident G_lt] [":", expr «expr < »(G a, G b)] [],
         { rcases [expr G_le.lt_or_eq, "with", ident H, "|", ident H],
           { exact [expr H] },
           have [ident A] [":", expr «expr ≠ »((a : exprℕ()), b)] [":=", expr fin.coe_injective.ne a_ne_b],
           rw ["[", "<-", expr color_G a (nat.lt_succ_iff.1 a.2), ",", "<-", expr color_G b (nat.lt_succ_iff.1 b.2), ",", expr H, "]"] ["at", ident A],
           exact [expr (A rfl).elim] },
         exact [expr or.inl (Gab a b G_lt)] },
       { assume [binders (a_ne_b)],
         rw [expr or_comm] [],
         exact [expr this a_ne_b.symm] }
     end,
     hlast := begin
       assume [binders (a ha)],
       have [ident I] [":", expr «expr < »((a : exprℕ()), N)] [":=", expr ha],
       have [] [":", expr «expr < »(G a, G (fin.last N))] [],
       by { dsimp [] ["[", expr G, "]"] [] [],
         simp [] [] [] ["[", expr I.ne, ",", expr (hg a I).1, "]"] [] [] },
       exact [expr Gab _ _ this]
     end,
     inter := begin
       assume [binders (a ha)],
       have [ident I] [":", expr «expr < »((a : exprℕ()), N)] [":=", expr ha],
       have [ident J] [":", expr «expr = »(G (fin.last N), i)] [],
       by { dsimp [] ["[", expr G, "]"] [] [],
         simp [] [] ["only"] ["[", expr if_true, ",", expr eq_self_iff_true, "]"] [] [] },
       have [ident K] [":", expr «expr = »(G a, g a)] [],
       { dsimp [] ["[", expr G, "]"] [] [],
         simp [] [] [] ["[", expr I.ne, ",", expr (hg a I).1, "]"] [] [] },
       convert [] [expr dist_le_add_of_nonempty_closed_ball_inter_closed_ball (hg _ I).2.1] []
     end }],
  exact [expr (hN.false : _) sc]
end

end TauPackage

open TauPackage

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The topological Besicovitch covering theorem: there exist finitely many families of disjoint
balls covering all the centers in a package. More specifically, one can use `N` families if there
are no satellite configurations with `N+1` points. -/
theorem exist_disjoint_covering_families
{N : exprℕ()}
{τ : exprℝ()}
(hτ : «expr < »(1, τ))
(hN : is_empty (satellite_config α N τ))
(q : ball_package β α) : «expr∃ , »((s : fin N → set β), «expr ∧ »(∀
  i : fin N, (s i).pairwise_disjoint (λ
   j, closed_ball (q.c j) (q.r j)), «expr ⊆ »(range q.c, «expr⋃ , »((i : fin N), «expr⋃ , »((j «expr ∈ » s i), ball (q.c j) (q.r j)))))) :=
begin
  casesI [expr is_empty_or_nonempty β] [],
  { refine [expr ⟨λ i, «expr∅»(), λ i, pairwise_disjoint_empty, _⟩],
    rw ["[", "<-", expr image_univ, ",", expr eq_empty_of_is_empty (univ : set β), "]"] [],
    simp [] [] [] [] [] [] },
  let [ident p] [":", expr tau_package β α] [":=", expr { τ := τ, one_lt_tau := hτ, ..q }],
  let [ident s] [] [":=", expr λ
   i : fin N, «expr⋃ , »((k : ordinal.{u})
    (hk : «expr < »(k, p.last_step))
    (h'k : «expr = »(p.color k, i)), ({p.index k} : set β))],
  refine [expr ⟨s, λ i, _, _⟩],
  { assume [binders (x hx y hy x_ne_y)],
    obtain ["⟨", ident jx, ",", ident jx_lt, ",", ident jxi, ",", ident rfl, "⟩", ":", expr «expr∃ , »((jx : ordinal), «expr ∧ »(«expr < »(jx, p.last_step), «expr ∧ »(«expr = »(p.color jx, i), «expr = »(x, p.index jx))))],
    by simpa [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, "]"] [] ["using", expr hx],
    obtain ["⟨", ident jy, ",", ident jy_lt, ",", ident jyi, ",", ident rfl, "⟩", ":", expr «expr∃ , »((jy : ordinal), «expr ∧ »(«expr < »(jy, p.last_step), «expr ∧ »(«expr = »(p.color jy, i), «expr = »(y, p.index jy))))],
    by simpa [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, "]"] [] ["using", expr hy],
    wlog [ident jxy] [":", expr «expr ≤ »(jx, jy)] [":=", expr le_total jx jy] ["using", "[", ident jx, ident jy, ",", ident jy, ident jx, "]"] tactic.skip,
    swap,
    { assume [binders (h1 h2 h3 h4 h5 h6 h7)],
      rw ["[", expr function.on_fun, ",", expr disjoint.comm, "]"] [],
      exact [expr this h4 h5 h6 h1 h2 h3 h7.symm] },
    replace [ident jxy] [":", expr «expr < »(jx, jy)] [],
    by { rcases [expr lt_or_eq_of_le jxy, "with", ident H, "|", ident rfl],
      { exact [expr H] },
      { exact [expr (x_ne_y rfl).elim] } },
    let [ident A] [":", expr set exprℕ()] [":=", expr «expr⋃ , »((j : {j // «expr < »(j, jy)})
      (hj : «expr ∩ »(closed_ball (p.c (p.index j)) (p.r (p.index j)), closed_ball (p.c (p.index jy)) (p.r (p.index jy))).nonempty), {p.color j})],
    have [ident color_j] [":", expr «expr = »(p.color jy, Inf «expr \ »(univ, A))] [],
    by rw ["[", expr tau_package.color, "]"] [],
    have [] [":", expr «expr ∈ »(p.color jy, «expr \ »(univ, A))] [],
    { rw [expr color_j] [],
      apply [expr Inf_mem],
      refine [expr ⟨N, _⟩],
      simp [] [] ["only"] ["[", expr not_exists, ",", expr true_and, ",", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, ",", expr not_and, ",", expr mem_univ, ",", expr mem_diff, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] [],
      assume [binders (k hk H)],
      exact [expr (p.color_lt (hk.trans jy_lt) hN).ne'] },
    simp [] [] ["only"] ["[", expr not_exists, ",", expr true_and, ",", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, ",", expr not_and, ",", expr mem_univ, ",", expr mem_diff, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] ["at", ident this],
    specialize [expr this jx jxy],
    contrapose ["!"] [ident this],
    simpa [] [] ["only"] ["[", expr jxi, ",", expr jyi, ",", expr and_true, ",", expr eq_self_iff_true, ",", "<-", expr not_disjoint_iff_nonempty_inter, "]"] [] [] },
  { refine [expr range_subset_iff.2 (λ b, _)],
    obtain ["⟨", ident a, ",", ident ha, "⟩", ":", expr «expr∃ , »((a : ordinal), «expr ∧ »(«expr < »(a, p.last_step), «expr < »(dist (p.c b) (p.c (p.index a)), p.r (p.index a))))],
    by simpa [] [] ["only"] ["[", expr Union_up_to, ",", expr exists_prop, ",", expr mem_Union, ",", expr mem_ball, ",", expr subtype.exists, ",", expr subtype.coe_mk, "]"] [] ["using", expr p.mem_Union_up_to_last_step b],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr mem_ball, ",", expr mem_singleton_iff, ",", expr bUnion_and', ",", expr exists_eq_left, ",", expr Union_exists, ",", expr exists_and_distrib_left, "]"] [] [],
    exact [expr ⟨⟨p.color a, p.color_lt ha.1 hN⟩, p.index a, ⟨a, rfl, ha.1, rfl⟩, ha.2⟩] }
end

/-!
### The measurable Besicovitch covering theorem
-/


open_locale Nnreal

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Consider, for each `x` in a set `s`, a radius `r x ∈ (0, 1]`. Then one can find finitely
many disjoint balls of the form `closed_ball x (r x)` covering a proportion `1/(N+1)` of `s`, if
there are no satellite configurations with `N+1` points.
-/
theorem exist_finset_disjoint_balls_large_measure
[second_countable_topology α]
[measurable_space α]
[opens_measurable_space α]
(μ : measure α)
[is_finite_measure μ]
{N : exprℕ()}
{τ : exprℝ()}
(hτ : «expr < »(1, τ))
(hN : is_empty (satellite_config α N τ))
(s : set α)
(r : α → exprℝ())
(rpos : ∀ x «expr ∈ » s, «expr < »(0, r x))
(rle : ∀
 x «expr ∈ » s, «expr ≤ »(r x, 1)) : «expr∃ , »((t : finset α), «expr ∧ »(«expr ⊆ »(«expr↑ »(t), s), «expr ∧ »(«expr ≤ »(μ «expr \ »(s, «expr⋃ , »((x «expr ∈ » t), closed_ball x (r x))), «expr * »(«expr / »(N, «expr + »(N, 1)), μ s)), (t : set α).pairwise_disjoint (λ
    x, closed_ball x (r x))))) :=
begin
  rcases [expr le_or_lt (μ s) 0, "with", ident hμs, "|", ident hμs],
  { have [] [":", expr «expr = »(μ s, 0)] [":=", expr le_bot_iff.1 hμs],
    refine [expr ⟨«expr∅»(), by simp [] [] ["only"] ["[", expr finset.coe_empty, ",", expr empty_subset, "]"] [] [], _, _⟩],
    { simp [] [] ["only"] ["[", expr this, ",", expr diff_empty, ",", expr Union_false, ",", expr Union_empty, ",", expr nonpos_iff_eq_zero, ",", expr mul_zero, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr finset.coe_empty, ",", expr pairwise_disjoint_empty, "]"] [] [] } },
  casesI [expr is_empty_or_nonempty α] [],
  { simp [] [] ["only"] ["[", expr eq_empty_of_is_empty s, ",", expr measure_empty, "]"] [] ["at", ident hμs],
    exact [expr (lt_irrefl _ hμs).elim] },
  have [ident Npos] [":", expr «expr ≠ »(N, 0)] [],
  { unfreezingI { rintros [ident rfl] },
    inhabit [expr α] [],
    exact [expr not_is_empty_of_nonempty _ hN] },
  obtain ["⟨", ident o, ",", ident so, ",", ident omeas, ",", ident μo, "⟩", ":", expr «expr∃ , »((o : set α), «expr ∧ »(«expr ⊆ »(s, o), «expr ∧ »(measurable_set o, «expr = »(μ o, μ s)))), ":=", expr exists_measurable_superset μ s],
  let [ident a] [":", expr ball_package s α] [":=", expr { c := λ x, x,
     r := λ x, r x,
     rpos := λ x, rpos x x.2,
     r_bound := 1,
     r_le := λ x, rle x x.2 }],
  rcases [expr exist_disjoint_covering_families hτ hN a, "with", "⟨", ident u, ",", ident hu, ",", ident hu', "⟩"],
  have [ident u_count] [":", expr ∀ i, countable (u i)] [],
  { assume [binders (i)],
    refine [expr (hu i).countable_of_nonempty_interior (λ j hj, _)],
    have [] [":", expr (ball (j : α) (r j)).nonempty] [":=", expr nonempty_ball.2 (a.rpos _)],
    exact [expr this.mono ball_subset_interior_closed_ball] },
  let [ident v] [":", expr fin N → set α] [":=", expr λ
   i, «expr⋃ , »((x : s) (hx : «expr ∈ »(x, u i)), closed_ball x (r x))],
  have [] [":", expr ∀
   i, measurable_set (v i)] [":=", expr λ i, measurable_set.bUnion (u_count i) (λ b hb, measurable_set_closed_ball)],
  have [ident A] [":", expr «expr = »(s, «expr⋃ , »((i : fin N), «expr ∩ »(s, v i)))] [],
  { refine [expr subset.antisymm _ (Union_subset (λ i, inter_subset_left _ _))],
    assume [binders (x hx)],
    obtain ["⟨", ident i, ",", ident y, ",", ident hxy, ",", ident h', "⟩", ":", expr «expr∃ , »((i : fin N)
      (i_1 : «expr↥ »(s))
      (i : «expr ∈ »(i_1, u i)), «expr ∈ »(x, ball «expr↑ »(i_1) (r «expr↑ »(i_1))))],
    { have [] [":", expr «expr ∈ »(x, range a.c)] [],
      by simpa [] [] ["only"] ["[", expr subtype.range_coe_subtype, ",", expr set_of_mem_eq, "]"] [] [],
      simpa [] [] ["only"] ["[", expr mem_Union, "]"] [] ["using", expr hu' this] },
    refine [expr mem_Union.2 ⟨i, ⟨hx, _⟩⟩],
    simp [] [] ["only"] ["[", expr v, ",", expr exists_prop, ",", expr mem_Union, ",", expr set_coe.exists, ",", expr exists_and_distrib_right, ",", expr subtype.coe_mk, "]"] [] [],
    exact [expr ⟨y, ⟨y.2, by simpa [] [] ["only"] ["[", expr subtype.coe_eta, "]"] [] []⟩, ball_subset_closed_ball h'⟩] },
  have [ident S] [":", expr «expr ≤ »(«expr∑ , »((i : fin N), «expr / »(μ s, N)), «expr∑ , »((i), μ «expr ∩ »(s, v i)))] [":=", expr calc
     «expr = »(«expr∑ , »((i : fin N), «expr / »(μ s, N)), μ s) : begin
       simp [] [] ["only"] ["[", expr finset.card_fin, ",", expr finset.sum_const, ",", expr nsmul_eq_mul, "]"] [] [],
       rw [expr ennreal.mul_div_cancel'] [],
       { simp [] [] ["only"] ["[", expr Npos, ",", expr ne.def, ",", expr nat.cast_eq_zero, ",", expr not_false_iff, "]"] [] [] },
       { exact [expr ennreal.coe_nat_ne_top] }
     end
     «expr ≤ »(..., «expr∑ , »((i), μ «expr ∩ »(s, v i))) : by { conv_lhs [] [] { rw [expr A] },
       apply [expr measure_Union_fintype_le] }],
  obtain ["⟨", ident i, ",", "-", ",", ident hi, "⟩", ":", expr «expr∃ , »((i : fin N)
    (hi : «expr ∈ »(i, finset.univ)), «expr ≤ »(«expr / »(μ s, N), μ «expr ∩ »(s, v i)))],
  { apply [expr ennreal.exists_le_of_sum_le _ S],
    exact [expr ⟨⟨0, bot_lt_iff_ne_bot.2 Npos⟩, finset.mem_univ _⟩] },
  replace [ident hi] [":", expr «expr < »(«expr / »(μ s, «expr + »(N, 1)), μ «expr ∩ »(s, v i))] [],
  { apply [expr lt_of_lt_of_le _ hi],
    apply [expr (ennreal.mul_lt_mul_left hμs.ne' (measure_lt_top μ s).ne).2],
    rw [expr ennreal.inv_lt_inv] [],
    conv_lhs [] [] { rw ["<-", expr add_zero (N : «exprℝ≥0∞»())] },
    exact [expr ennreal.add_lt_add_left (ennreal.nat_ne_top N) ennreal.zero_lt_one] },
  have [ident B] [":", expr «expr = »(μ «expr ∩ »(o, v i), «expr∑' , »((x : u i), μ «expr ∩ »(o, closed_ball x (r x))))] [],
  { have [] [":", expr «expr = »(«expr ∩ »(o, v i), «expr⋃ , »((x : s)
       (hx : «expr ∈ »(x, u i)), «expr ∩ »(o, closed_ball x (r x))))] [],
    by simp [] [] ["only"] ["[", expr inter_Union, "]"] [] [],
    rw ["[", expr this, ",", expr measure_bUnion (u_count i), "]"] [],
    { refl },
    { exact [expr (hu i).mono (λ k, inter_subset_right _ _)] },
    { exact [expr λ b hb, omeas.inter measurable_set_closed_ball] } },
  obtain ["⟨", ident w, ",", ident hw, "⟩", ":", expr «expr∃ , »((w : finset (u i)), «expr < »(«expr / »(μ s, «expr + »(N, 1)), «expr∑ in , »((x : u i), w, μ «expr ∩ »(o, closed_ball (x : α) (r (x : α))))))],
  { have [ident C] [":", expr has_sum (λ x : u i, μ «expr ∩ »(o, closed_ball x (r x))) (μ «expr ∩ »(o, v i))] [],
    by { rw [expr B] [],
      exact [expr ennreal.summable.has_sum] },
    have [] [":", expr «expr < »(«expr / »(μ s, «expr + »(N, 1)), μ «expr ∩ »(o, v i))] [":=", expr hi.trans_le (measure_mono (inter_subset_inter_left _ so))],
    exact [expr ((tendsto_order.1 C).1 _ this).exists] },
  refine [expr ⟨finset.image (λ x : u i, x) w, _, _, _⟩],
  { simp [] [] ["only"] ["[", expr image_subset_iff, ",", expr coe_coe, ",", expr finset.coe_image, "]"] [] [],
    assume [binders (y hy)],
    simp [] [] ["only"] ["[", expr subtype.coe_prop, ",", expr mem_preimage, "]"] [] [] },
  { suffices [ident H] [":", expr «expr ≤ »(μ «expr \ »(o, «expr⋃ , »((x «expr ∈ » w), closed_ball «expr↑ »(x) (r «expr↑ »(x)))), «expr * »(«expr / »(N, «expr + »(N, 1)), μ s))],
    { rw ["[", expr finset.set_bUnion_finset_image, "]"] [],
      exact [expr le_trans (measure_mono (diff_subset_diff so (subset.refl _))) H] },
    rw ["[", "<-", expr diff_inter_self_eq_diff, ",", expr measure_diff_le_iff_le_add _ omeas (inter_subset_right _ _) (measure_lt_top μ _).ne, "]"] [],
    swap,
    { apply [expr measurable_set.inter _ omeas],
      haveI [] [":", expr encodable (u i)] [":=", expr (u_count i).to_encodable],
      exact [expr measurable_set.Union (λ b, measurable_set.Union_Prop (λ hb, measurable_set_closed_ball))] },
    calc
      «expr = »(μ o, «expr + »(«expr * »(«expr / »(1, «expr + »(N, 1)), μ s), «expr * »(«expr / »(N, «expr + »(N, 1)), μ s))) : by { rw ["[", expr μo, ",", "<-", expr add_mul, ",", expr ennreal.div_add_div_same, ",", expr add_comm, ",", expr ennreal.div_self, ",", expr one_mul, "]"] []; simp [] [] [] [] [] [] }
      «expr ≤ »(..., «expr + »(μ «expr ∩ »(«expr⋃ , »((x «expr ∈ » w), closed_ball «expr↑ »(x) (r «expr↑ »(x))), o), «expr * »(«expr / »(N, «expr + »(N, 1)), μ s))) : begin
        refine [expr add_le_add _ le_rfl],
        rw ["[", expr div_eq_mul_inv, ",", expr one_mul, ",", expr mul_comm, ",", "<-", expr div_eq_mul_inv, "]"] [],
        apply [expr hw.le.trans (le_of_eq _)],
        rw ["[", "<-", expr finset.set_bUnion_coe, ",", expr inter_comm _ o, ",", expr inter_bUnion, ",", expr finset.set_bUnion_coe, ",", expr measure_bUnion_finset, "]"] [],
        { have [] [":", expr (w : set (u i)).pairwise_disjoint (λ b : u i, closed_ball (b : α) (r (b : α)))] [],
          by { assume [binders (k hk l hl hkl)],
            exact [expr hu i k k.2 l l.2 (subtype.coe_injective.ne hkl)] },
          exact [expr this.mono (λ k, inter_subset_right _ _)] },
        { assume [binders (b hb)],
          apply [expr omeas.inter measurable_set_closed_ball] }
      end },
  { assume [binders (k hk l hl hkl)],
    obtain ["⟨", ident k', ",", ident k'w, ",", ident rfl, "⟩", ":", expr «expr∃ , »((k' : u i), «expr ∧ »(«expr ∈ »(k', w), «expr = »(«expr↑ »(«expr↑ »(k')), k)))],
    by simpa [] [] ["only"] ["[", expr mem_image, ",", expr finset.mem_coe, ",", expr coe_coe, ",", expr finset.coe_image, "]"] [] ["using", expr hk],
    obtain ["⟨", ident l', ",", ident l'w, ",", ident rfl, "⟩", ":", expr «expr∃ , »((l' : u i), «expr ∧ »(«expr ∈ »(l', w), «expr = »(«expr↑ »(«expr↑ »(l')), l)))],
    by simpa [] [] ["only"] ["[", expr mem_image, ",", expr finset.mem_coe, ",", expr coe_coe, ",", expr finset.coe_image, "]"] [] ["using", expr hl],
    have [ident k'nel'] [":", expr «expr ≠ »((k' : s), l')] [],
    by { assume [binders (h)],
      rw [expr h] ["at", ident hkl],
      exact [expr hkl rfl] },
    exact [expr hu i k' k'.2 l' l'.2 k'nel'] }
end

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is finite, and that the space has the Besicovitch
covering property (which is satisfied for instance by normed real vector spaces). It expresses the
conclusion in a slightly awkward form (with a subset of `α × ℝ`) coming from the proof technique.
For a version assuming that the measure is sigma-finite,
see `exists_disjoint_closed_ball_covering_ae_aux`.
For a version giving the conclusion in a nicer form, see `exists_disjoint_closed_ball_covering_ae`.
-/
theorem exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux
[second_countable_topology α]
[hb : has_besicovitch_covering α]
[measurable_space α]
[opens_measurable_space α]
(μ : measure α)
[is_finite_measure μ]
(f : α → set exprℝ())
(s : set α)
(hf : ∀ x «expr ∈ » s, (f x).nonempty)
(hf' : ∀ x «expr ∈ » s, «expr ⊆ »(f x, Ioi 0))
(hf'' : ∀
 x «expr ∈ » s, «expr ≤ »(Inf (f x), 0)) : «expr∃ , »((t : set «expr × »(α, exprℝ())), «expr ∧ »(countable t, «expr ∧ »(∀
   p : «expr × »(α, exprℝ()), «expr ∈ »(p, t) → «expr ∈ »(p.1, s), «expr ∧ »(∀
    p : «expr × »(α, exprℝ()), «expr ∈ »(p, t) → «expr ∈ »(p.2, f p.1), «expr ∧ »(«expr = »(μ «expr \ »(s, «expr⋃ , »((p : «expr × »(α, exprℝ()))
        (hp : «expr ∈ »(p, t)), closed_ball p.1 p.2)), 0), t.pairwise_disjoint (λ p, closed_ball p.1 p.2)))))) :=
begin
  rcases [expr hb.no_satellite_config, "with", "⟨", ident N, ",", ident τ, ",", ident hτ, ",", ident hN, "⟩"],
  let [ident P] [":", expr finset «expr × »(α, exprℝ()) → exprProp()] [":=", expr λ
   t, «expr ∧ »((t : set «expr × »(α, exprℝ())).pairwise_disjoint (λ
     p, closed_ball p.1 p.2), «expr ∧ »(∀
     p : «expr × »(α, exprℝ()), «expr ∈ »(p, t) → «expr ∈ »(p.1, s), ∀
     p : «expr × »(α, exprℝ()), «expr ∈ »(p, t) → «expr ∈ »(p.2, f p.1)))],
  have [] [":", expr ∀
   t : finset «expr × »(α, exprℝ()), P t → «expr∃ , »((u : finset «expr × »(α, exprℝ())), «expr ∧ »(«expr ⊆ »(t, u), «expr ∧ »(P u, «expr ≤ »(μ «expr \ »(s, «expr⋃ , »((p : «expr × »(α, exprℝ()))
         (hp : «expr ∈ »(p, u)), closed_ball p.1 p.2)), «expr * »(«expr / »(N, «expr + »(N, 1)), μ «expr \ »(s, «expr⋃ , »((p : «expr × »(α, exprℝ()))
          (hp : «expr ∈ »(p, t)), closed_ball p.1 p.2)))))))] [],
  { assume [binders (t ht)],
    set [] [ident B] [] [":="] [expr «expr⋃ , »((p : «expr × »(α, exprℝ()))
      (hp : «expr ∈ »(p, t)), closed_ball p.1 p.2)] ["with", ident hB],
    have [ident B_closed] [":", expr is_closed B] [":=", expr is_closed_bUnion (finset.finite_to_set _) (λ
      i hi, is_closed_ball)],
    set [] [ident s'] [] [":="] [expr «expr \ »(s, B)] ["with", ident hs'],
    have [] [":", expr ∀
     x «expr ∈ » s', «expr∃ , »((r «expr ∈ » f x), «expr ∧ »(«expr ≤ »(r, 1), disjoint B (closed_ball x r)))] [],
    { assume [binders (x hx)],
      have [ident xs] [":", expr «expr ∈ »(x, s)] [":=", expr ((mem_diff x).1 hx).1],
      rcases [expr eq_empty_or_nonempty B, "with", ident hB, "|", ident hB],
      { have [] [":", expr «expr < »((0 : exprℝ()), 1)] [":=", expr zero_lt_one],
        rcases [expr exists_lt_of_cInf_lt (hf x xs) ((hf'' x xs).trans_lt zero_lt_one), "with", "⟨", ident r, ",", ident hr, ",", ident h'r, "⟩"],
        exact [expr ⟨r, hr, h'r.le, by simp [] [] ["only"] ["[", expr hB, ",", expr empty_disjoint, "]"] [] []⟩] },
      { let [ident R] [] [":=", expr inf_dist x B],
        have [] [":", expr «expr < »(0, min R 1)] [":=", expr lt_min ((B_closed.not_mem_iff_inf_dist_pos hB).1 ((mem_diff x).1 hx).2) zero_lt_one],
        rcases [expr exists_lt_of_cInf_lt (hf x xs) ((hf'' x xs).trans_lt this), "with", "⟨", ident r, ",", ident hr, ",", ident h'r, "⟩"],
        refine [expr ⟨r, hr, h'r.le.trans (min_le_right _ _), _⟩],
        rw [expr disjoint.comm] [],
        exact [expr disjoint_closed_ball_of_lt_inf_dist (h'r.trans_le (min_le_left _ _))] } },
    choose ["!"] [ident r] [ident hr] ["using", expr this],
    obtain ["⟨", ident v, ",", ident vs', ",", ident hμv, ",", ident hv, "⟩", ":", expr «expr∃ , »((v : finset α), «expr ∧ »(«expr ⊆ »(«expr↑ »(v), s'), «expr ∧ »(«expr ≤ »(μ «expr \ »(s', «expr⋃ , »((x «expr ∈ » v), closed_ball x (r x))), «expr * »(«expr / »(N, «expr + »(N, 1)), μ s')), (v : set α).pairwise_disjoint (λ
         x : α, closed_ball x (r x)))))],
    { have [ident rpos] [":", expr ∀
       x «expr ∈ » s', «expr < »(0, r x)] [":=", expr λ x hx, hf' x ((mem_diff x).1 hx).1 (hr x hx).1],
      have [ident rle] [":", expr ∀ x «expr ∈ » s', «expr ≤ »(r x, 1)] [":=", expr λ x hx, (hr x hx).2.1],
      exact [expr exist_finset_disjoint_balls_large_measure μ hτ hN s' r rpos rle] },
    refine [expr ⟨«expr ∪ »(t, finset.image (λ x, (x, r x)) v), finset.subset_union_left _ _, ⟨_, _, _⟩, _⟩],
    { simp [] [] ["only"] ["[", expr finset.coe_union, ",", expr pairwise_disjoint_union, ",", expr ht.1, ",", expr true_and, ",", expr finset.coe_image, "]"] [] [],
      split,
      { assume [binders (p hp q hq hpq)],
        rcases [expr (mem_image _ _ _).1 hp, "with", "⟨", ident p', ",", ident p'v, ",", ident rfl, "⟩"],
        rcases [expr (mem_image _ _ _).1 hq, "with", "⟨", ident q', ",", ident q'v, ",", ident rfl, "⟩"],
        refine [expr hv p' p'v q' q'v (λ hp'q', _)],
        rw ["[", expr hp'q', "]"] ["at", ident hpq],
        exact [expr hpq rfl] },
      { assume [binders (p hp q hq hpq)],
        rcases [expr (mem_image _ _ _).1 hq, "with", "⟨", ident q', ",", ident q'v, ",", ident rfl, "⟩"],
        apply [expr disjoint_of_subset_left _ (hr q' (vs' q'v)).2.2],
        rw ["[", expr hB, ",", "<-", expr finset.set_bUnion_coe, "]"] [],
        exact [expr subset_bUnion_of_mem hp] } },
    { assume [binders (p hp)],
      rcases [expr finset.mem_union.1 hp, "with", ident h'p, "|", ident h'p],
      { exact [expr ht.2.1 p h'p] },
      { rcases [expr finset.mem_image.1 h'p, "with", "⟨", ident p', ",", ident p'v, ",", ident rfl, "⟩"],
        exact [expr ((mem_diff _).1 (vs' (finset.mem_coe.2 p'v))).1] } },
    { assume [binders (p hp)],
      rcases [expr finset.mem_union.1 hp, "with", ident h'p, "|", ident h'p],
      { exact [expr ht.2.2 p h'p] },
      { rcases [expr finset.mem_image.1 h'p, "with", "⟨", ident p', ",", ident p'v, ",", ident rfl, "⟩"],
        dsimp [] [] [] [],
        exact [expr (hr p' (vs' p'v)).1] } },
    { convert [] [expr hμv] ["using", 2],
      rw ["[", expr finset.set_bUnion_union, ",", "<-", expr diff_diff, ",", expr finset.set_bUnion_finset_image, "]"] [] } },
  choose ["!"] [ident F] [ident hF] ["using", expr this],
  let [ident u] [] [":=", expr λ n, «expr ^[ ]»(F, n) «expr∅»()],
  have [ident u_succ] [":", expr ∀
   n : exprℕ(), «expr = »(u n.succ, F (u n))] [":=", expr λ
   n, by simp [] [] ["only"] ["[", expr u, ",", expr function.comp_app, ",", expr function.iterate_succ', "]"] [] []],
  have [ident Pu] [":", expr ∀ n, P (u n)] [],
  { assume [binders (n)],
    induction [expr n] [] ["with", ident n, ident IH] [],
    { simp [] [] ["only"] ["[", expr u, ",", expr P, ",", expr prod.forall, ",", expr id.def, ",", expr function.iterate_zero, "]"] [] [],
      simp [] [] ["only"] ["[", expr finset.not_mem_empty, ",", expr forall_false_left, ",", expr finset.coe_empty, ",", expr forall_2_true_iff, ",", expr and_self, ",", expr pairwise_disjoint_empty, "]"] [] [] },
    { rw [expr u_succ] [],
      exact [expr (hF (u n) IH).2.1] } },
  refine [expr ⟨«expr⋃ , »((n), u n), countable_Union (λ n, (u n).countable_to_set), _, _, _, _⟩],
  { assume [binders (p hp)],
    rcases [expr mem_Union.1 hp, "with", "⟨", ident n, ",", ident hn, "⟩"],
    exact [expr (Pu n).2.1 p (finset.mem_coe.1 hn)] },
  { assume [binders (p hp)],
    rcases [expr mem_Union.1 hp, "with", "⟨", ident n, ",", ident hn, "⟩"],
    exact [expr (Pu n).2.2 p (finset.mem_coe.1 hn)] },
  { have [ident A] [":", expr ∀
     n, «expr ≤ »(μ «expr \ »(s, «expr⋃ , »((p : «expr × »(α, exprℝ()))
        (hp : «expr ∈ »(p, «expr⋃ , »((n : exprℕ()), (u n : set «expr × »(α, exprℝ()))))), closed_ball p.fst p.snd)), μ «expr \ »(s, «expr⋃ , »((p : «expr × »(α, exprℝ()))
        (hp : «expr ∈ »(p, u n)), closed_ball p.fst p.snd)))] [],
    { assume [binders (n)],
      apply [expr measure_mono],
      apply [expr diff_subset_diff (subset.refl _)],
      exact [expr bUnion_subset_bUnion_left (subset_Union (λ i, (u i : set «expr × »(α, exprℝ()))) n)] },
    have [ident B] [":", expr ∀
     n, «expr ≤ »(μ «expr \ »(s, «expr⋃ , »((p : «expr × »(α, exprℝ()))
        (hp : «expr ∈ »(p, u n)), closed_ball p.fst p.snd)), «expr * »(«expr ^ »(«expr / »(N, «expr + »(N, 1)), n), μ s))] [],
    { assume [binders (n)],
      induction [expr n] [] ["with", ident n, ident IH] [],
      { simp [] [] ["only"] ["[", expr le_refl, ",", expr diff_empty, ",", expr one_mul, ",", expr Union_false, ",", expr Union_empty, ",", expr pow_zero, "]"] [] [] },
      calc
        «expr ≤ »(μ «expr \ »(s, «expr⋃ , »((p : «expr × »(α, exprℝ()))
           (hp : «expr ∈ »(p, u n.succ)), closed_ball p.fst p.snd)), «expr * »(«expr / »(N, «expr + »(N, 1)), μ «expr \ »(s, «expr⋃ , »((p : «expr × »(α, exprℝ()))
            (hp : «expr ∈ »(p, u n)), closed_ball p.fst p.snd)))) : by { rw [expr u_succ] [],
          exact [expr (hF (u n) (Pu n)).2.2] }
        «expr ≤ »(..., «expr * »(«expr ^ »(«expr / »(N, «expr + »(N, 1)), n.succ), μ s)) : by { rw ["[", expr pow_succ, ",", expr mul_assoc, "]"] [],
          exact [expr ennreal.mul_le_mul le_rfl IH] } },
    have [ident C] [":", expr tendsto (λ
      n : exprℕ(), «expr * »(«expr ^ »(«expr / »((N : «exprℝ≥0∞»()), «expr + »(N, 1)), n), μ s)) at_top (expr𝓝() «expr * »(0, μ s))] [],
    { apply [expr ennreal.tendsto.mul_const _ (or.inr (measure_lt_top μ s).ne)],
      apply [expr ennreal.tendsto_pow_at_top_nhds_0_of_lt_1],
      rw ["[", expr ennreal.div_lt_iff, ",", expr one_mul, "]"] [],
      { conv_lhs [] [] { rw ["<-", expr add_zero (N : «exprℝ≥0∞»())] },
        exact [expr ennreal.add_lt_add_left (ennreal.nat_ne_top N) ennreal.zero_lt_one] },
      { simp [] [] ["only"] ["[", expr true_or, ",", expr add_eq_zero_iff, ",", expr ne.def, ",", expr not_false_iff, ",", expr one_ne_zero, ",", expr and_false, "]"] [] [] },
      { simp [] [] ["only"] ["[", expr ennreal.nat_ne_top, ",", expr ne.def, ",", expr not_false_iff, ",", expr or_true, "]"] [] [] } },
    rw [expr zero_mul] ["at", ident C],
    apply [expr le_bot_iff.1],
    exact [expr le_of_tendsto_of_tendsto' tendsto_const_nhds C (λ n, (A n).trans (B n))] },
  { refine [expr (pairwise_disjoint_Union _).2 (λ n, (Pu n).1)],
    apply [expr (monotone_nat_of_le_succ (λ n, _)).directed_le],
    rw [expr u_succ] [],
    exact [expr (hF (u n) (Pu n)).1] }
end

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is sigma-finite, and that the space has the
Besicovitch covering property (which is satisfied for instance by normed real vector spaces).
It expresses the conclusion in a slightly awkward form (with a subset of `α × ℝ`) coming from the
proof technique.
For a version giving the conclusion in a nicer form, see `exists_disjoint_closed_ball_covering_ae`.
-/
theorem exists_disjoint_closed_ball_covering_ae_aux [second_countable_topology α] [HasBesicovitchCovering α]
  [MeasurableSpace α] [OpensMeasurableSpace α] (μ : Measureₓ α) [sigma_finite μ] (f : α → Set ℝ) (s : Set α)
  (hf : ∀ x _ : x ∈ s, (f x).Nonempty) (hf' : ∀ x _ : x ∈ s, f x ⊆ Ioi 0) (hf'' : ∀ x _ : x ∈ s, Inf (f x) ≤ 0) :
  ∃ t : Set (α × ℝ),
    countable t ∧
      (∀ p : α × ℝ, p ∈ t → p.1 ∈ s) ∧
        (∀ p : α × ℝ, p ∈ t → p.2 ∈ f p.1) ∧
          μ (s \ ⋃(p : α × ℝ)(hp : p ∈ t), closed_ball p.1 p.2) = 0 ∧
            t.pairwise_disjoint fun p => closed_ball p.1 p.2 :=
  by 
    (
      rcases exists_absolutely_continuous_is_finite_measure μ with ⟨ν, hν, hμν⟩)
    rcases exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux ν f s hf hf' hf'' with
      ⟨t, t_count, ts, tr, tν, tdisj⟩
    exact ⟨t, t_count, ts, tr, hμν tν, tdisj⟩

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is sigma-finite, and that the space has the
Besicovitch covering property (which is satisfied for instance by normed real vector spaces).
-/
theorem exists_disjoint_closed_ball_covering_ae
[second_countable_topology α]
[hb : has_besicovitch_covering α]
[measurable_space α]
[opens_measurable_space α]
(μ : measure α)
[sigma_finite μ]
(f : α → set exprℝ())
(s : set α)
(hf : ∀ x «expr ∈ » s, (f x).nonempty)
(hf' : ∀ x «expr ∈ » s, «expr ⊆ »(f x, Ioi 0))
(hf'' : ∀
 x «expr ∈ » s, «expr ≤ »(Inf (f x), 0)) : «expr∃ , »((t : set α)
 (r : α → exprℝ()), «expr ∧ »(countable t, «expr ∧ »(«expr ⊆ »(t, s), «expr ∧ »(∀
    x «expr ∈ » t, «expr ∈ »(r x, f x), «expr ∧ »(«expr = »(μ «expr \ »(s, «expr⋃ , »((x «expr ∈ » t), closed_ball x (r x))), 0), t.pairwise_disjoint (λ
      x, closed_ball x (r x))))))) :=
begin
  rcases [expr exists_disjoint_closed_ball_covering_ae_aux μ f s hf hf' hf'', "with", "⟨", ident v, ",", ident v_count, ",", ident vs, ",", ident vf, ",", ident μv, ",", ident v_disj, "⟩"],
  let [ident t] [] [":=", expr «expr '' »(prod.fst, v)],
  have [] [":", expr ∀ x «expr ∈ » t, «expr∃ , »((r : exprℝ()), «expr ∈ »((x, r), v))] [],
  { assume [binders (x hx)],
    rcases [expr (mem_image _ _ _).1 hx, "with", "⟨", "⟨", ident p, ",", ident q, "⟩", ",", ident hp, ",", ident rfl, "⟩"],
    exact [expr ⟨q, hp⟩] },
  choose ["!"] [ident r] [ident hr] ["using", expr this],
  have [ident im_t] [":", expr «expr = »(«expr '' »(λ x, (x, r x), t), v)] [],
  { have [ident I] [":", expr ∀
     p : «expr × »(α, exprℝ()), «expr ∈ »(p, v) → «expr ≤ »(0, p.2)] [":=", expr λ
     p hp, le_of_lt (hf' _ (vs _ hp) (vf _ hp))],
    apply [expr subset.antisymm],
    { simp [] [] ["only"] ["[", expr image_subset_iff, "]"] [] [],
      rintros ["⟨", ident x, ",", ident p, "⟩", ident hxp],
      simp [] [] ["only"] ["[", expr mem_preimage, "]"] [] [],
      exact [expr hr _ (mem_image_of_mem _ hxp)] },
    { rintros ["⟨", ident x, ",", ident p, "⟩", ident hxp],
      have [ident hxrx] [":", expr «expr ∈ »((x, r x), v)] [":=", expr hr _ (mem_image_of_mem _ hxp)],
      have [] [":", expr «expr = »(p, r x)] [],
      { by_contra [],
        have [ident A] [":", expr «expr ≠ »((x, p), (x, r x))] [],
        by simpa [] [] ["only"] ["[", expr true_and, ",", expr prod.mk.inj_iff, ",", expr eq_self_iff_true, ",", expr ne.def, "]"] [] ["using", expr h],
        have [ident H] [] [":=", expr v_disj (x, p) hxp (x, r x) hxrx A],
        contrapose [] [ident H],
        rw [expr not_disjoint_iff_nonempty_inter] [],
        refine [expr ⟨x, by simp [] [] [] ["[", expr I _ hxp, ",", expr I _ hxrx, "]"] [] []⟩] },
      rw [expr this] [],
      apply [expr mem_image_of_mem],
      exact [expr mem_image_of_mem _ hxp] } },
  refine [expr ⟨t, r, v_count.image _, _, _, _, _⟩],
  { assume [binders (x hx)],
    rcases [expr (mem_image _ _ _).1 hx, "with", "⟨", "⟨", ident p, ",", ident q, "⟩", ",", ident hp, ",", ident rfl, "⟩"],
    exact [expr vs _ hp] },
  { assume [binders (x hx)],
    rcases [expr (mem_image _ _ _).1 hx, "with", "⟨", "⟨", ident p, ",", ident q, "⟩", ",", ident hp, ",", ident rfl, "⟩"],
    exact [expr vf _ (hr _ hx)] },
  { have [] [":", expr «expr = »(«expr⋃ , »((x : α)
       (H : «expr ∈ »(x, t)), closed_ball x (r x)), «expr⋃ , »((p : «expr × »(α, exprℝ()))
       (H : «expr ∈ »(p, «expr '' »(λ x, (x, r x), t))), closed_ball p.1 p.2))] [],
    by conv_rhs [] [] { rw [expr bUnion_image] },
    rw ["[", expr this, ",", expr im_t, "]"] [],
    exact [expr μv] },
  { have [ident A] [":", expr inj_on (λ x : α, (x, r x)) t] [],
    by simp [] [] ["only"] ["[", expr inj_on, ",", expr prod.mk.inj_iff, ",", expr implies_true_iff, ",", expr eq_self_iff_true, "]"] [] [] { contextual := tt },
    rwa ["[", "<-", expr im_t, ",", expr A.pairwise_disjoint_image, "]"] ["at", ident v_disj] }
end

-- error in MeasureTheory.Covering.Besicovitch: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a space with the Besicovitch covering property, the set of closed balls with positive radius
forms a Vitali family. This is essentially a restatement of the measurable Besicovitch theorem. -/
protected
def vitali_family
[second_countable_topology α]
[has_besicovitch_covering α]
[measurable_space α]
[opens_measurable_space α]
(μ : measure α)
[sigma_finite μ] : vitali_family μ :=
{ sets_at := λ x, «expr '' »(λ r : exprℝ(), closed_ball x r, Ioi (0 : exprℝ())),
  measurable_set' := begin
    assume [binders (x y hy)],
    obtain ["⟨", ident r, ",", ident rpos, ",", ident rfl, "⟩", ":", expr «expr∃ , »((r : exprℝ()), «expr ∧ »(«expr < »(0, r), «expr = »(closed_ball x r, y)))],
    by simpa [] [] ["only"] ["[", expr mem_image, ",", expr mem_Ioi, "]"] [] ["using", expr hy],
    exact [expr is_closed_ball.measurable_set]
  end,
  nonempty_interior := begin
    assume [binders (x y hy)],
    obtain ["⟨", ident r, ",", ident rpos, ",", ident rfl, "⟩", ":", expr «expr∃ , »((r : exprℝ()), «expr ∧ »(«expr < »(0, r), «expr = »(closed_ball x r, y)))],
    by simpa [] [] ["only"] ["[", expr mem_image, ",", expr mem_Ioi, "]"] [] ["using", expr hy],
    simp [] [] ["only"] ["[", expr nonempty.mono ball_subset_interior_closed_ball, ",", expr rpos, ",", expr nonempty_ball, "]"] [] []
  end,
  nontrivial := λ x ε εpos, ⟨closed_ball x ε, mem_image_of_mem _ εpos, subset.refl _⟩,
  covering := begin
    assume [binders (s f fsubset ffine)],
    let [ident g] [":", expr α → set exprℝ()] [":=", expr λ
     x, {r | «expr ∧ »(«expr < »(0, r), «expr ∈ »(closed_ball x r, f x))}],
    have [ident A] [":", expr ∀ x «expr ∈ » s, (g x).nonempty] [],
    { assume [binders (x xs)],
      obtain ["⟨", ident t, ",", ident tf, ",", ident ht, "⟩", ":", expr «expr∃ , »((t : set α)
        (H : «expr ∈ »(t, f x)), «expr ⊆ »(t, closed_ball x 1)), ":=", expr ffine x xs 1 zero_lt_one],
      obtain ["⟨", ident r, ",", ident rpos, ",", ident rfl, "⟩", ":", expr «expr∃ , »((r : exprℝ()), «expr ∧ »(«expr < »(0, r), «expr = »(closed_ball x r, t)))],
      by simpa [] [] [] [] [] ["using", expr fsubset x xs tf],
      exact [expr ⟨r, rpos, tf⟩] },
    have [ident B] [":", expr ∀ x «expr ∈ » s, «expr ⊆ »(g x, Ioi (0 : exprℝ()))] [],
    { assume [binders (x xs r hr)],
      replace [ident hr] [":", expr «expr ∧ »(«expr < »(0, r), «expr ∈ »(closed_ball x r, f x))] [],
      by simpa [] [] ["only"] [] [] ["using", expr hr],
      exact [expr hr.1] },
    have [ident C] [":", expr ∀ x «expr ∈ » s, «expr ≤ »(Inf (g x), 0)] [],
    { assume [binders (x xs)],
      have [ident g_bdd] [":", expr bdd_below (g x)] [":=", expr ⟨0, λ r hr, hr.1.le⟩],
      refine [expr le_of_forall_le_of_dense (λ ε εpos, _)],
      obtain ["⟨", ident t, ",", ident tf, ",", ident ht, "⟩", ":", expr «expr∃ , »((t : set α)
        (H : «expr ∈ »(t, f x)), «expr ⊆ »(t, closed_ball x ε)), ":=", expr ffine x xs ε εpos],
      obtain ["⟨", ident r, ",", ident rpos, ",", ident rfl, "⟩", ":", expr «expr∃ , »((r : exprℝ()), «expr ∧ »(«expr < »(0, r), «expr = »(closed_ball x r, t)))],
      by simpa [] [] [] [] [] ["using", expr fsubset x xs tf],
      rcases [expr le_total r ε, "with", ident H, "|", ident H],
      { exact [expr (cInf_le g_bdd ⟨rpos, tf⟩).trans H] },
      { have [] [":", expr «expr = »(closed_ball x r, closed_ball x ε)] [":=", expr subset.antisymm ht (closed_ball_subset_closed_ball H)],
        rw [expr this] ["at", ident tf],
        exact [expr cInf_le g_bdd ⟨εpos, tf⟩] } },
    obtain ["⟨", ident t, ",", ident r, ",", ident t_count, ",", ident ts, ",", ident tg, ",", ident μt, ",", ident tdisj, "⟩", ":", expr «expr∃ , »((t : set α)
      (r : α → exprℝ()), «expr ∧ »(countable t, «expr ∧ »(«expr ⊆ »(t, s), «expr ∧ »(∀
         x «expr ∈ » t, «expr ∈ »(r x, g x), «expr ∧ »(«expr = »(μ «expr \ »(s, «expr⋃ , »((x «expr ∈ » t), closed_ball x (r x))), 0), t.pairwise_disjoint (λ
           x, closed_ball x (r x))))))), ":=", expr exists_disjoint_closed_ball_covering_ae μ g s A B C],
    exact [expr ⟨t, λ x, closed_ball x (r x), ts, tdisj, λ x xt, (tg x xt).2, μt⟩]
  end }

end Besicovitch

