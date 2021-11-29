import Mathbin.Algebra.Algebra.RestrictScalars 
import Mathbin.Algebra.Algebra.Subalgebra 
import Mathbin.Analysis.Normed.Group.InfiniteSum 
import Mathbin.Data.Matrix.Basic 
import Mathbin.Topology.Algebra.Module 
import Mathbin.Topology.Instances.Ennreal 
import Mathbin.Topology.Sequences

/-!
# Normed spaces

In this file we define (semi)normed rings, fields, spaces, and algebras. We also prove some theorems
about these definitions.
-/


variable{α : Type _}{β : Type _}{γ : Type _}{ι : Type _}

noncomputable theory

open Filter Metric

open_locale TopologicalSpace BigOperators Nnreal Ennreal uniformity Pointwise

section SemiNormedRing

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class SemiNormedRing(α : Type _) extends HasNorm α, Ringₓ α, PseudoMetricSpace α where 
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a*b) ≤ norm a*norm b

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class NormedRing(α : Type _) extends HasNorm α, Ringₓ α, MetricSpace α where 
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a*b) ≤ norm a*norm b

/-- A normed ring is a seminormed ring. -/
instance (priority := 100)NormedRing.toSemiNormedRing [β : NormedRing α] : SemiNormedRing α :=
  { β with  }

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class SemiNormedCommRing(α : Type _) extends SemiNormedRing α where 
  mul_comm : ∀ (x y : α), (x*y) = y*x

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class NormedCommRing(α : Type _) extends NormedRing α where 
  mul_comm : ∀ (x y : α), (x*y) = y*x

/-- A normed commutative ring is a seminormed commutative ring. -/
instance (priority := 100)NormedCommRing.toSemiNormedCommRing [β : NormedCommRing α] : SemiNormedCommRing α :=
  { β with  }

instance  : NormedCommRing PUnit :=
  { PUnit.normedGroup, PUnit.commRing with
    norm_mul :=
      fun _ _ =>
        by 
          simp  }

/-- A mixin class with the axiom `∥1∥ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class NormOneClass(α : Type _)[HasNorm α][HasOne α] : Prop where 
  norm_one : ∥(1 : α)∥ = 1

export NormOneClass(norm_one)

attribute [simp] norm_one

@[simp]
theorem nnnorm_one [SemiNormedGroup α] [HasOne α] [NormOneClass α] : ∥(1 : α)∥₊ = 1 :=
  Nnreal.eq norm_one

instance (priority := 100)SemiNormedCommRing.toCommRing [β : SemiNormedCommRing α] : CommRingₓ α :=
  { β with  }

instance (priority := 100)NormedRing.toNormedGroup [β : NormedRing α] : NormedGroup α :=
  { β with  }

instance (priority := 100)SemiNormedRing.toSemiNormedGroup [β : SemiNormedRing α] : SemiNormedGroup α :=
  { β with  }

instance Prod.norm_one_class [NormedGroup α] [HasOne α] [NormOneClass α] [NormedGroup β] [HasOne β] [NormOneClass β] :
  NormOneClass (α × β) :=
  ⟨by 
      simp [Prod.norm_def]⟩

variable[SemiNormedRing α]

theorem norm_mul_le (a b : α) : ∥a*b∥ ≤ ∥a∥*∥b∥ :=
  SemiNormedRing.norm_mul _ _

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.semiNormedRing {𝕜 : Type _} {_ : CommRingₓ 𝕜} {E : Type _} [SemiNormedRing E] {_ : Algebra 𝕜 E}
  (s : Subalgebra 𝕜 E) : SemiNormedRing s :=
  { s.to_submodule.semi_normed_group with norm_mul := fun a b => norm_mul_le a.1 b.1 }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.normedRing {𝕜 : Type _} {_ : CommRingₓ 𝕜} {E : Type _} [NormedRing E] {_ : Algebra 𝕜 E}
  (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.semi_normed_ring with  }

theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ∥l.prod∥ ≤ (l.map norm).Prod
| [], h => (h rfl).elim
| [a], _ =>
  by 
    simp 
| a :: b :: l, _ =>
  by 
    rw [List.map_consₓ, List.prod_cons, @List.prod_cons _ _ _ ∥a∥]
    refine' le_transₓ (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)

theorem List.norm_prod_le [NormOneClass α] : ∀ (l : List α), ∥l.prod∥ ≤ (l.map norm).Prod
| [] =>
  by 
    simp 
| a :: l => List.norm_prod_le' (List.cons_ne_nil a l)

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finset.norm_prod_le'
{α : Type*}
[normed_comm_ring α]
(s : finset ι)
(hs : s.nonempty)
(f : ι → α) : «expr ≤ »(«expr∥ ∥»(«expr∏ in , »((i), s, f i)), «expr∏ in , »((i), s, «expr∥ ∥»(f i))) :=
begin
  rcases [expr s, "with", "⟨", "⟨", ident l, "⟩", ",", ident hl, "⟩"],
  have [] [":", expr «expr ≠ »(l.map f, «expr[ , ]»([]))] [],
  by simpa [] [] [] [] [] ["using", expr hs],
  simpa [] [] [] [] [] ["using", expr list.norm_prod_le' this]
end

theorem Finset.norm_prod_le {α : Type _} [NormedCommRing α] [NormOneClass α] (s : Finset ι) (f : ι → α) :
  ∥∏i in s, f i∥ ≤ ∏i in s, ∥f i∥ :=
  by 
    rcases s with ⟨⟨l⟩, hl⟩
    simpa using (l.map f).norm_prod_le

/-- If `α` is a seminormed ring, then `∥a^n∥≤ ∥a∥^n` for `n > 0`. See also `norm_pow_le`. -/
theorem norm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ∥a ^ n∥ ≤ ∥a∥ ^ n
| 1, h =>
  by 
    simp 
| n+2, h =>
  by 
    rw [pow_succₓ _ (n+1), pow_succₓ _ (n+1)]
    exact
      le_transₓ (norm_mul_le a (a ^ n+1))
        (mul_le_mul (le_reflₓ _) (norm_pow_le' (Nat.succ_posₓ _)) (norm_nonneg _) (norm_nonneg _))

/-- If `α` is a seminormed ring with `∥1∥=1`, then `∥a^n∥≤ ∥a∥^n`. See also `norm_pow_le'`. -/
theorem norm_pow_le [NormOneClass α] (a : α) : ∀ (n : ℕ), ∥a ^ n∥ ≤ ∥a∥ ^ n
| 0 =>
  by 
    simp 
| n+1 => norm_pow_le' a n.zero_lt_succ

theorem eventually_norm_pow_le (a : α) : ∀ᶠn : ℕ in at_top, ∥a ^ n∥ ≤ ∥a∥ ^ n :=
  eventually_at_top.mpr ⟨1, fun b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩

/-- In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
theorem mul_left_bound (x : α) : ∀ (y : α), ∥AddMonoidHom.mulLeft x y∥ ≤ ∥x∥*∥y∥ :=
  norm_mul_le x

/-- In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
theorem mul_right_bound (x : α) : ∀ (y : α), ∥AddMonoidHom.mulRight x y∥ ≤ ∥x∥*∥y∥ :=
  fun y =>
    by 
      rw [mul_commₓ]
      convert norm_mul_le y x

/-- Seminormed ring structure on the product of two seminormed rings, using the sup norm. -/
instance Prod.semiNormedRing [SemiNormedRing β] : SemiNormedRing (α × β) :=
  { Prod.semiNormedGroup with
    norm_mul :=
      fun x y =>
        calc ∥x*y∥ = ∥(x.1*y.1, x.2*y.2)∥ := rfl 
          _ = max ∥x.1*y.1∥ ∥x.2*y.2∥ := rfl 
          _ ≤ max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥) := max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2)
          _ = max (∥x.1∥*∥y.1∥) (∥y.2∥*∥x.2∥) :=
          by 
            simp [mul_commₓ]
          _ ≤ max ∥x.1∥ ∥x.2∥*max ∥y.2∥ ∥y.1∥ :=
          by 
            apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
          _ = max ∥x.1∥ ∥x.2∥*max ∥y.1∥ ∥y.2∥ :=
          by 
            simp [max_commₓ]
          _ = ∥x∥*∥y∥ := rfl
           }

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def Matrix.semiNormedGroup {n m : Type _} [Fintype n] [Fintype m] : SemiNormedGroup (Matrix n m α) :=
  Pi.semiNormedGroup

attribute [local instance] Matrix.semiNormedGroup

theorem semi_norm_matrix_le_iff {n m : Type _} [Fintype n] [Fintype m] {r : ℝ} (hr : 0 ≤ r) {A : Matrix n m α} :
  ∥A∥ ≤ r ↔ ∀ i j, ∥A i j∥ ≤ r :=
  by 
    simp [pi_semi_norm_le_iff hr]

end SemiNormedRing

section NormedRing

variable[NormedRing α]

theorem Units.norm_pos [Nontrivial α] (x : Units α) : 0 < ∥(x : α)∥ :=
  norm_pos_iff.mpr (Units.ne_zero x)

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { Prod.semiNormedGroup with norm_mul := norm_mul_le }

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def Matrix.normedGroup {n m : Type _} [Fintype n] [Fintype m] : NormedGroup (Matrix n m α) :=
  Pi.normedGroup

end NormedRing

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance semi_normed_ring_top_monoid [semi_normed_ring α] : has_continuous_mul α :=
⟨«expr $ »(continuous_iff_continuous_at.2, λ
  x, «expr $ »(tendsto_iff_norm_tendsto_zero.2, begin
     have [] [":", expr ∀
      e : «expr × »(α, α), «expr ≤ »(«expr∥ ∥»(«expr - »(«expr * »(e.1, e.2), «expr * »(x.1, x.2))), «expr + »(«expr * »(«expr∥ ∥»(e.1), «expr∥ ∥»(«expr - »(e.2, x.2))), «expr * »(«expr∥ ∥»(«expr - »(e.1, x.1)), «expr∥ ∥»(x.2))))] [],
     { intro [ident e],
       calc
         «expr ≤ »(«expr∥ ∥»(«expr - »(«expr * »(e.1, e.2), «expr * »(x.1, x.2))), «expr∥ ∥»(«expr + »(«expr * »(e.1, «expr - »(e.2, x.2)), «expr * »(«expr - »(e.1, x.1), x.2)))) : by rw ["[", expr mul_sub, ",", expr sub_mul, ",", expr sub_add_sub_cancel, "]"] []
         «expr ≤ »(..., «expr + »(«expr * »(«expr∥ ∥»(e.1), «expr∥ ∥»(«expr - »(e.2, x.2))), «expr * »(«expr∥ ∥»(«expr - »(e.1, x.1)), «expr∥ ∥»(x.2)))) : norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _) },
     refine [expr squeeze_zero (λ e, norm_nonneg _) this _],
     convert [] [expr ((continuous_fst.tendsto x).norm.mul ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)] [],
     show [expr tendsto _ _ _],
     from [expr tendsto_const_nhds],
     simp [] [] [] [] [] []
   end))⟩

/-- A seminormed ring is a topological ring. -/
instance (priority := 100)semi_normed_top_ring [SemiNormedRing α] : TopologicalRing α :=
  {  }

/-- A normed field is a field with a norm satisfying ∥x y∥ = ∥x∥ ∥y∥. -/
class NormedField(α : Type _) extends HasNorm α, Field α, MetricSpace α where 
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a*b) = norm a*norm b

/-- A nondiscrete normed field is a normed field in which there is an element of norm different from
`0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by multiplication
by the powers of any element, and thus to relate algebra and topology. -/
class NondiscreteNormedField(α : Type _) extends NormedField α where 
  non_trivial : ∃ x : α, 1 < ∥x∥

namespace NormedField

section NormedField

variable[NormedField α]

@[simp]
theorem norm_mul (a b : α) : ∥a*b∥ = ∥a∥*∥b∥ :=
  NormedField.norm_mul' a b

instance (priority := 100)to_normed_comm_ring : NormedCommRing α :=
  { ‹NormedField α› with norm_mul := fun a b => (norm_mul a b).le }

instance (priority := 900)to_norm_one_class : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (@one_ne_zero α _ _))$
      by 
        rw [←norm_mul, mul_oneₓ, mul_oneₓ]⟩

@[simp]
theorem nnnorm_mul (a b : α) : ∥a*b∥₊ = ∥a∥₊*∥b∥₊ :=
  Nnreal.eq$ norm_mul a b

/-- `norm` as a `monoid_hom`. -/
@[simps]
def norm_hom : MonoidWithZeroHom α ℝ :=
  ⟨norm, norm_zero, norm_one, norm_mul⟩

/-- `nnnorm` as a `monoid_hom`. -/
@[simps]
def nnnorm_hom : MonoidWithZeroHom α ℝ≥0  :=
  ⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩

@[simp]
theorem norm_pow (a : α) : ∀ (n : ℕ), ∥a ^ n∥ = ∥a∥ ^ n :=
  (norm_hom.toMonoidHom : α →* ℝ).map_pow a

@[simp]
theorem nnnorm_pow (a : α) (n : ℕ) : ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
  (nnnorm_hom.toMonoidHom : α →*  ℝ≥0 ).map_pow a n

@[simp]
theorem norm_prod (s : Finset β) (f : β → α) : ∥∏b in s, f b∥ = ∏b in s, ∥f b∥ :=
  (norm_hom.toMonoidHom : α →* ℝ).map_prod f s

@[simp]
theorem nnnorm_prod (s : Finset β) (f : β → α) : ∥∏b in s, f b∥₊ = ∏b in s, ∥f b∥₊ :=
  (nnnorm_hom.toMonoidHom : α →*  ℝ≥0 ).map_prod f s

@[simp]
theorem norm_div (a b : α) : ∥a / b∥ = ∥a∥ / ∥b∥ :=
  (norm_hom : MonoidWithZeroHom α ℝ).map_div a b

@[simp]
theorem nnnorm_div (a b : α) : ∥a / b∥₊ = ∥a∥₊ / ∥b∥₊ :=
  (nnnorm_hom : MonoidWithZeroHom α ℝ≥0 ).map_div a b

@[simp]
theorem norm_inv (a : α) : ∥a⁻¹∥ = ∥a∥⁻¹ :=
  (norm_hom : MonoidWithZeroHom α ℝ).map_inv a

@[simp]
theorem nnnorm_inv (a : α) : ∥a⁻¹∥₊ = ∥a∥₊⁻¹ :=
  Nnreal.eq$
    by 
      simp 

@[simp]
theorem norm_zpow : ∀ (a : α) (n : ℤ), ∥a ^ n∥ = ∥a∥ ^ n :=
  (norm_hom : MonoidWithZeroHom α ℝ).map_zpow

@[simp]
theorem nnnorm_zpow : ∀ (a : α) (n : ℤ), ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
  (nnnorm_hom : MonoidWithZeroHom α ℝ≥0 ).map_zpow

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance : has_continuous_inv₀ α :=
begin
  refine [expr ⟨λ r r0, tendsto_iff_norm_tendsto_zero.2 _⟩],
  have [ident r0'] [":", expr «expr < »(0, «expr∥ ∥»(r))] [":=", expr norm_pos_iff.2 r0],
  rcases [expr exists_between r0', "with", "⟨", ident ε, ",", ident ε0, ",", ident εr, "⟩"],
  have [] [":", expr «expr∀ᶠ in , »((e), expr𝓝() r, «expr ≤ »(«expr∥ ∥»(«expr - »(«expr ⁻¹»(e), «expr ⁻¹»(r))), «expr / »(«expr / »(«expr∥ ∥»(«expr - »(r, e)), «expr∥ ∥»(r)), ε)))] [],
  { filter_upwards ["[", expr (is_open_lt continuous_const continuous_norm).eventually_mem εr, "]"] [],
    intros [ident e, ident he],
    have [ident e0] [":", expr «expr ≠ »(e, 0)] [":=", expr norm_pos_iff.1 (ε0.trans he)],
    calc
      «expr = »(«expr∥ ∥»(«expr - »(«expr ⁻¹»(e), «expr ⁻¹»(r))), «expr / »(«expr / »(«expr∥ ∥»(«expr - »(r, e)), «expr∥ ∥»(r)), «expr∥ ∥»(e))) : by field_simp [] ["[", expr mul_comm, "]"] [] []
      «expr ≤ »(..., «expr / »(«expr / »(«expr∥ ∥»(«expr - »(r, e)), «expr∥ ∥»(r)), ε)) : div_le_div_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) ε0 he.le },
  refine [expr squeeze_zero' «expr $ »(eventually_of_forall, λ _, norm_nonneg _) this _],
  refine [expr (continuous_const.sub continuous_id).norm.div_const.div_const.tendsto' _ _ _],
  simp [] [] [] [] [] []
end

end NormedField

variable(α)[NondiscreteNormedField α]

theorem exists_one_lt_norm : ∃ x : α, 1 < ∥x∥ :=
  ‹NondiscreteNormedField α›.non_trivial

theorem exists_norm_lt_one : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < 1 :=
  by 
    rcases exists_one_lt_norm α with ⟨y, hy⟩
    refine' ⟨y⁻¹, _, _⟩
    ·
      simp only [inv_eq_zero, Ne.def, norm_pos_iff]
      rintro rfl 
      rw [norm_zero] at hy 
      exact lt_asymmₓ zero_lt_one hy
    ·
      simp [inv_lt_one hy]

theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ∥x∥ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α 
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n,
    by 
      rwa [norm_pow]⟩

theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < r :=
  let ⟨w, hw⟩ := exists_one_lt_norm α 
  let ⟨n, hle, hlt⟩ := exists_mem_Ioc_zpow hr hw
  ⟨w ^ n,
    by 
      rw [norm_zpow] <;> exact zpow_pos_of_pos (lt_transₓ zero_lt_one hw) _,
    by 
      rwa [norm_zpow]⟩

variable{α}

@[instance]
theorem punctured_nhds_ne_bot (x : α) : ne_bot (𝓝[«expr ᶜ» {x}] x) :=
  by 
    rw [←mem_closure_iff_nhds_within_ne_bot, Metric.mem_closure_iff]
    rintro ε ε0 
    rcases NormedField.exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
    refine' ⟨x+b, mt (set.mem_singleton_iff.trans add_right_eq_selfₓ).1$ norm_pos_iff.1 hb0, _⟩
    rwa [dist_comm, dist_eq_norm, add_sub_cancel']

@[instance]
theorem nhds_within_is_unit_ne_bot : ne_bot (𝓝[{ x:α | IsUnit x }] 0) :=
  by 
    simpa only [is_unit_iff_ne_zero] using punctured_nhds_ne_bot (0 : α)

end NormedField

instance  : NormedField ℝ :=
  { Real.normedGroup with norm_mul' := abs_mul }

instance  : NondiscreteNormedField ℝ :=
  { non_trivial :=
      ⟨2,
        by 
          unfold norm 
          rw [abs_of_nonneg] <;> normNum⟩ }

namespace Real

theorem norm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥ = x :=
  abs_of_nonneg hx

theorem norm_of_nonpos {x : ℝ} (hx : x ≤ 0) : ∥x∥ = -x :=
  abs_of_nonpos hx

@[simp]
theorem norm_coe_nat (n : ℕ) : ∥(n : ℝ)∥ = n :=
  abs_of_nonneg n.cast_nonneg

@[simp]
theorem nnnorm_coe_nat (n : ℕ) : ∥(n : ℝ)∥₊ = n :=
  Nnreal.eq$
    by 
      simp 

@[simp]
theorem norm_two : ∥(2 : ℝ)∥ = 2 :=
  abs_of_pos (@zero_lt_two ℝ _ _)

@[simp]
theorem nnnorm_two : ∥(2 : ℝ)∥₊ = 2 :=
  Nnreal.eq$
    by 
      simp 

theorem nnnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥₊ = ⟨x, hx⟩ :=
  Nnreal.eq$ norm_of_nonneg hx

theorem ennnorm_eq_of_real {x : ℝ} (hx : 0 ≤ x) : (∥x∥₊ : ℝ≥0∞) = Ennreal.ofReal x :=
  by 
    rw [←of_real_norm_eq_coe_nnnorm, norm_of_nonneg hx]

theorem of_real_le_ennnorm (x : ℝ) : Ennreal.ofReal x ≤ ∥x∥₊ :=
  by 
    byCases' hx : 0 ≤ x
    ·
      rw [Real.ennnorm_eq_of_real hx]
      rfl'
    ·
      rw [Ennreal.of_real_eq_zero.2 (le_of_ltₓ (not_leₓ.1 hx))]
      exact bot_le

/-- If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `module.punctured_nhds_ne_bot`. -/
instance punctured_nhds_module_ne_bot {E : Type _} [AddCommGroupₓ E] [TopologicalSpace E] [HasContinuousAdd E]
  [Nontrivial E] [Module ℝ E] [HasContinuousSmul ℝ E] (x : E) : ne_bot (𝓝[«expr ᶜ» {x}] x) :=
  Module.punctured_nhds_ne_bot ℝ E x

end Real

namespace Nnreal

open_locale Nnreal

@[simp]
theorem norm_eq (x :  ℝ≥0 ) : ∥(x : ℝ)∥ = x :=
  by 
    rw [Real.norm_eq_abs, x.abs_eq]

@[simp]
theorem nnnorm_eq (x :  ℝ≥0 ) : ∥(x : ℝ)∥₊ = x :=
  Nnreal.eq$ Real.norm_of_nonneg x.2

end Nnreal

@[simp]
theorem norm_norm [SemiNormedGroup α] (x : α) : ∥∥x∥∥ = ∥x∥ :=
  Real.norm_of_nonneg (norm_nonneg _)

@[simp]
theorem nnnorm_norm [SemiNormedGroup α] (a : α) : ∥∥a∥∥₊ = ∥a∥₊ :=
  by 
    simpa [Real.nnnorm_of_nonneg (norm_nonneg a)]

/-- A restatement of `metric_space.tendsto_at_top` in terms of the norm. -/
theorem NormedGroup.tendsto_at_top [Nonempty α] [SemilatticeSup α] {β : Type _} [SemiNormedGroup β] {f : α → β}
  {b : β} : tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ∥f n - b∥ < ε :=
  (at_top_basis.tendsto_iff Metric.nhds_basis_ball).trans
    (by 
      simp [dist_eq_norm])

/--
A variant of `normed_group.tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedGroup.tendsto_at_top' [Nonempty α] [SemilatticeSup α] [NoTopOrder α] {β : Type _} [SemiNormedGroup β]
  {f : α → β} {b : β} : tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ∥f n - b∥ < ε :=
  (at_top_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans
    (by 
      simp [dist_eq_norm])

instance  : NormedCommRing ℤ :=
  { norm := fun n => ∥(n : ℝ)∥,
    norm_mul :=
      fun m n =>
        le_of_eqₓ$
          by 
            simp only [norm, Int.cast_mul, abs_mul],
    dist_eq :=
      fun m n =>
        by 
          simp only [Int.dist_eq, norm, Int.cast_sub],
    mul_comm := mul_commₓ }

@[normCast]
theorem Int.norm_cast_real (m : ℤ) : ∥(m : ℝ)∥ = ∥m∥ :=
  rfl

theorem Int.norm_eq_abs (n : ℤ) : ∥n∥ = |n| :=
  rfl

theorem Nnreal.coe_nat_abs (n : ℤ) : (n.nat_abs :  ℝ≥0 ) = ∥n∥₊ :=
  Nnreal.eq$
    calc ((n.nat_abs :  ℝ≥0 ) : ℝ) = (n.nat_abs : ℤ) :=
      by 
        simp only [Int.cast_coe_nat, Nnreal.coe_nat_cast]
      _ = |n| :=
      by 
        simp only [←Int.abs_eq_nat_abs, Int.cast_abs]
      _ = ∥n∥ := rfl
      

instance  : NormOneClass ℤ :=
  ⟨by 
      simp [←Int.norm_cast_real]⟩

instance  : NormedField ℚ :=
  { norm := fun r => ∥(r : ℝ)∥,
    norm_mul' :=
      fun r₁ r₂ =>
        by 
          simp only [norm, Rat.cast_mul, abs_mul],
    dist_eq :=
      fun r₁ r₂ =>
        by 
          simp only [Rat.dist_eq, norm, Rat.cast_sub] }

instance  : NondiscreteNormedField ℚ :=
  { non_trivial :=
      ⟨2,
        by 
          unfold norm 
          rw [abs_of_nonneg] <;> normNum⟩ }

@[normCast, simp]
theorem Rat.norm_cast_real (r : ℚ) : ∥(r : ℝ)∥ = ∥r∥ :=
  rfl

@[normCast, simp]
theorem Int.norm_cast_rat (m : ℤ) : ∥(m : ℚ)∥ = ∥m∥ :=
  by 
    rw [←Rat.norm_cast_real, ←Int.norm_cast_real] <;> congr 1 <;> normCast

section 

variable[SemiNormedGroup α]

theorem norm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥ ≤ n*∥a∥ :=
  by 
    induction' n with n ih
    ·
      simp only [norm_zero, Nat.cast_zero, zero_mul, zero_smul]
    simp only [Nat.succ_eq_add_one, add_smul, add_mulₓ, one_mulₓ, Nat.cast_add, Nat.cast_one, one_nsmul]
    exact norm_add_le_of_le ih le_rfl

theorem norm_zsmul_le (n : ℤ) (a : α) : ∥n • a∥ ≤ ∥n∥*∥a∥ :=
  by 
    induction' n with n n
    ·
      simp only [Int.of_nat_eq_coe, coe_nat_zsmul]
      convert norm_nsmul_le n a 
      exact Nat.abs_cast n
    ·
      simp only [Int.neg_succ_of_nat_coe, neg_smul, norm_neg, coe_nat_zsmul]
      convert norm_nsmul_le n.succ a 
      exact Nat.abs_cast n.succ

theorem nnnorm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥₊ ≤ n*∥a∥₊ :=
  by 
    simpa only [←Nnreal.coe_le_coe, Nnreal.coe_mul, Nnreal.coe_nat_cast] using norm_nsmul_le n a

theorem nnnorm_zsmul_le (n : ℤ) (a : α) : ∥n • a∥₊ ≤ ∥n∥₊*∥a∥₊ :=
  by 
    simpa only [←Nnreal.coe_le_coe, Nnreal.coe_mul] using norm_zsmul_le n a

end 

section SemiNormedSpace

section Prio

set_option extends_priority 920

/-- A seminormed space over a normed field is a vector space endowed with a seminorm which satisfies
the equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class SemiNormedSpace(α : Type _)(β : Type _)[NormedField α][SemiNormedGroup β] extends Module α β where 
  norm_smul_le : ∀ (a : α) (b : β), ∥a • b∥ ≤ ∥a∥*∥b∥

set_option extends_priority 920

/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class NormedSpace(α : Type _)(β : Type _)[NormedField α][NormedGroup β] extends Module α β where 
  norm_smul_le : ∀ (a : α) (b : β), ∥a • b∥ ≤ ∥a∥*∥b∥

/-- A normed space is a seminormed space. -/
instance (priority := 100)NormedSpace.toSemiNormedSpace [NormedField α] [NormedGroup β] [γ : NormedSpace α β] :
  SemiNormedSpace α β :=
  { γ with  }

end Prio

variable[NormedField α][SemiNormedGroup β]

instance (priority := 100)SemiNormedSpace.has_bounded_smul [SemiNormedSpace α β] : HasBoundedSmul α β :=
  { dist_smul_pair' :=
      fun x y₁ y₂ =>
        by 
          simpa [dist_eq_norm, smul_sub] using SemiNormedSpace.norm_smul_le x (y₁ - y₂),
    dist_pair_smul' :=
      fun x₁ x₂ y =>
        by 
          simpa [dist_eq_norm, sub_smul] using SemiNormedSpace.norm_smul_le (x₁ - x₂) y }

instance NormedField.toNormedSpace : NormedSpace α α :=
  { norm_smul_le := fun a b => le_of_eqₓ (NormedField.norm_mul a b) }

theorem norm_smul [SemiNormedSpace α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥*∥x∥ :=
  by 
    byCases' h : s = 0
    ·
      simp [h]
    ·
      refine' le_antisymmₓ (SemiNormedSpace.norm_smul_le s x) _ 
      calc (∥s∥*∥x∥) = ∥s∥*∥s⁻¹ • s • x∥ :=
        by 
          rw [inv_smul_smul₀ h]_ ≤ ∥s∥*∥s⁻¹∥*∥s • x∥ :=
        mul_le_mul_of_nonneg_left (SemiNormedSpace.norm_smul_le _ _) (norm_nonneg _)_ = ∥s • x∥ :=
        by 
          rw [NormedField.norm_inv, ←mul_assocₓ, mul_inv_cancel (mt norm_eq_zero.1 h), one_mulₓ]

@[simp]
theorem abs_norm_eq_norm (z : β) : |∥z∥| = ∥z∥ :=
  (abs_eq (norm_nonneg z)).mpr (Or.inl rfl)

theorem dist_smul [SemiNormedSpace α β] (s : α) (x y : β) : dist (s • x) (s • y) = ∥s∥*dist x y :=
  by 
    simp only [dist_eq_norm, (norm_smul _ _).symm, smul_sub]

theorem nnnorm_smul [SemiNormedSpace α β] (s : α) (x : β) : ∥s • x∥₊ = ∥s∥₊*∥x∥₊ :=
  Nnreal.eq$ norm_smul s x

theorem nndist_smul [SemiNormedSpace α β] (s : α) (x y : β) : nndist (s • x) (s • y) = ∥s∥₊*nndist x y :=
  Nnreal.eq$ dist_smul s x y

theorem norm_smul_of_nonneg [SemiNormedSpace ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) : ∥t • x∥ = t*∥x∥ :=
  by 
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

variable{E : Type _}[SemiNormedGroup E][SemiNormedSpace α E]

variable{F : Type _}[SemiNormedGroup F][SemiNormedSpace α F]

theorem eventually_nhds_norm_smul_sub_lt (c : α) (x : E) {ε : ℝ} (h : 0 < ε) : ∀ᶠy in 𝓝 x, ∥c • (y - x)∥ < ε :=
  have  : tendsto (fun y => ∥c • (y - x)∥) (𝓝 x) (𝓝 0) :=
    (continuous_const.smul (continuous_id.sub continuous_const)).norm.tendsto' _ _
      (by 
        simp )
  this.eventually (gt_mem_nhds h)

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem closure_ball
[semi_normed_space exprℝ() E]
(x : E)
{r : exprℝ()}
(hr : «expr < »(0, r)) : «expr = »(closure (ball x r), closed_ball x r) :=
begin
  refine [expr set.subset.antisymm closure_ball_subset_closed_ball (λ y hy, _)],
  have [] [":", expr continuous_within_at (λ
    c : exprℝ(), «expr + »(«expr • »(c, «expr - »(y, x)), x)) (set.Ico 0 1) 1] [":=", expr ((continuous_id.smul continuous_const).add continuous_const).continuous_within_at],
  convert [] [expr this.mem_closure _ _] [],
  { rw ["[", expr one_smul, ",", expr sub_add_cancel, "]"] [] },
  { simp [] [] [] ["[", expr closure_Ico (@zero_lt_one exprℝ() _ _), ",", expr zero_le_one, "]"] [] [] },
  { rintros [ident c, "⟨", ident hc0, ",", ident hc1, "⟩"],
    rw ["[", expr set.mem_preimage, ",", expr mem_ball, ",", expr dist_eq_norm, ",", expr add_sub_cancel, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg hc0, ",", expr mul_comm, ",", "<-", expr mul_one r, "]"] [],
    rw ["[", expr mem_closed_ball, ",", expr dist_eq_norm, "]"] ["at", ident hy],
    apply [expr mul_lt_mul']; assumption }
end

theorem frontier_ball [SemiNormedSpace ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : Frontier (ball x r) = sphere x r :=
  by 
    rw [Frontier, closure_ball x hr, is_open_ball.interior_eq]
    ext x 
    exact (@eq_iff_le_not_lt ℝ _ _ _).symm

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem interior_closed_ball
[semi_normed_space exprℝ() E]
(x : E)
{r : exprℝ()}
(hr : «expr < »(0, r)) : «expr = »(interior (closed_ball x r), ball x r) :=
begin
  refine [expr set.subset.antisymm _ ball_subset_interior_closed_ball],
  intros [ident y, ident hy],
  rcases [expr le_iff_lt_or_eq.1 «expr $ »(mem_closed_ball.1, interior_subset hy), "with", ident hr, "|", ident rfl],
  { exact [expr hr] },
  set [] [ident f] [":", expr exprℝ() → E] [":="] [expr λ c : exprℝ(), «expr + »(«expr • »(c, «expr - »(y, x)), x)] [],
  suffices [] [":", expr «expr ⊆ »(«expr ⁻¹' »(f, closed_ball x (dist y x)), set.Icc «expr- »(1) 1)],
  { have [ident hfc] [":", expr continuous f] [":=", expr (continuous_id.smul continuous_const).add continuous_const],
    have [ident hf1] [":", expr «expr ∈ »((1 : exprℝ()), «expr ⁻¹' »(f, interior «expr $ »(closed_ball x, dist y x)))] [],
    by simpa [] [] [] ["[", expr f, "]"] [] [],
    have [ident h1] [":", expr «expr ∈ »((1 : exprℝ()), interior (set.Icc («expr- »(1) : exprℝ()) 1))] [":=", expr interior_mono this (preimage_interior_subset_interior_preimage hfc hf1)],
    contrapose [] [ident h1],
    simp [] [] [] [] [] [] },
  intros [ident c, ident hc],
  rw ["[", expr set.mem_Icc, ",", "<-", expr abs_le, ",", "<-", expr real.norm_eq_abs, ",", "<-", expr mul_le_mul_right hr, "]"] [],
  simpa [] [] [] ["[", expr f, ",", expr dist_eq_norm, ",", expr norm_smul, "]"] [] ["using", expr hc]
end

theorem frontier_closed_ball [SemiNormedSpace ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  Frontier (closed_ball x r) = sphere x r :=
  by 
    rw [Frontier, closure_closed_ball, interior_closed_ball x hr, closed_ball_diff_ball]

theorem smul_ball {c : α} (hc : c ≠ 0) (x : E) (r : ℝ) : c • ball x r = ball (c • x) (∥c∥*r) :=
  by 
    ext y 
    rw [mem_smul_set_iff_inv_smul_mem₀ hc]
    convLHS => rw [←inv_smul_smul₀ hc x]
    simp [←div_eq_inv_mul, div_lt_iff (norm_pos_iff.2 hc), mul_commₓ _ r, dist_smul]

theorem smul_closed_ball' {c : α} (hc : c ≠ 0) (x : E) (r : ℝ) : c • closed_ball x r = closed_ball (c • x) (∥c∥*r) :=
  by 
    ext y 
    rw [mem_smul_set_iff_inv_smul_mem₀ hc]
    convLHS => rw [←inv_smul_smul₀ hc x]
    simp [dist_smul, ←div_eq_inv_mul, div_le_iff (norm_pos_iff.2 hc), mul_commₓ _ r]

theorem smul_closed_ball {E : Type _} [NormedGroup E] [NormedSpace α E] (c : α) (x : E) {r : ℝ} (hr : 0 ≤ r) :
  c • closed_ball x r = closed_ball (c • x) (∥c∥*r) :=
  by 
    rcases eq_or_ne c 0 with (rfl | hc)
    ·
      simp [hr, zero_smul_set, Set.singleton_zero, ←nonempty_closed_ball]
    ·
      exact smul_closed_ball' hc x r

variable(α)

theorem ne_neg_of_mem_sphere [CharZero α] {r : ℝ} (hr : 0 < r) (x : sphere (0 : E) r) : x ≠ -x :=
  fun h =>
    nonzero_of_mem_sphere hr x
      (eq_zero_of_eq_neg α
        (by 
          convLHS => rw [h]
          simp ))

theorem ne_neg_of_mem_unit_sphere [CharZero α] (x : sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere α
    (by 
      normNum)
    x

variable{α}

open NormedField

/-- The product of two seminormed spaces is a seminormed space, with the sup norm. -/
instance Prod.semiNormedSpace : SemiNormedSpace α (E × F) :=
  { Prod.normedGroup, Prod.module with
    norm_smul_le :=
      fun s x =>
        le_of_eqₓ$
          by 
            simp [Prod.semi_norm_def, norm_smul, mul_max_of_nonneg] }

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The product of finitely many seminormed spaces is a seminormed space, with the sup norm. -/
instance pi.semi_normed_space
{E : ι → Type*}
[fintype ι]
[∀ i, semi_normed_group (E i)]
[∀ i, semi_normed_space α (E i)] : semi_normed_space α (∀ i, E i) :=
{ norm_smul_le := λ
  a
  f, «expr $ »(le_of_eq, show «expr = »((«expr↑ »(finset.sup finset.univ (λ
      b : ι, «expr∥ ∥₊»(«expr • »(a, f b)))) : exprℝ()), «expr * »(«expr∥ ∥₊»(a), «expr↑ »(finset.sup finset.univ (λ
       b : ι, «expr∥ ∥₊»(f b))))), by simp [] [] ["only"] ["[", expr (nnreal.coe_mul _ _).symm, ",", expr nnreal.mul_finset_sup, ",", expr nnnorm_smul, "]"] [] []) }

/-- A subspace of a seminormed space is also a normed space, with the restriction of the norm. -/
instance Submodule.semiNormedSpace {𝕜 R : Type _} [HasScalar 𝕜 R] [NormedField 𝕜] [Ringₓ R] {E : Type _}
  [SemiNormedGroup E] [SemiNormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E] (s : Submodule R E) :
  SemiNormedSpace 𝕜 s :=
  { norm_smul_le := fun c x => le_of_eqₓ$ norm_smul c (x : E) }

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If there is a scalar `c` with `∥c∥>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `∥c∥`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
theorem rescale_to_shell_semi_normed
{c : α}
(hc : «expr < »(1, «expr∥ ∥»(c)))
{ε : exprℝ()}
(εpos : «expr < »(0, ε))
{x : E}
(hx : «expr ≠ »(«expr∥ ∥»(x), 0)) : «expr∃ , »((d : α), «expr ∧ »(«expr ≠ »(d, 0), «expr ∧ »(«expr < »(«expr∥ ∥»(«expr • »(d, x)), ε), «expr ∧ »(«expr ≤ »(«expr / »(ε, «expr∥ ∥»(c)), «expr∥ ∥»(«expr • »(d, x))), «expr ≤ »(«expr ⁻¹»(«expr∥ ∥»(d)), «expr * »(«expr * »(«expr ⁻¹»(ε), «expr∥ ∥»(c)), «expr∥ ∥»(x))))))) :=
begin
  have [ident xεpos] [":", expr «expr < »(0, «expr / »(«expr∥ ∥»(x), ε))] [":=", expr div_pos ((ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos],
  rcases [expr exists_mem_Ico_zpow xεpos hc, "with", "⟨", ident n, ",", ident hn, "⟩"],
  have [ident cpos] [":", expr «expr < »(0, «expr∥ ∥»(c))] [":=", expr lt_trans (zero_lt_one : «expr < »((0 : exprℝ()), 1)) hc],
  have [ident cnpos] [":", expr «expr < »(0, «expr∥ ∥»(«expr ^ »(c, «expr + »(n, 1))))] [":=", expr by { rw [expr norm_zpow] [],
     exact [expr lt_trans xεpos hn.2] }],
  refine [expr ⟨«expr ⁻¹»(«expr ^ »(c, «expr + »(n, 1))), _, _, _, _⟩],
  show [expr «expr ≠ »(«expr ⁻¹»(«expr ^ »(c, «expr + »(n, 1))), 0)],
  by rwa ["[", expr ne.def, ",", expr inv_eq_zero, ",", "<-", expr ne.def, ",", "<-", expr norm_pos_iff, "]"] [],
  show [expr «expr < »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr ^ »(c, «expr + »(n, 1))), x)), ε)],
  { rw ["[", expr norm_smul, ",", expr norm_inv, ",", "<-", expr div_eq_inv_mul, ",", expr div_lt_iff cnpos, ",", expr mul_comm, ",", expr norm_zpow, "]"] [],
    exact [expr (div_lt_iff εpos).1 hn.2] },
  show [expr «expr ≤ »(«expr / »(ε, «expr∥ ∥»(c)), «expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr ^ »(c, «expr + »(n, 1))), x)))],
  { rw ["[", expr div_le_iff cpos, ",", expr norm_smul, ",", expr norm_inv, ",", expr norm_zpow, ",", expr zpow_add₀ (ne_of_gt cpos), ",", expr zpow_one, ",", expr mul_inv_rev₀, ",", expr mul_comm, ",", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, ",", expr mul_inv_cancel (ne_of_gt cpos), ",", expr one_mul, ",", "<-", expr div_eq_inv_mul, ",", expr le_div_iff (zpow_pos_of_pos cpos _), ",", expr mul_comm, "]"] [],
    exact [expr (le_div_iff εpos).1 hn.1] },
  show [expr «expr ≤ »(«expr ⁻¹»(«expr∥ ∥»(«expr ⁻¹»(«expr ^ »(c, «expr + »(n, 1))))), «expr * »(«expr * »(«expr ⁻¹»(ε), «expr∥ ∥»(c)), «expr∥ ∥»(x)))],
  { have [] [":", expr «expr = »(«expr * »(«expr * »(«expr ⁻¹»(ε), «expr∥ ∥»(c)), «expr∥ ∥»(x)), «expr * »(«expr * »(«expr ⁻¹»(ε), «expr∥ ∥»(x)), «expr∥ ∥»(c)))] [],
    by ring [],
    rw ["[", expr norm_inv, ",", expr inv_inv₀, ",", expr norm_zpow, ",", expr zpow_add₀ (ne_of_gt cpos), ",", expr zpow_one, ",", expr this, ",", "<-", expr div_eq_inv_mul, "]"] [],
    exact [expr mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _)] }
end

end SemiNormedSpace

section NormedSpace

variable[NormedField α]

variable{E : Type _}[NormedGroup E][NormedSpace α E]

variable{F : Type _}[NormedGroup F][NormedSpace α F]

open NormedField

theorem interior_closed_ball' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
  Interior (closed_ball x r) = ball x r :=
  by 
    rcases lt_trichotomyₓ r 0 with (hr | rfl | hr)
    ·
      simp [closed_ball_eq_empty.2 hr, ball_eq_empty.2 hr.le]
    ·
      rw [closed_ball_zero, ball_zero, interior_singleton]
    ·
      exact interior_closed_ball x hr

theorem frontier_closed_ball' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
  Frontier (closed_ball x r) = sphere x r :=
  by 
    rw [Frontier, closure_closed_ball, interior_closed_ball' x r, closed_ball_diff_ball]

variable{α}

/-- If there is a scalar `c` with `∥c∥>1`, then any element can be moved by scalar multiplication to
any shell of width `∥c∥`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
theorem rescale_to_shell {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
  ∃ d : α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ ε / ∥c∥ ≤ ∥d • x∥ ∧ ∥d∥⁻¹ ≤ (ε⁻¹*∥c∥)*∥x∥ :=
  rescale_to_shell_semi_normed hc εpos (ne_of_ltₓ (norm_pos_iff.2 hx)).symm

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance  : NormedSpace α (E × F) :=
  { Prod.semiNormedSpace with  }

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance Pi.normedSpace {E : ι → Type _} [Fintype ι] [∀ i, NormedGroup (E i)] [∀ i, NormedSpace α (E i)] :
  NormedSpace α (∀ i, E i) :=
  { Pi.semiNormedSpace with  }

section 

attribute [local instance] Matrix.normedGroup

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed field.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def Matrix.normedSpace {α : Type _} [NormedField α] {n m : Type _} [Fintype n] [Fintype m] :
  NormedSpace α (Matrix n m α) :=
  Pi.normedSpace

end 

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance Submodule.normedSpace {𝕜 R : Type _} [HasScalar 𝕜 R] [NormedField 𝕜] [Ringₓ R] {E : Type _} [NormedGroup E]
  [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E] (s : Submodule R E) : NormedSpace 𝕜 s :=
  { Submodule.semiNormedSpace s with  }

end NormedSpace

section NormedAlgebra

/-- A seminormed algebra `𝕜'` over `𝕜` is an algebra endowed with a seminorm for which the
embedding of `𝕜` in `𝕜'` is an isometry. -/
class SemiNormedAlgebra(𝕜 : Type _)(𝕜' : Type _)[NormedField 𝕜][SemiNormedRing 𝕜'] extends Algebra 𝕜 𝕜' where 
  norm_algebra_map_eq : ∀ (x : 𝕜), ∥algebraMap 𝕜 𝕜' x∥ = ∥x∥

/-- A normed algebra `𝕜'` over `𝕜` is an algebra endowed with a norm for which the embedding of
`𝕜` in `𝕜'` is an isometry. -/
class NormedAlgebra(𝕜 : Type _)(𝕜' : Type _)[NormedField 𝕜][NormedRing 𝕜'] extends Algebra 𝕜 𝕜' where 
  norm_algebra_map_eq : ∀ (x : 𝕜), ∥algebraMap 𝕜 𝕜' x∥ = ∥x∥

/-- A normed algebra is a seminormed algebra. -/
instance (priority := 100)NormedAlgebra.toSemiNormedAlgebra (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [NormedRing 𝕜']
  [NormedAlgebra 𝕜 𝕜'] : SemiNormedAlgebra 𝕜 𝕜' :=
  { norm_algebra_map_eq := NormedAlgebra.norm_algebra_map_eq }

@[simp]
theorem norm_algebra_map_eq {𝕜 : Type _} (𝕜' : Type _) [NormedField 𝕜] [SemiNormedRing 𝕜'] [h : SemiNormedAlgebra 𝕜 𝕜']
  (x : 𝕜) : ∥algebraMap 𝕜 𝕜' x∥ = ∥x∥ :=
  SemiNormedAlgebra.norm_algebra_map_eq _

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
theorem algebra_map_isometry (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [SemiNormedRing 𝕜'] [SemiNormedAlgebra 𝕜 𝕜'] :
  Isometry (algebraMap 𝕜 𝕜') :=
  by 
    refine' isometry_emetric_iff_metric.2 fun x y => _ 
    rw [dist_eq_norm, dist_eq_norm, ←RingHom.map_sub, norm_algebra_map_eq]

variable(𝕜 : Type _)[NormedField 𝕜]

variable(𝕜' : Type _)[SemiNormedRing 𝕜']

instance (priority := 100)SemiNormedAlgebra.toSemiNormedSpace [h : SemiNormedAlgebra 𝕜 𝕜'] : SemiNormedSpace 𝕜 𝕜' :=
  { h with
    norm_smul_le :=
      fun s x =>
        calc ∥s • x∥ = ∥(algebraMap 𝕜 𝕜') s*x∥ :=
          by 
            rw [h.smul_def']
            rfl 
          _ ≤ ∥algebraMap 𝕜 𝕜' s∥*∥x∥ := SemiNormedRing.norm_mul _ _ 
          _ = ∥s∥*∥x∥ :=
          by 
            rw [norm_algebra_map_eq]
           }

/-- While this may appear identical to `semi_normed_algebra.to_semi_normed_space`, it contains an
implicit argument involving `normed_ring.to_semi_normed_ring` that typeclass inference has trouble
inferring.

Specifically, the following instance cannot be found without this
`semi_normed_algebra.to_semi_normed_space'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_ring (E i)] [Π i, normed_algebra 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

See `semi_normed_space.to_module'` for a similar situation. -/
instance (priority := 100)SemiNormedAlgebra.toSemiNormedSpace' (𝕜 : Type _) [NormedField 𝕜] (𝕜' : Type _)
  [NormedRing 𝕜'] [SemiNormedAlgebra 𝕜 𝕜'] : SemiNormedSpace 𝕜 𝕜' :=
  by 
    infer_instance

instance (priority := 100)NormedAlgebra.toNormedSpace (𝕜 : Type _) [NormedField 𝕜] (𝕜' : Type _) [NormedRing 𝕜']
  [h : NormedAlgebra 𝕜 𝕜'] : NormedSpace 𝕜 𝕜' :=
  { h with norm_smul_le := SemiNormedSpace.norm_smul_le }

instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { Algebra.id 𝕜 with
    norm_algebra_map_eq :=
      by 
        simp  }

variable(𝕜')[SemiNormedAlgebra 𝕜 𝕜']

include 𝕜

theorem NormedAlgebra.norm_one : ∥(1 : 𝕜')∥ = 1 :=
  by 
    simpa using norm_algebra_map_eq 𝕜' (1 : 𝕜)

theorem NormedAlgebra.norm_one_class : NormOneClass 𝕜' :=
  ⟨NormedAlgebra.norm_one 𝕜 𝕜'⟩

theorem NormedAlgebra.zero_ne_one : (0 : 𝕜') ≠ 1 :=
  by 
    refine' (ne_zero_of_norm_pos _).symm 
    rw [NormedAlgebra.norm_one 𝕜 𝕜']
    normNum

theorem NormedAlgebra.nontrivial : Nontrivial 𝕜' :=
  ⟨⟨0, 1, NormedAlgebra.zero_ne_one 𝕜 𝕜'⟩⟩

end NormedAlgebra

section RestrictScalars

variable(𝕜 :
    Type
      _)(𝕜' :
    Type
      _)[NormedField
      𝕜][NormedField
      𝕜'][NormedAlgebra 𝕜
      𝕜'](E : Type _)[NormedGroup E][NormedSpace 𝕜' E](F : Type _)[SemiNormedGroup F][SemiNormedSpace 𝕜' F]

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-seminormed space structure induced by a `𝕜'`-seminormed space structure when `𝕜'` is a
seminormed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `module.restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def SemiNormedSpace.restrictScalars : SemiNormedSpace 𝕜 F :=
  { RestrictScalars.module 𝕜 𝕜' F with
    norm_smul_le :=
      fun c x =>
        le_of_eqₓ$
          by 
            change ∥algebraMap 𝕜 𝕜' c • x∥ = ∥c∥*∥x∥
            simp [norm_smul] }

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-normed space structure induced by a `𝕜'`-normed space structure when `𝕜'` is a
normed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  { RestrictScalars.module 𝕜 𝕜' E with
    norm_smul_le :=
      fun c x =>
        le_of_eqₓ$
          by 
            change ∥algebraMap 𝕜 𝕜' c • x∥ = ∥c∥*∥x∥
            simp [norm_smul] }

instance  {𝕜 : Type _} {𝕜' : Type _} {F : Type _} [I : SemiNormedGroup F] : SemiNormedGroup (RestrictScalars 𝕜 𝕜' F) :=
  I

instance  {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [I : NormedGroup E] : NormedGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance Module.RestrictScalars.semiNormedSpaceOrig {𝕜 : Type _} {𝕜' : Type _} {F : Type _} [NormedField 𝕜']
  [SemiNormedGroup F] [I : SemiNormedSpace 𝕜' F] : SemiNormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' F) :=
  I

instance Module.RestrictScalars.normedSpaceOrig {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [NormedField 𝕜'] [NormedGroup E]
  [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I

instance  : SemiNormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' F) :=
  (SemiNormedSpace.restrictScalars 𝕜 𝕜' F : SemiNormedSpace 𝕜 F)

instance  : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  (NormedSpace.restrictScalars 𝕜 𝕜' E : NormedSpace 𝕜 E)

end RestrictScalars

section CauchyProduct

/-! ## Multiplying two infinite sums in a normed ring

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `topology/algebra/infinite_sum` (e.g `tsum_mul_tsum`),
but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `β` and `γ`, and then we specialize to
`β = γ = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).

### Arbitrary index types
-/


variable{ι' : Type _}[NormedRing α]

open Finset

open_locale Classical

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable.mul_of_nonneg
{f : ι → exprℝ()}
{g : ι' → exprℝ()}
(hf : summable f)
(hg : summable g)
(hf' : «expr ≤ »(0, f))
(hg' : «expr ≤ »(0, g)) : summable (λ x : «expr × »(ι, ι'), «expr * »(f x.1, g x.2)) :=
let ⟨s, hf⟩ := hf in
let ⟨t, hg⟩ := hg in
suffices this : ∀
u : finset «expr × »(ι, ι'), «expr ≤ »(«expr∑ in , »((x), u, «expr * »(f x.1, g x.2)), «expr * »(s, t)), from summable_of_sum_le (λ
 x, mul_nonneg (hf' _) (hg' _)) this,
assume u, calc
  «expr ≤ »(«expr∑ in , »((x), u, «expr * »(f x.1, g x.2)), «expr∑ in , »((x), (u.image prod.fst).product (u.image prod.snd), «expr * »(f x.1, g x.2))) : sum_mono_set_of_nonneg (λ
   x, mul_nonneg (hf' _) (hg' _)) subset_product
  «expr = »(..., «expr∑ in , »((x), u.image prod.fst, «expr∑ in , »((y), u.image prod.snd, «expr * »(f x, g y)))) : sum_product
  «expr = »(..., «expr∑ in , »((x), u.image prod.fst, «expr * »(f x, «expr∑ in , »((y), u.image prod.snd, g y)))) : sum_congr rfl (λ
   x _, mul_sum.symm)
  «expr ≤ »(..., «expr∑ in , »((x), u.image prod.fst, «expr * »(f x, t))) : sum_le_sum (λ
   x _, mul_le_mul_of_nonneg_left (sum_le_has_sum _ (λ _ _, hg' _) hg) (hf' _))
  «expr = »(..., «expr * »(«expr∑ in , »((x), u.image prod.fst, f x), t)) : sum_mul.symm
  «expr ≤ »(..., «expr * »(s, t)) : mul_le_mul_of_nonneg_right (sum_le_has_sum _ (λ
    _ _, hf' _) hf) «expr $ »(hg.nonneg, λ _, hg' _)

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable.mul_norm
{f : ι → α}
{g : ι' → α}
(hf : summable (λ x, «expr∥ ∥»(f x)))
(hg : summable (λ x, «expr∥ ∥»(g x))) : summable (λ x : «expr × »(ι, ι'), «expr∥ ∥»(«expr * »(f x.1, g x.2))) :=
summable_of_nonneg_of_le (λ
 x, norm_nonneg «expr * »(f x.1, g x.2)) (λ
 x, norm_mul_le (f x.1) (g x.2)) (hf.mul_of_nonneg hg (λ
 x, «expr $ »(norm_nonneg, f x)) (λ x, «expr $ »(norm_nonneg, g x)) : _)

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem summable_mul_of_summable_norm
[complete_space α]
{f : ι → α}
{g : ι' → α}
(hf : summable (λ x, «expr∥ ∥»(f x)))
(hg : summable (λ x, «expr∥ ∥»(g x))) : summable (λ x : «expr × »(ι, ι'), «expr * »(f x.1, g x.2)) :=
summable_of_summable_norm (hf.mul_norm hg)

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/
theorem tsum_mul_tsum_of_summable_norm [CompleteSpace α] {f : ι → α} {g : ι' → α} (hf : Summable fun x => ∥f x∥)
  (hg : Summable fun x => ∥g x∥) : ((∑'x, f x)*∑'y, g y) = ∑'z : ι × ι', f z.1*g z.2 :=
  tsum_mul_tsum (summable_of_summable_norm hf) (summable_of_summable_norm hg) (summable_mul_of_summable_norm hf hg)

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`finset.range (n+1)` involving `nat` substraction.
In order to avoid `nat` substraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n`. -/


section Nat

open Finset.Nat

-- error in Analysis.NormedSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem summable_norm_sum_mul_antidiagonal_of_summable_norm
{f g : exprℕ() → α}
(hf : summable (λ x, «expr∥ ∥»(f x)))
(hg : summable (λ
  x, «expr∥ ∥»(g x))) : summable (λ n, «expr∥ ∥»(«expr∑ in , »((kl), antidiagonal n, «expr * »(f kl.1, g kl.2)))) :=
begin
  have [] [] [":=", expr summable_sum_mul_antidiagonal_of_summable_mul (summable.mul_of_nonneg hf hg (λ
     _, norm_nonneg _) (λ _, norm_nonneg _))],
  refine [expr summable_of_nonneg_of_le (λ _, norm_nonneg _) _ this],
  intros [ident n],
  calc
    «expr ≤ »(«expr∥ ∥»(«expr∑ in , »((kl), antidiagonal n, «expr * »(f kl.1, g kl.2))), «expr∑ in , »((kl), antidiagonal n, «expr∥ ∥»(«expr * »(f kl.1, g kl.2)))) : norm_sum_le _ _
    «expr ≤ »(..., «expr∑ in , »((kl), antidiagonal n, «expr * »(«expr∥ ∥»(f kl.1), «expr∥ ∥»(g kl.2)))) : sum_le_sum (λ
     i _, norm_mul_le _ _)
end

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `finset.nat.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace α] {f g : ℕ → α}
  (hf : Summable fun x => ∥f x∥) (hg : Summable fun x => ∥g x∥) :
  ((∑'n, f n)*∑'n, g n) = ∑'n, ∑kl in antidiagonal n, f kl.1*g kl.2 :=
  tsum_mul_tsum_eq_tsum_sum_antidiagonal (summable_of_summable_norm hf) (summable_of_summable_norm hg)
    (summable_mul_of_summable_norm hf hg)

theorem summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → α} (hf : Summable fun x => ∥f x∥)
  (hg : Summable fun x => ∥g x∥) : Summable fun n => ∥∑k in range (n+1), f k*g (n - k)∥ :=
  by 
    simpRw [←sum_antidiagonal_eq_sum_range_succ fun k l => f k*g l]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace α] {f g : ℕ → α} (hf : Summable fun x => ∥f x∥)
  (hg : Summable fun x => ∥g x∥) : ((∑'n, f n)*∑'n, g n) = ∑'n, ∑k in range (n+1), f k*g (n - k) :=
  by 
    simpRw [←sum_antidiagonal_eq_sum_range_succ fun k l => f k*g l]
    exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg

end Nat

end CauchyProduct

