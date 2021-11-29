import Mathbin.Topology.Algebra.MulAction 
import Mathbin.Topology.MetricSpace.Lipschitz

/-!
# Compatibility of algebraic operations with metric space structures

In this file we define mixin typeclasses `has_lipschitz_mul`, `has_lipschitz_add`,
`has_bounded_smul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure.  The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `has_continuous_mul` instance from `has_lipschitz_mul`, etc.  In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`uniform_group`) is structured differently.

-/


open_locale Nnreal

noncomputable theory

variable(α β : Type _)[PseudoMetricSpace α][PseudoMetricSpace β]

section HasLipschitzMul

-- error in Topology.MetricSpace.Algebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Class `has_lipschitz_add M` says that the addition `(+) : X × X → X` is Lipschitz jointly in
the two arguments. -/
class has_lipschitz_add
[add_monoid β] : exprProp() :=
  (lipschitz_add : «expr∃ , »((C), lipschitz_with C (λ p : «expr × »(β, β), «expr + »(p.1, p.2))))

-- error in Topology.MetricSpace.Algebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Class `has_lipschitz_mul M` says that the multiplication `(*) : X × X → X` is Lipschitz jointly
in the two arguments. -/
@[to_additive #[]]
class has_lipschitz_mul
[monoid β] : exprProp() :=
  (lipschitz_mul : «expr∃ , »((C), lipschitz_with C (λ p : «expr × »(β, β), «expr * »(p.1, p.2))))

variable[Monoidₓ β]

/-- The Lipschitz constant of a monoid `β` satisfying `has_lipschitz_mul` -/
@[toAdditive "The Lipschitz constant of an `add_monoid` `β` satisfying `has_lipschitz_add`"]
def HasLipschitzMul.c [_i : HasLipschitzMul β] :  ℝ≥0  :=
  Classical.some _i.lipschitz_mul

variable{β}

-- error in Topology.MetricSpace.Algebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[to_additive #[]]
theorem lipschitz_with_lipschitz_const_mul_edist
[_i : has_lipschitz_mul β] : lipschitz_with (has_lipschitz_mul.C β) (λ p : «expr × »(β, β), «expr * »(p.1, p.2)) :=
classical.some_spec _i.lipschitz_mul

variable[HasLipschitzMul β]

@[toAdditive]
theorem lipschitz_with_lipschitz_const_mul : ∀ (p q : β × β), dist (p.1*p.2) (q.1*q.2) ≤ HasLipschitzMul.c β*dist p q :=
  by 
    rw [←lipschitz_with_iff_dist_le_mul]
    exact lipschitz_with_lipschitz_const_mul_edist

@[toAdditive]
instance (priority := 100)HasLipschitzMul.has_continuous_mul : HasContinuousMul β :=
  ⟨lipschitz_with_lipschitz_const_mul_edist.Continuous⟩

@[toAdditive]
instance Submonoid.has_lipschitz_mul (s : Submonoid β) : HasLipschitzMul s :=
  { lipschitz_mul :=
      ⟨HasLipschitzMul.c β,
        by 
          rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
          convert lipschitz_with_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩ }

-- error in Topology.MetricSpace.Algebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance real.has_lipschitz_add : has_lipschitz_add exprℝ() :=
{ lipschitz_add := ⟨2, begin
     rw [expr lipschitz_with_iff_dist_le_mul] [],
     intros [ident p, ident q],
     simp [] [] ["only"] ["[", expr real.dist_eq, ",", expr prod.dist_eq, ",", expr prod.fst_sub, ",", expr prod.snd_sub, ",", expr nnreal.coe_one, ",", expr nnreal.coe_bit0, "]"] [] [],
     convert [] [expr le_trans (abs_add «expr - »(p.1, q.1) «expr - »(p.2, q.2)) _] ["using", 2],
     { abel [] [] [] },
     have [] [] [":=", expr le_max_left «expr| |»(«expr - »(p.1, q.1)) «expr| |»(«expr - »(p.2, q.2))],
     have [] [] [":=", expr le_max_right «expr| |»(«expr - »(p.1, q.1)) «expr| |»(«expr - »(p.2, q.2))],
     linarith [] [] []
   end⟩ }

instance Nnreal.has_lipschitz_add : HasLipschitzAdd ℝ≥0  :=
  { lipschitz_add :=
      ⟨HasLipschitzAdd.c ℝ,
        by 
          rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
          convert lipschitz_with_lipschitz_const_add_edist ⟨(x₁ : ℝ), x₂⟩ ⟨y₁, y₂⟩ using 1⟩ }

end HasLipschitzMul

section HasBoundedSmul

variable[HasZero α][HasZero β][HasScalar α β]

/-- Mixin typeclass on a scalar action of a metric space `α` on a metric space `β` both with
distinguished points `0`, requiring compatibility of the action in the sense that
`dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂` and
`dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0`. -/
class HasBoundedSmul : Prop where 
  dist_smul_pair' : ∀ (x : α), ∀ (y₁ y₂ : β), dist (x • y₁) (x • y₂) ≤ dist x 0*dist y₁ y₂ 
  dist_pair_smul' : ∀ (x₁ x₂ : α), ∀ (y : β), dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂*dist y 0

variable{α β}[HasBoundedSmul α β]

theorem dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) ≤ dist x 0*dist y₁ y₂ :=
  HasBoundedSmul.dist_smul_pair' x y₁ y₂

theorem dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂*dist y 0 :=
  HasBoundedSmul.dist_pair_smul' x₁ x₂ y

-- error in Topology.MetricSpace.Algebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The typeclass `has_bounded_smul` on a metric-space scalar action implies continuity of the
action. -/ @[priority 100] instance has_bounded_smul.has_continuous_smul : has_continuous_smul α β :=
{ continuous_smul := begin
    rw [expr metric.continuous_iff] [],
    rintros ["⟨", ident a, ",", ident b, "⟩", ident ε, ident hε],
    have [] [":", expr «expr ≤ »(0, dist a 0)] [":=", expr dist_nonneg],
    have [] [":", expr «expr ≤ »(0, dist b 0)] [":=", expr dist_nonneg],
    let [ident δ] [":", expr exprℝ()] [":=", expr min 1 «expr * »(«expr ⁻¹»(«expr + »(«expr + »(dist a 0, dist b 0), 2)), ε)],
    have [ident hδ_pos] [":", expr «expr < »(0, δ)] [],
    { refine [expr lt_min_iff.mpr ⟨by norm_num [] [], mul_pos _ hε⟩],
      rw [expr inv_pos] [],
      linarith [] [] [] },
    refine [expr ⟨δ, hδ_pos, _⟩],
    rintros ["⟨", ident a', ",", ident b', "⟩", ident hab'],
    calc
      «expr ≤ »(_, _) : dist_triangle _ «expr • »(a, b') _
      «expr ≤ »(..., «expr * »(δ, «expr + »(«expr + »(dist a 0, dist b 0), δ))) : _
      «expr < »(..., ε) : _,
    { have [] [":", expr «expr ≤ »(0, dist a' a)] [":=", expr dist_nonneg],
      have [] [] [":=", expr dist_triangle b' b 0],
      have [] [] [":=", expr dist_comm «expr • »(a, b') «expr • »(a', b')],
      have [] [] [":=", expr dist_comm a a'],
      have [] [":", expr «expr ≤ »(dist a' a, dist (a', b') (a, b))] [":=", expr le_max_left _ _],
      have [] [":", expr «expr ≤ »(dist b' b, dist (a', b') (a, b))] [":=", expr le_max_right _ _],
      have [] [] [":=", expr dist_smul_pair a b' b],
      have [] [] [":=", expr dist_pair_smul a a' b'],
      nlinarith [] [] [] },
    { have [] [":", expr «expr ≤ »(δ, _)] [":=", expr min_le_right _ _],
      have [] [":", expr «expr ≤ »(δ, _)] [":=", expr min_le_left _ _],
      have [] [":", expr «expr < »(«expr * »(«expr ⁻¹»(«expr + »(«expr + »(dist a 0, dist b 0), 2)), «expr * »(ε, «expr + »(«expr + »(dist a 0, dist b 0), δ))), ε)] [],
      { rw [expr inv_mul_lt_iff] []; nlinarith [] [] [] },
      nlinarith [] [] [] }
  end }

instance Real.has_bounded_smul : HasBoundedSmul ℝ ℝ :=
  { dist_smul_pair' :=
      fun x y₁ y₂ =>
        by 
          simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le,
    dist_pair_smul' :=
      fun x₁ x₂ y =>
        by 
          simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le }

instance Nnreal.has_bounded_smul : HasBoundedSmul ℝ≥0  ℝ≥0  :=
  { dist_smul_pair' :=
      fun x y₁ y₂ =>
        by 
          convert dist_smul_pair (x : ℝ) (y₁ : ℝ) y₂ using 1,
    dist_pair_smul' :=
      fun x₁ x₂ y =>
        by 
          convert dist_pair_smul (x₁ : ℝ) x₂ (y : ℝ) using 1 }

end HasBoundedSmul

