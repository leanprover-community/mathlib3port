import Mathbin.Geometry.Manifold.Algebra.Structures

/-!
# Algebraic structures over smooth functions

In this file, we define instances of algebraic structures over smooth functions.
-/


noncomputable theory

open_locale Manifold

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜
      E]{E' :
    Type
      _}[NormedGroup
      E'][NormedSpace 𝕜
      E']{H :
    Type
      _}[TopologicalSpace
      H]{I :
    ModelWithCorners 𝕜 E
      H}{H' :
    Type
      _}[TopologicalSpace
      H']{I' :
    ModelWithCorners 𝕜 E'
      H'}{N :
    Type
      _}[TopologicalSpace
      N][ChartedSpace H
      N]{E'' :
    Type
      _}[NormedGroup
      E''][NormedSpace 𝕜
      E'']{H'' :
    Type
      _}[TopologicalSpace H'']{I'' : ModelWithCorners 𝕜 E'' H''}{N' : Type _}[TopologicalSpace N'][ChartedSpace H'' N']

namespace SmoothMap

@[toAdditive]
instance Mul {G : Type _} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] : Mul C^∞⟮I, N; I', G⟯ :=
  ⟨fun f g => ⟨f*g, f.smooth.mul g.smooth⟩⟩

@[simp, toAdditive]
theorem coe_mul {G : Type _} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G]
  (f g : C^∞⟮I, N; I', G⟯) : «expr⇑ » (f*g) = f*g :=
  rfl

@[simp, toAdditive]
theorem mul_comp {G : Type _} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G]
  (f g : C^∞⟮I'', N'; I', G⟯) (h : C^∞⟮I, N; I'', N'⟯) : (f*g).comp h = f.comp h*g.comp h :=
  by 
    ext <;> simp only [TimesContMdiffMap.comp_apply, coe_mul, Pi.mul_apply]

@[toAdditive]
instance HasOne {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] : HasOne C^∞⟮I, N; I', G⟯ :=
  ⟨TimesContMdiffMap.const (1 : G)⟩

@[simp, toAdditive]
theorem coe_one {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] :
  «expr⇑ » (1 : C^∞⟮I, N; I', G⟯) = 1 :=
  rfl

section GroupStructure

/-!
### Group structure

In this section we show that smooth functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/


@[toAdditive]
instance Semigroupₓ {G : Type _} [Semigroupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
  Semigroupₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.hasMul with
    mul_assoc :=
      fun a b c =>
        by 
          ext <;> exact mul_assocₓ _ _ _ }

@[toAdditive]
instance Monoidₓ {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
  Monoidₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.semigroup, SmoothMap.hasOne with
    one_mul :=
      fun a =>
        by 
          ext <;> exact one_mulₓ _,
    mul_one :=
      fun a =>
        by 
          ext <;> exact mul_oneₓ _ }

/-- Coercion to a function as an `monoid_hom`. Similar to `monoid_hom.coe_fn`. -/
@[toAdditive "Coercion to a function as an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.", simps]
def coe_fn_monoid_hom {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
  C^∞⟮I, N; I', G⟯ →* N → G :=
  { toFun := coeFn, map_one' := coe_one, map_mul' := coe_mul }

@[toAdditive]
instance CommMonoidₓ {G : Type _} [CommMonoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
  CommMonoidₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.monoid, SmoothMap.hasOne with
    mul_comm :=
      fun a b =>
        by 
          ext <;> exact mul_commₓ _ _ }

@[toAdditive]
instance Groupₓ {G : Type _} [Groupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G] :
  Groupₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.monoid with inv := fun f => ⟨fun x => f x⁻¹, f.smooth.inv⟩,
    mul_left_inv :=
      fun a =>
        by 
          ext <;> exact mul_left_invₓ _,
    div := fun f g => ⟨f / g, f.smooth.div g.smooth⟩,
    div_eq_mul_inv :=
      fun f g =>
        by 
          ext <;> exact div_eq_mul_inv _ _ }

@[simp, toAdditive]
theorem coe_inv {G : Type _} [Groupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G]
  (f : C^∞⟮I, N; I', G⟯) : «expr⇑ » (f⁻¹) = f⁻¹ :=
  rfl

@[simp, toAdditive]
theorem coe_div {G : Type _} [Groupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G]
  (f g : C^∞⟮I, N; I', G⟯) : «expr⇑ » (f / g) = f / g :=
  rfl

@[toAdditive]
instance CommGroupₓ {G : Type _} [CommGroupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G] :
  CommGroupₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.group, SmoothMap.commMonoid with  }

end GroupStructure

section RingStructure

/-!
### Ring stucture

In this section we show that smooth functions valued in a smooth ring `R` inherit a ring structure
under pointwise multiplication.
-/


instance Semiringₓ {R : Type _} [Semiringₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
  Semiringₓ C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.addCommMonoid, SmoothMap.monoid with
    left_distrib :=
      fun a b c =>
        by 
          ext <;> exact left_distrib _ _ _,
    right_distrib :=
      fun a b c =>
        by 
          ext <;> exact right_distrib _ _ _,
    zero_mul :=
      fun a =>
        by 
          ext <;> exact zero_mul _,
    mul_zero :=
      fun a =>
        by 
          ext <;> exact mul_zero _ }

instance Ringₓ {R : Type _} [Ringₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
  Ringₓ C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.semiring, SmoothMap.addCommGroup with  }

instance CommRingₓ {R : Type _} [CommRingₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
  CommRingₓ C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.semiring, SmoothMap.addCommGroup, SmoothMap.commMonoid with  }

/-- Coercion to a function as a `ring_hom`. -/
@[simps]
def coe_fn_ring_hom {R : Type _} [CommRingₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
  C^∞⟮I, N; I', R⟯ →+* N → R :=
  { (coe_fn_monoid_hom : C^∞⟮I, N; I', R⟯ →* _), (coe_fn_add_monoid_hom : C^∞⟮I, N; I', R⟯ →+ _) with toFun := coeFn }

/-- `function.eval` as a `ring_hom` on the ring of smooth functions. -/
def eval_ring_hom {R : Type _} [CommRingₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] (n : N) :
  C^∞⟮I, N; I', R⟯ →+* R :=
  (Pi.evalRingHom _ n : (N → R) →+* R).comp SmoothMap.coeFnRingHom

end RingStructure

section ModuleStructure

/-!
### Semiodule stucture

In this section we show that smooth functions valued in a vector space `M` over a normed
field `𝕜` inherit a vector space structure.
-/


instance HasScalar {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : HasScalar 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun r f => ⟨r • f, smooth_const.smul f.smooth⟩⟩

@[simp]
theorem coe_smul {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] (r : 𝕜) (f : C^∞⟮I, N; 𝓘(𝕜, V), V⟯) :
  «expr⇑ » (r • f) = r • f :=
  rfl

@[simp]
theorem smul_comp {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] (r : 𝕜) (g : C^∞⟮I'', N'; 𝓘(𝕜, V), V⟯)
  (h : C^∞⟮I, N; I'', N'⟯) : (r • g).comp h = r • g.comp h :=
  rfl

instance Module {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : Module 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  Module.ofCore$
    { smul := · • ·,
      smul_add :=
        fun c f g =>
          by 
            ext x <;> exact smul_add c (f x) (g x),
      add_smul :=
        fun c₁ c₂ f =>
          by 
            ext x <;> exact add_smul c₁ c₂ (f x),
      mul_smul :=
        fun c₁ c₂ f =>
          by 
            ext x <;> exact mul_smul c₁ c₂ (f x),
      one_smul :=
        fun f =>
          by 
            ext x <;> exact one_smul 𝕜 (f x) }

/-- Coercion to a function as a `linear_map`. -/
@[simps]
def coe_fn_linear_map {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : C^∞⟮I, N; 𝓘(𝕜, V), V⟯ →ₗ[𝕜] N → V :=
  { (coe_fn_add_monoid_hom : C^∞⟮I, N; 𝓘(𝕜, V), V⟯ →+ _) with toFun := coeFn, map_smul' := coe_smul }

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that smooth functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/


variable{A : Type _}[NormedRing A][NormedAlgebra 𝕜 A][SmoothRing 𝓘(𝕜, A) A]

-- error in Geometry.Manifold.Algebra.SmoothFunctions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Smooth constant functions as a `ring_hom`. -/
def C : «expr →+* »(𝕜, «exprC^ ⟮ , ; , ⟯»(«expr∞»(), I, N, «expr𝓘( , )»(𝕜, A), A)) :=
{ to_fun := λ c : 𝕜, ⟨λ x, algebra_map 𝕜 A c, smooth_const⟩,
  map_one' := by ext [] [ident x] []; exact [expr (algebra_map 𝕜 A).map_one],
  map_mul' := λ c₁ c₂, by ext [] [ident x] []; exact [expr (algebra_map 𝕜 A).map_mul _ _],
  map_zero' := by ext [] [ident x] []; exact [expr (algebra_map 𝕜 A).map_zero],
  map_add' := λ c₁ c₂, by ext [] [ident x] []; exact [expr (algebra_map 𝕜 A).map_add _ _] }

instance Algebra : Algebra 𝕜 C^∞⟮I, N; 𝓘(𝕜, A), A⟯ :=
  { SmoothMap.semiring with smul := fun r f => ⟨r • f, smooth_const.smul f.smooth⟩, toRingHom := SmoothMap.c,
    commutes' :=
      fun c f =>
        by 
          ext x <;> exact Algebra.commutes' _ _,
    smul_def' :=
      fun c f =>
        by 
          ext x <;> exact Algebra.smul_def' _ _ }

/-- Coercion to a function as an `alg_hom`. -/
@[simps]
def coe_fn_alg_hom : C^∞⟮I, N; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] N → A :=
  { toFun := coeFn, commutes' := fun r => rfl, map_zero' := SmoothMap.coe_zero, map_one' := SmoothMap.coe_one,
    map_add' := SmoothMap.coe_add, map_mul' := SmoothMap.coe_mul }

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of smooth functions from `N` to `V`
is naturally a vector space over the ring of smooth functions from `N` to `𝕜`. -/


instance has_scalar' {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : HasScalar C^∞⟮I, N; 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun f g => ⟨fun x => f x • g x, Smooth.smul f.2 g.2⟩⟩

@[simp]
theorem smul_comp' {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] (f : C^∞⟮I'', N'; 𝕜⟯) (g : C^∞⟮I'', N'; 𝓘(𝕜, V), V⟯)
  (h : C^∞⟮I, N; I'', N'⟯) : (f • g).comp h = f.comp h • g.comp h :=
  rfl

instance module' {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : Module C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  { smul := · • ·,
    smul_add :=
      fun c f g =>
        by 
          ext x <;> exact smul_add (c x) (f x) (g x),
    add_smul :=
      fun c₁ c₂ f =>
        by 
          ext x <;> exact add_smul (c₁ x) (c₂ x) (f x),
    mul_smul :=
      fun c₁ c₂ f =>
        by 
          ext x <;> exact mul_smul (c₁ x) (c₂ x) (f x),
    one_smul :=
      fun f =>
        by 
          ext x <;> exact one_smul 𝕜 (f x),
    zero_smul :=
      fun f =>
        by 
          ext x <;> exact zero_smul _ _,
    smul_zero :=
      fun r =>
        by 
          ext x <;> exact smul_zero _ }

end ModuleOverContinuousFunctions

end SmoothMap

