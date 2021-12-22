import Mathbin.Topology.LocallyConstant.Algebra
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.ContinuousFunction.Algebra

/-!
# The algebra morphism from locally constant functions to continuous functions.

-/


namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] (f : LocallyConstant X Y)

/--  The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive "The inclusion of locally-constant functions into continuous functions as an\nadditive monoid hom.",
  simps]
def to_continuous_map_monoid_hom [Monoidₓ Y] [HasContinuousMul Y] : LocallyConstant X Y →* C(X, Y) :=
  { toFun := coeₓ,
    map_one' := by
      ext
      simp ,
    map_mul' := fun x y => by
      ext
      simp }

/--  The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps]
def to_continuous_map_linear_map (R : Type _) [Semiringₓ R] [TopologicalSpace R] [AddCommMonoidₓ Y] [Module R Y]
    [HasContinuousAdd Y] [HasContinuousSmul R Y] : LocallyConstant X Y →ₗ[R] C(X, Y) :=
  { toFun := coeₓ,
    map_add' := fun x y => by
      ext
      simp ,
    map_smul' := fun x y => by
      ext
      simp }

/--  The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps]
def to_continuous_map_alg_hom (R : Type _) [CommSemiringₓ R] [TopologicalSpace R] [Semiringₓ Y] [Algebra R Y]
    [TopologicalRing Y] [HasContinuousSmul R Y] : LocallyConstant X Y →ₐ[R] C(X, Y) :=
  { toFun := coeₓ,
    map_one' := by
      ext
      simp ,
    map_mul' := fun x y => by
      ext
      simp ,
    map_zero' := by
      ext
      simp ,
    map_add' := fun x y => by
      ext
      simp ,
    commutes' := fun r => by
      ext x
      simp [Algebra.smul_def] }

end LocallyConstant

