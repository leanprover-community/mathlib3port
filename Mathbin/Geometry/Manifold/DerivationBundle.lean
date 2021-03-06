/-
Copyright Â© 2020 NicolÃ² Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NicolÃ² Cavalleri
-/
import Mathbin.Geometry.Manifold.Algebra.SmoothFunctions
import Mathbin.RingTheory.Derivation

/-!

# Derivation bundle

In this file we define the derivations at a point of a manifold on the algebra of smooth fuctions.
Moreover, we define the differential of a function in terms of derivations.

The content of this file is not meant to be regarded as an alternative definition to the current
tangent bundle but rather as a purely algebraic theory that provides a purely algebraic definition
of the Lie algebra for a Lie group.

-/


variable (ð : Type _) [NondiscreteNormedField ð] {E : Type _} [NormedGroup E] [NormedSpace ð E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners ð E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M] (n : WithTop â)

open Manifold

-- the following two instances prevent poorly understood type class inference timeout problems
instance smoothFunctionsAlgebra : Algebra ð C^ââ®I, M; ðâ¯ := by
  infer_instance

instance smooth_functions_tower : IsScalarTower ð C^ââ®I, M; ðâ¯ C^ââ®I, M; ðâ¯ := by
  infer_instance

/-- Type synonym, introduced to put a different `has_smul` action on `C^nâ®I, M; ðâ¯`
which is defined as `f â¢ r = f(x) * r`. -/
@[nolint unused_arguments]
def PointedSmoothMap (x : M) :=
  C^nâ®I, M; ðâ¯

-- mathport name: Â«exprC^ â® , ; â¯â¨ â©Â»
localized [Derivation] notation "C^" n "â®" I "," M ";" ð "â¯â¨" x "â©" => PointedSmoothMap ð I M n x

variable {ð M}

namespace PointedSmoothMap

instance {x : M} : CoeFun C^ââ®I,M;ðâ¯â¨xâ© fun _ => M â ð :=
  ContMdiffMap.hasCoeToFun

instance {x : M} : CommRingâ C^ââ®I,M;ðâ¯â¨xâ© :=
  SmoothMap.commRing

instance {x : M} : Algebra ð C^ââ®I,M;ðâ¯â¨xâ© :=
  SmoothMap.algebra

instance {x : M} : Inhabited C^ââ®I,M;ðâ¯â¨xâ© :=
  â¨0â©

instance {x : M} : Algebra C^ââ®I,M;ðâ¯â¨xâ© C^ââ®I, M; ðâ¯ :=
  Algebra.id C^ââ®I, M; ðâ¯

instance {x : M} : IsScalarTower ð C^ââ®I,M;ðâ¯â¨xâ© C^ââ®I, M; ðâ¯ :=
  IsScalarTower.right

variable {I}

/-- `smooth_map.eval_ring_hom` gives rise to an algebra structure of `C^ââ®I, M; ðâ¯` on `ð`. -/
instance evalAlgebra {x : M} : Algebra C^ââ®I,M;ðâ¯â¨xâ© ð :=
  (SmoothMap.evalRingHom x : C^ââ®I,M;ðâ¯â¨xâ© â+* ð).toAlgebra

/-- With the `eval_algebra` algebra structure evaluation is actually an algebra morphism. -/
def eval (x : M) : C^ââ®I, M; ðâ¯ ââ[C^ââ®I,M;ðâ¯â¨xâ©] ð :=
  Algebra.ofId C^ââ®I,M;ðâ¯â¨xâ© ð

theorem smul_def (x : M) (f : C^ââ®I,M;ðâ¯â¨xâ©) (k : ð) : f â¢ k = f x * k :=
  rfl

instance (x : M) :
    IsScalarTower ð C^ââ®I,M;ðâ¯â¨xâ© ð where smul_assoc := fun k f h => by
    simp only [â smul_def, â Algebra.id.smul_eq_mul, â SmoothMap.coe_smul, â Pi.smul_apply, â mul_assoc]

end PointedSmoothMap

open Derivation

/-- The derivations at a point of a manifold. Some regard this as a possible definition of the
tangent space -/
@[reducible]
def PointDerivation (x : M) :=
  Derivation ð C^ââ®I,M;ðâ¯â¨xâ© ð

section

variable (I) {M} (X Y : Derivation ð C^ââ®I, M; ðâ¯ C^ââ®I, M; ðâ¯) (f g : C^ââ®I, M; ðâ¯) (r : ð)

/-- Evaluation at a point gives rise to a `C^ââ®I, M; ðâ¯`-linear map between `C^ââ®I, M; ðâ¯` and `ð`.
 -/
def SmoothFunction.evalAt (x : M) : C^ââ®I, M; ðâ¯ ââ[C^ââ®I,M;ðâ¯â¨xâ©] ð :=
  (PointedSmoothMap.eval x).toLinearMap

namespace Derivation

variable {I}

/-- The evaluation at a point as a linear map. -/
def evalAt (x : M) : Derivation ð C^ââ®I, M; ðâ¯ C^ââ®I, M; ðâ¯ ââ[ð] PointDerivation I x :=
  (SmoothFunction.evalAt I x).compDer

theorem eval_at_apply (x : M) : evalAt x X f = (X f) x :=
  rfl

end Derivation

variable {I} {E' : Type _} [NormedGroup E'] [NormedSpace ð E'] {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners ð E' H'} {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']

/-- The heterogeneous differential as a linear map. Instead of taking a function as an argument this
differential takes `h : f x = y`. It is particularly handy to deal with situations where the points
on where it has to be evaluated are equal but not definitionally equal. -/
def hfdifferential {f : C^ââ®I, M; I', M'â¯} {x : M} {y : M'} (h : f x = y) :
    PointDerivation I x ââ[ð] PointDerivation I' y where
  toFun := fun v =>
    Derivation.mk'
      { toFun := fun g => v (g.comp f),
        map_add' := fun g g' => by
          rw [SmoothMap.add_comp, Derivation.map_add],
        map_smul' := fun k g => by
          simp only [â SmoothMap.smul_comp, â Derivation.map_smul, â RingHom.id_apply] }
      fun g g' => by
      simp only [â Derivation.leibniz, â SmoothMap.mul_comp, â LinearMap.coe_mk, â PointedSmoothMap.smul_def, â
        ContMdiffMap.comp_apply, â h]
  map_smul' := fun k v => rfl
  map_add' := fun v w => rfl

/-- The homogeneous differential as a linear map. -/
def fdifferential (f : C^ââ®I, M; I', M'â¯) (x : M) : PointDerivation I x ââ[ð] PointDerivation I' (f x) :=
  hfdifferential (rfl : f x = f x)

-- mathport name: Â«exprðÂ»
-- Standard notation for the differential. The abbreviation is `MId`.
localized [Manifold] notation "ð" => fdifferential

-- mathport name: Â«exprðâÂ»
-- Standard notation for the differential. The abbreviation is `MId`.
localized [Manifold] notation "ðâ" => hfdifferential

@[simp]
theorem apply_fdifferential (f : C^ââ®I, M; I', M'â¯) {x : M} (v : PointDerivation I x) (g : C^ââ®I', M'; ðâ¯) :
    ð f x v g = v (g.comp f) :=
  rfl

@[simp]
theorem apply_hfdifferential {f : C^ââ®I, M; I', M'â¯} {x : M} {y : M'} (h : f x = y) (v : PointDerivation I x)
    (g : C^ââ®I', M'; ðâ¯) : ðâ h v g = ð f x v g :=
  rfl

variable {E'' : Type _} [NormedGroup E''] [NormedSpace ð E''] {H'' : Type _} [TopologicalSpace H'']
  {I'' : ModelWithCorners ð E'' H''} {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M'']

@[simp]
theorem fdifferential_comp (g : C^ââ®I', M'; I'', M''â¯) (f : C^ââ®I, M; I', M'â¯) (x : M) :
    ð (g.comp f) x = (ð g (f x)).comp (ð f x) :=
  rfl

end

