import Mathbin.Topology.Algebra.Module 
import Mathbin.Topology.Instances.Real

/-!
# Continuous additive maps are `ℝ`-linear

In this file we prove that a continuous map `f : E →+ F` between two topological vector spaces
over `ℝ` is `ℝ`-linear
-/


variable{E :
    Type
      _}[AddCommGroupₓ
      E][Module ℝ
      E][TopologicalSpace
      E][HasContinuousSmul ℝ
      E]{F : Type _}[AddCommGroupₓ F][Module ℝ F][TopologicalSpace F][HasContinuousSmul ℝ F][T2Space F]

namespace AddMonoidHom

-- error in Topology.Instances.RealVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear. -/
theorem map_real_smul
(f : «expr →+ »(E, F))
(hf : continuous f)
(c : exprℝ())
(x : E) : «expr = »(f «expr • »(c, x), «expr • »(c, f x)) :=
suffices «expr = »(λ c : exprℝ(), f «expr • »(c, x), λ c : exprℝ(), «expr • »(c, f x)), from _root_.congr_fun this c,
rat.dense_embedding_coe_real.dense.equalizer «expr $ »(hf.comp, continuous_id.smul continuous_const) (continuous_id.smul continuous_const) «expr $ »(funext, λ
 r, f.map_rat_cast_smul exprℝ() exprℝ() r x)

/-- Reinterpret a continuous additive homomorphism between two real vector spaces
as a continuous real-linear map. -/
def to_real_linear_map (f : E →+ F) (hf : Continuous f) : E →L[ℝ] F :=
  ⟨{ toFun := f, map_add' := f.map_add, map_smul' := f.map_real_smul hf }, hf⟩

@[simp]
theorem coe_to_real_linear_map (f : E →+ F) (hf : Continuous f) : «expr⇑ » (f.to_real_linear_map hf) = f :=
  rfl

end AddMonoidHom

