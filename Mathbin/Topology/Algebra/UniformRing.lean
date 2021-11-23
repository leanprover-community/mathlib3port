import Mathbin.Topology.Algebra.GroupCompletion 
import Mathbin.Topology.Algebra.Ring

/-!
# Completion of topological rings:

This files endows the completion of a topological ring with a ring structure.
More precisely the instance `uniform_space.completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`uniform_add_group`. There is also a commutative version when the original ring is commutative.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `uniform_space.completion.extension_hom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `completion R`.
* `uniform_space.completion.map_ring_hom` : promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `completion R` to `completion S`.
-/


open Classical Set Filter TopologicalSpace AddCommGroupₓ

open_locale Classical

noncomputable theory

namespace UniformSpace.Completion

open DenseInducing UniformSpace Function

variable(α : Type _)[Ringₓ α][UniformSpace α]

instance  : HasOne (completion α) :=
  ⟨(1 : α)⟩

instance  : Mul (completion α) :=
  ⟨curry$ (dense_inducing_coe.Prod dense_inducing_coe).extend (coeₓ ∘ uncurry (·*·))⟩

@[normCast]
theorem coe_one : ((1 : α) : completion α) = 1 :=
  rfl

variable{α}[TopologicalRing α]

@[normCast]
theorem coe_mul (a b : α) : ((a*b : α) : completion α) = a*b :=
  ((dense_inducing_coe.Prod dense_inducing_coe).extend_eq ((continuous_coe α).comp (@continuous_mul α _ _ _))
      (a, b)).symm

variable[UniformAddGroup α]

-- error in Topology.Algebra.UniformRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_mul : continuous (λ p : «expr × »(completion α, completion α), «expr * »(p.1, p.2)) :=
begin
  let [ident m] [] [":=", expr (add_monoid_hom.mul : «expr →+ »(α, «expr →+ »(α, α))).compr₂ to_compl],
  have [] [":", expr continuous (λ p : «expr × »(α, α), m p.1 p.2)] [],
  from [expr (continuous_coe α).comp continuous_mul],
  have [ident di] [":", expr dense_inducing (to_compl : α → completion α)] [],
  from [expr dense_inducing_coe],
  convert [] [expr di.extend_Z_bilin di this] [],
  ext [] ["⟨", ident x, ",", ident y, "⟩"] [],
  refl
end

theorem Continuous.mul {β : Type _} [TopologicalSpace β] {f g : β → completion α} (hf : Continuous f)
  (hg : Continuous g) : Continuous fun b => f b*g b :=
  continuous_mul.comp (hf.prod_mk hg : _)

instance  : Ringₓ (completion α) :=
  { completion.add_comm_group, completion.has_mul α, completion.has_one α with
    one_mul :=
      fun a =>
        completion.induction_on a (is_closed_eq (Continuous.mul continuous_const continuous_id) continuous_id)
          fun a =>
            by 
              rw [←coe_one, ←coe_mul, one_mulₓ],
    mul_one :=
      fun a =>
        completion.induction_on a (is_closed_eq (Continuous.mul continuous_id continuous_const) continuous_id)
          fun a =>
            by 
              rw [←coe_one, ←coe_mul, mul_oneₓ],
    mul_assoc :=
      fun a b c =>
        completion.induction_on₃ a b c
          (is_closed_eq
            (Continuous.mul (Continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
              (continuous_snd.comp continuous_snd))
            (Continuous.mul continuous_fst
              (Continuous.mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
          fun a b c =>
            by 
              rw [←coe_mul, ←coe_mul, ←coe_mul, ←coe_mul, mul_assocₓ],
    left_distrib :=
      fun a b c =>
        completion.induction_on₃ a b c
          (is_closed_eq
            (Continuous.mul continuous_fst
              (Continuous.add (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)))
            (Continuous.add (Continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
              (Continuous.mul continuous_fst (continuous_snd.comp continuous_snd))))
          fun a b c =>
            by 
              rw [←coe_add, ←coe_mul, ←coe_mul, ←coe_mul, ←coe_add, mul_addₓ],
    right_distrib :=
      fun a b c =>
        completion.induction_on₃ a b c
          (is_closed_eq
            (Continuous.mul (Continuous.add continuous_fst (continuous_fst.comp continuous_snd))
              (continuous_snd.comp continuous_snd))
            (Continuous.add (Continuous.mul continuous_fst (continuous_snd.comp continuous_snd))
              (Continuous.mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
          fun a b c =>
            by 
              rw [←coe_add, ←coe_mul, ←coe_mul, ←coe_mul, ←coe_add, add_mulₓ] }

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
def coe_ring_hom : α →+* completion α :=
  ⟨coeₓ, coe_one α, fun a b => coe_mul a b, coe_zero, fun a b => coe_add a b⟩

theorem continuous_coe_ring_hom : Continuous (coe_ring_hom : α → completion α) :=
  continuous_coe α

universe u

variable{β : Type u}[UniformSpace β][Ringₓ β][UniformAddGroup β][TopologicalRing β](f : α →+* β)(hf : Continuous f)

/-- The completion extension as a ring morphism. -/
def extension_hom [CompleteSpace β] [SeparatedSpace β] : completion α →+* β :=
  have hf' : Continuous (f : α →+ β) := hf 
  have hf : UniformContinuous f := uniform_continuous_of_continuous hf'
  { toFun := completion.extension f,
    map_zero' :=
      by 
        rw [←coe_zero, extension_coe hf, f.map_zero],
    map_add' :=
      fun a b =>
        completion.induction_on₂ a b
          (is_closed_eq (continuous_extension.comp continuous_add)
            ((continuous_extension.comp continuous_fst).add (continuous_extension.comp continuous_snd)))
          fun a b =>
            by 
              rw [←coe_add, extension_coe hf, extension_coe hf, extension_coe hf, f.map_add],
    map_one' :=
      by 
        rw [←coe_one, extension_coe hf, f.map_one],
    map_mul' :=
      fun a b =>
        completion.induction_on₂ a b
          (is_closed_eq (continuous_extension.comp continuous_mul)
            ((continuous_extension.comp continuous_fst).mul (continuous_extension.comp continuous_snd)))
          fun a b =>
            by 
              rw [←coe_mul, extension_coe hf, extension_coe hf, extension_coe hf, f.map_mul] }

instance top_ring_compl : TopologicalRing (completion α) :=
  { continuous_add := continuous_add, continuous_mul := continuous_mul }

/-- The completion map as a ring morphism. -/
def map_ring_hom (hf : Continuous f) : completion α →+* completion β :=
  extension_hom (coe_ring_hom.comp f) (continuous_coe_ring_hom.comp hf)

variable(R : Type _)[CommRingₓ R][UniformSpace R][UniformAddGroup R][TopologicalRing R]

instance  : CommRingₓ (completion R) :=
  { completion.ring with
    mul_comm :=
      fun a b =>
        completion.induction_on₂ a b
          (is_closed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst))
          fun a b =>
            by 
              rw [←coe_mul, ←coe_mul, mul_commₓ] }

end UniformSpace.Completion

namespace UniformSpace

variable{α : Type _}

theorem ring_sep_rel α [CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
  separation_setoid α = Submodule.quotientRel (Ideal.closure ⊥) :=
  Setoidₓ.ext$ fun x y => group_separation_rel x y

theorem ring_sep_quot α [r : CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
  Quotientₓ (separation_setoid α) = (⊥ : Ideal α).closure.Quotient :=
  by 
    rw [@ring_sep_rel α r] <;> rfl

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sep_quot_equiv_ring_quot α [r : CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
  Quotientₓ (separation_setoid α) ≃ (⊥ : Ideal α).closure.Quotient :=
  Quotientₓ.congrRight$ fun x y => group_separation_rel x y

instance CommRingₓ [CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
  CommRingₓ (Quotientₓ (separation_setoid α)) :=
  by 
    rw [ring_sep_quot α] <;> infer_instance

instance TopologicalRing [CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
  TopologicalRing (Quotientₓ (separation_setoid α)) :=
  by 
    convert topological_ring_quotient (⊥ : Ideal α).closure <;>
      try 
        apply ring_sep_rel 
    simp [UniformSpace.commRing]

end UniformSpace

