import Mathbin.LinearAlgebra.AffineSpace.AffineMap 
import Mathbin.Topology.ContinuousFunction.Basic 
import Mathbin.Topology.Algebra.Module

/-!
# Continuous affine maps.

This file defines a type of bundled continuous affine maps.

Note that the definition and basic properties established here require minimal assumptions, and do
not even assume compatibility between the topological and algebraic structures. Of course it is
necessary to assume some compatibility in order to obtain a useful theory. Such a theory is
developed elsewhere for affine spaces modelled on _normed_ vector spaces, but not yet for general
topological affine spaces (since we have not defined these yet).

## Main definitions:

 * `continuous_affine_map`

## Notation:

We introduce the notation `P →A[R] Q` for `continuous_affine_map R P Q`. Note that this is parallel
to the notation `E →L[R] F` for `continuous_linear_map R E F`.
-/


/-- A continuous map of affine spaces. -/
structure ContinuousAffineMap (R : Type _) {V W : Type _} (P Q : Type _) [Ringₓ R] [AddCommGroupₓ V] [Module R V]
  [TopologicalSpace P] [AddTorsor V P] [AddCommGroupₓ W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q] extends
  P →ᵃ[R] Q where 
  cont : Continuous to_fun

notation:25 P " →A[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousAffineMap

variable {R V W P Q : Type _} [Ringₓ R]

variable [AddCommGroupₓ V] [Module R V] [TopologicalSpace P] [AddTorsor V P]

variable [AddCommGroupₓ W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

include V W

/-- see Note [function coercion] -/
instance : CoeFun (P →A[R] Q) fun _ => P → Q :=
  ⟨fun f => f.to_affine_map.to_fun⟩

theorem to_fun_eq_coe (f : P →A[R] Q) : f.to_fun = «expr⇑ » f :=
  rfl

-- error in Topology.Algebra.ContinuousAffineMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coe_injective : @function.injective «expr →A[ ] »(P, R, Q) (P → Q) coe_fn :=
begin
  rintros ["⟨", "⟨", ident f, ",", "⟨", ident f', ",", ident hf₁, ",", ident hf₂, "⟩", ",", ident hf₀, "⟩", ",", ident hf₁, "⟩", "⟨", "⟨", ident g, ",", "⟨", ident g', ",", ident hg₁, ",", ident hg₂, "⟩", ",", ident hg₀, "⟩", ",", ident hg₁, "⟩", ident h],
  have [] [":", expr «expr ∧ »(«expr = »(f, g), «expr = »(f', g'))] [],
  { simpa [] [] ["only"] [] [] ["using", expr affine_map.coe_fn_injective h] },
  congr,
  exacts ["[", expr this.1, ",", expr this.2, "]"]
end

@[ext]
theorem ext {f g : P →A[R] Q} (h : ∀ x, f x = g x) : f = g :=
  coe_injective$ funext h

theorem ext_iff {f g : P →A[R] Q} : f = g ↔ ∀ x, f x = g x :=
  ⟨by 
      rintro rfl x 
      rfl,
    ext⟩

theorem congr_funₓ {f g : P →A[R] Q} (h : f = g) (x : P) : f x = g x :=
  h ▸ rfl

instance : Coe (P →A[R] Q) (P →ᵃ[R] Q) :=
  ⟨to_affine_map⟩

/-- Forgetting its algebraic properties, a continuous affine map is a continuous map. -/
def to_continuous_map (f : P →A[R] Q) : C(P, Q) :=
  ⟨f, f.cont⟩

instance : Coe (P →A[R] Q) C(P, Q) :=
  ⟨to_continuous_map⟩

@[simp]
theorem to_affine_map_eq_coe (f : P →A[R] Q) : f.to_affine_map = «expr↑ » f :=
  rfl

@[simp]
theorem to_continuous_map_coe (f : P →A[R] Q) : f.to_continuous_map = «expr↑ » f :=
  rfl

@[simp, normCast]
theorem coe_to_affine_map (f : P →A[R] Q) : ((f : P →ᵃ[R] Q) : P → Q) = f :=
  rfl

@[simp, normCast]
theorem coe_to_continuous_map (f : P →A[R] Q) : ((f : C(P, Q)) : P → Q) = f :=
  rfl

theorem to_affine_map_injective {f g : P →A[R] Q} (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) : f = g :=
  by 
    ext a 
    exact AffineMap.congr_fun h a

theorem to_continuous_map_injective {f g : P →A[R] Q} (h : (f : C(P, Q)) = (g : C(P, Q))) : f = g :=
  by 
    ext a 
    exact ContinuousMap.congr_fun h a

@[normCast]
theorem coe_affine_map_mk (f : P →ᵃ[R] Q) h : ((⟨f, h⟩ : P →A[R] Q) : P →ᵃ[R] Q) = f :=
  rfl

@[normCast]
theorem coe_continuous_map_mk (f : P →ᵃ[R] Q) h : ((⟨f, h⟩ : P →A[R] Q) : C(P, Q)) = ⟨f, h⟩ :=
  rfl

@[simp]
theorem coe_mk (f : P →ᵃ[R] Q) h : ((⟨f, h⟩ : P →A[R] Q) : P → Q) = f :=
  rfl

@[simp]
theorem mk_coe (f : P →A[R] Q) h : (⟨(f : P →ᵃ[R] Q), h⟩ : P →A[R] Q) = f :=
  by 
    ext 
    rfl

@[continuity]
protected theorem Continuous (f : P →A[R] Q) : Continuous f :=
  f.2

variable (R P)

/-- The constant map is a continuous affine map. -/
def const (q : Q) : P →A[R] Q :=
  { AffineMap.const R P q with toFun := AffineMap.const R P q, cont := continuous_const }

@[simp]
theorem coe_const (q : Q) : (const R P q : P → Q) = Function.const P q :=
  rfl

noncomputable instance : Inhabited (P →A[R] Q) :=
  ⟨const R P$
      Nonempty.some
        (by 
          infer_instance :
        Nonempty Q)⟩

variable {R P} {W₂ Q₂ : Type _}

variable [AddCommGroupₓ W₂] [Module R W₂] [TopologicalSpace Q₂] [AddTorsor W₂ Q₂]

include W₂

/-- The composition of morphisms is a morphism. -/
def comp (f : Q →A[R] Q₂) (g : P →A[R] Q) : P →A[R] Q₂ :=
  { (f : Q →ᵃ[R] Q₂).comp (g : P →ᵃ[R] Q) with cont := f.cont.comp g.cont }

@[simp, normCast]
theorem coe_comp (f : Q →A[R] Q₂) (g : P →A[R] Q) : (f.comp g : P → Q₂) = ((f : Q → Q₂) ∘ (g : P → Q)) :=
  rfl

theorem comp_apply (f : Q →A[R] Q₂) (g : P →A[R] Q) (x : P) : f.comp g x = f (g x) :=
  rfl

omit W₂

section ModuleValuedMaps

variable {S : Type _} [CommRingₓ S] [Module S V] [Module S W]

variable [TopologicalSpace W] [TopologicalSpace S] [HasContinuousSmul S W]

instance : HasZero (P →A[R] W) :=
  ⟨ContinuousAffineMap.const R P 0⟩

@[normCast, simp]
theorem coe_zero : ((0 : P →A[R] W) : P → W) = 0 :=
  rfl

theorem zero_apply (x : P) : (0 : P →A[R] W) x = 0 :=
  rfl

instance : HasScalar S (P →A[S] W) :=
  { smul := fun t f => { t • (f : P →ᵃ[S] W) with cont := f.continuous.const_smul t } }

@[normCast, simp]
theorem coe_smul (t : S) (f : P →A[S] W) : «expr⇑ » (t • f) = t • f :=
  rfl

theorem smul_apply (t : S) (f : P →A[S] W) (x : P) : (t • f) x = t • f x :=
  rfl

variable [TopologicalAddGroup W]

instance : Add (P →A[R] W) :=
  { add := fun f g => { (f : P →ᵃ[R] W)+(g : P →ᵃ[R] W) with cont := f.continuous.add g.continuous } }

@[normCast, simp]
theorem coe_add (f g : P →A[R] W) : «expr⇑ » (f+g) = f+g :=
  rfl

theorem add_apply (f g : P →A[R] W) (x : P) : (f+g) x = f x+g x :=
  rfl

instance : Sub (P →A[R] W) :=
  { sub := fun f g => { (f : P →ᵃ[R] W) - (g : P →ᵃ[R] W) with cont := f.continuous.sub g.continuous } }

@[normCast, simp]
theorem coe_sub (f g : P →A[R] W) : «expr⇑ » (f - g) = f - g :=
  rfl

theorem sub_apply (f g : P →A[R] W) (x : P) : (f - g) x = f x - g x :=
  rfl

instance : Neg (P →A[R] W) :=
  { neg := fun f => { -(f : P →ᵃ[R] W) with cont := f.continuous.neg } }

@[normCast, simp]
theorem coe_neg (f : P →A[R] W) : «expr⇑ » (-f) = -f :=
  rfl

theorem neg_apply (f : P →A[R] W) (x : P) : (-f) x = -f x :=
  rfl

instance : AddCommGroupₓ (P →A[R] W) :=
  { (coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub : AddCommGroupₓ (P →A[R] W)) with add := ·+·,
    zero := 0, neg := Neg.neg, sub := Sub.sub }

instance : Module S (P →A[S] W) :=
  Function.Injective.module S ⟨fun f => f.to_affine_map.to_fun, rfl, coe_add⟩ coe_injective coe_smul

end ModuleValuedMaps

end ContinuousAffineMap

namespace ContinuousLinearMap

variable {R V W : Type _} [Ringₓ R]

variable [AddCommGroupₓ V] [Module R V] [TopologicalSpace V]

variable [AddCommGroupₓ W] [Module R W] [TopologicalSpace W]

/-- A continuous linear map can be regarded as a continuous affine map. -/
def to_continuous_affine_map (f : V →L[R] W) : V →A[R] W :=
  { toFun := f, linear := f,
    map_vadd' :=
      by 
        simp ,
    cont := f.cont }

@[simp]
theorem coe_to_continuous_affine_map (f : V →L[R] W) : «expr⇑ » f.to_continuous_affine_map = f :=
  rfl

@[simp]
theorem to_continuous_affine_map_map_zero (f : V →L[R] W) : f.to_continuous_affine_map 0 = 0 :=
  by 
    simp 

end ContinuousLinearMap

