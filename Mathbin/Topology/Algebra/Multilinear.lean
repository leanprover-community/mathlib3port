import Mathbin.Topology.Algebra.Module 
import Mathbin.LinearAlgebra.Multilinear.Basic

/-!
# Continuous multilinear maps

We define continuous multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are multilinear
and continuous, by extending the space of multilinear maps with a continuity assumption.
Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type, and all these
spaces are also topological spaces.

## Main definitions

* `continuous_multilinear_map R M₁ M₂` is the space of continuous multilinear maps from
  `Π(i : ι), M₁ i` to `M₂`. We show that it is an `R`-module.

## Implementation notes

We mostly follow the API of multilinear maps.

## Notation

We introduce the notation `M [×n]→L[R] M'` for the space of continuous `n`-multilinear maps from
`M^n` to `M'`. This is a particular case of the general notion (where we allow varying dependent
types as the arguments of our continuous multilinear maps), but arguably the most important one,
especially when defining iterated derivatives.
-/


open Function Finₓ Set

open_locale BigOperators

universe u v w w₁ w₁' w₂ w₃ w₄

variable{R :
    Type
      u}{ι :
    Type
      v}{n :
    ℕ}{M :
    Finₓ n.succ → Type w}{M₁ : ι → Type w₁}{M₁' : ι → Type w₁'}{M₂ : Type w₂}{M₃ : Type w₃}{M₄ : Type w₄}[DecidableEq ι]

/-- Continuous multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂`
are modules over `R` with a topological structure. In applications, there will be compatibility
conditions between the algebraic and the topological structures, but this is not needed for the
definition. -/
structure
  ContinuousMultilinearMap(R :
    Type
      u){ι :
    Type
      v}(M₁ :
    ι →
      Type
        w₁)(M₂ :
    Type
      w₂)[DecidableEq
      ι][Semiringₓ
      R][∀ i,
      AddCommMonoidₓ
        (M₁
          i)][AddCommMonoidₓ
      M₂][∀ i, Module R (M₁ i)][Module R M₂][∀ i, TopologicalSpace (M₁ i)][TopologicalSpace M₂] extends
  MultilinearMap R M₁ M₂ where 
  cont : Continuous to_fun

-- error in Topology.Algebra.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
notation M `[×`:25 n `]→L[`:25 R `] ` M' := continuous_multilinear_map R (λ i : fin n, M) M'

namespace ContinuousMultilinearMap

section Semiringₓ

variable[Semiringₓ
      R][∀ i,
      AddCommMonoidₓ
        (M
          i)][∀ i,
      AddCommMonoidₓ
        (M₁
          i)][∀ i,
      AddCommMonoidₓ
        (M₁'
          i)][AddCommMonoidₓ
      M₂][AddCommMonoidₓ
      M₃][AddCommMonoidₓ
      M₄][∀ i,
      Module R
        (M
          i)][∀ i,
      Module R
        (M₁
          i)][∀ i,
      Module R
        (M₁'
          i)][Module R
      M₂][Module R
      M₃][Module R
      M₄][∀ i,
      TopologicalSpace
        (M
          i)][∀ i,
      TopologicalSpace
        (M₁
          i)][∀ i,
      TopologicalSpace
        (M₁' i)][TopologicalSpace M₂][TopologicalSpace M₃][TopologicalSpace M₄](f f' : ContinuousMultilinearMap R M₁ M₂)

instance  : CoeFun (ContinuousMultilinearMap R M₁ M₂) fun _ => (∀ i, M₁ i) → M₂ :=
  ⟨fun f => f.to_fun⟩

@[continuity]
theorem coe_continuous : Continuous (f : (∀ i, M₁ i) → M₂) :=
  f.cont

@[simp]
theorem coe_coe : (f.to_multilinear_map : (∀ i, M₁ i) → M₂) = f :=
  rfl

theorem to_multilinear_map_inj :
  Function.Injective
    (ContinuousMultilinearMap.toMultilinearMap : ContinuousMultilinearMap R M₁ M₂ → MultilinearMap R M₁ M₂)
| ⟨f, hf⟩, ⟨g, hg⟩, rfl => rfl

@[ext]
theorem ext {f f' : ContinuousMultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
  to_multilinear_map_inj$ MultilinearMap.ext H

@[simp]
theorem map_add (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x+y)) = f (update m i x)+f (update m i y) :=
  f.map_add' m i x y

@[simp]
theorem map_smul (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) : f (update m i (c • x)) = c • f (update m i x) :=
  f.map_smul' m i c x

theorem map_coord_zero {m : ∀ i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
  f.to_multilinear_map.map_coord_zero i h

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.to_multilinear_map.map_zero

instance  : HasZero (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨{ (0 : MultilinearMap R M₁ M₂) with cont := continuous_const }⟩

instance  : Inhabited (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨0⟩

@[simp]
theorem zero_apply (m : ∀ i, M₁ i) : (0 : ContinuousMultilinearMap R M₁ M₂) m = 0 :=
  rfl

section HasContinuousAdd

variable[HasContinuousAdd M₂]

instance  : Add (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f f' => ⟨f.to_multilinear_map+f'.to_multilinear_map, f.cont.add f'.cont⟩⟩

@[simp]
theorem add_apply (m : ∀ i, M₁ i) : (f+f') m = f m+f' m :=
  rfl

@[simp]
theorem to_multilinear_map_add (f g : ContinuousMultilinearMap R M₁ M₂) :
  (f+g).toMultilinearMap = f.to_multilinear_map+g.to_multilinear_map :=
  rfl

instance AddCommMonoidₓ : AddCommMonoidₓ (ContinuousMultilinearMap R M₁ M₂) :=
  to_multilinear_map_inj.AddCommMonoid _ rfl fun _ _ => rfl

/-- Evaluation of a `continuous_multilinear_map` at a vector as an `add_monoid_hom`. -/
def apply_add_hom (m : ∀ i, M₁ i) : ContinuousMultilinearMap R M₁ M₂ →+ M₂ :=
  ⟨fun f => f m, rfl, fun _ _ => rfl⟩

@[simp]
theorem sum_apply {α : Type _} (f : α → ContinuousMultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) {s : Finset α} :
  (∑a in s, f a) m = ∑a in s, f a m :=
  (apply_add_hom m).map_sum f s

end HasContinuousAdd

/-- If `f` is a continuous multilinear map, then `f.to_continuous_linear_map m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
def to_continuous_linear_map (m : ∀ i, M₁ i) (i : ι) : M₁ i →L[R] M₂ :=
  { f.to_multilinear_map.to_linear_map m i with cont := f.cont.comp (continuous_const.update i continuous_id) }

/-- The cartesian product of two continuous multilinear maps, as a continuous multilinear map. -/
def Prod (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) :
  ContinuousMultilinearMap R M₁ (M₂ × M₃) :=
  { f.to_multilinear_map.prod g.to_multilinear_map with cont := f.cont.prod_mk g.cont }

@[simp]
theorem prod_apply (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) (m : ∀ i, M₁ i) :
  (f.prod g) m = (f m, g m) :=
  rfl

/-- Combine a family of continuous multilinear maps with the same domain and codomains `M' i` into a
continuous multilinear map taking values in the space of functions `Π i, M' i`. -/
def pi {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoidₓ (M' i)] [∀ i, TopologicalSpace (M' i)]
  [∀ i, Module R (M' i)] (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) : ContinuousMultilinearMap R M₁ (∀ i, M' i) :=
  { cont := continuous_pi$ fun i => (f i).coe_continuous,
    toMultilinearMap := MultilinearMap.pi fun i => (f i).toMultilinearMap }

@[simp]
theorem coe_pi {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoidₓ (M' i)] [∀ i, TopologicalSpace (M' i)]
  [∀ i, Module R (M' i)] (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) : «expr⇑ » (pi f) = fun m j => f j m :=
  rfl

theorem pi_apply {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoidₓ (M' i)] [∀ i, TopologicalSpace (M' i)]
  [∀ i, Module R (M' i)] (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) (m : ∀ i, M₁ i) (j : ι') : pi f m j = f j m :=
  rfl

/-- If `g` is continuous multilinear and `f` is a collection of continuous linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a continuous multilinear map, that we call
`g.comp_continuous_linear_map f`. -/
def comp_continuous_linear_map (g : ContinuousMultilinearMap R M₁' M₄) (f : ∀ (i : ι), M₁ i →L[R] M₁' i) :
  ContinuousMultilinearMap R M₁ M₄ :=
  { g.to_multilinear_map.comp_linear_map fun i => (f i).toLinearMap with
    cont := g.cont.comp$ continuous_pi$ fun j => (f j).cont.comp$ continuous_apply _ }

@[simp]
theorem comp_continuous_linear_map_apply (g : ContinuousMultilinearMap R M₁' M₄) (f : ∀ (i : ι), M₁ i →L[R] M₁' i)
  (m : ∀ i, M₁ i) : g.comp_continuous_linear_map f m = g fun i => f i$ m i :=
  rfl

/-- Composing a continuous multilinear map with a continuous linear map gives again a
continuous multilinear map. -/
def _root_.continuous_linear_map.comp_continuous_multilinear_map (g : M₂ →L[R] M₃)
  (f : ContinuousMultilinearMap R M₁ M₂) : ContinuousMultilinearMap R M₁ M₃ :=
  { g.to_linear_map.comp_multilinear_map f.to_multilinear_map with cont := g.cont.comp f.cont }

@[simp]
theorem _root_.continuous_linear_map.comp_continuous_multilinear_map_coe (g : M₂ →L[R] M₃)
  (f : ContinuousMultilinearMap R M₁ M₂) :
  (g.comp_continuous_multilinear_map f : (∀ i, M₁ i) → M₃) = ((g : M₂ → M₃) ∘ (f : (∀ i, M₁ i) → M₂)) :=
  by 
    ext m 
    rfl

/-- `continuous_multilinear_map.pi` as an `equiv`. -/
@[simps]
def pi_equiv {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoidₓ (M' i)] [∀ i, TopologicalSpace (M' i)]
  [∀ i, Module R (M' i)] : (∀ i, ContinuousMultilinearMap R M₁ (M' i)) ≃ ContinuousMultilinearMap R M₁ (∀ i, M' i) :=
  { toFun := ContinuousMultilinearMap.pi,
    invFun := fun f i => (ContinuousLinearMap.proj i : _ →L[R] M' i).compContinuousMultilinearMap f,
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rfl }

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
theorem cons_add (f : ContinuousMultilinearMap R M M₂) (m : ∀ (i : Finₓ n), M i.succ) (x y : M 0) :
  f (cons (x+y) m) = f (cons x m)+f (cons y m) :=
  f.to_multilinear_map.cons_add m x y

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a multilinear map along the first variable. -/
theorem cons_smul (f : ContinuousMultilinearMap R M M₂) (m : ∀ (i : Finₓ n), M i.succ) (c : R) (x : M 0) :
  f (cons (c • x) m) = c • f (cons x m) :=
  f.to_multilinear_map.cons_smul m c x

theorem map_piecewise_add (m m' : ∀ i, M₁ i) (t : Finset ι) :
  f (t.piecewise (m+m') m') = ∑s in t.powerset, f (s.piecewise m m') :=
  f.to_multilinear_map.map_piecewise_add _ _ _

/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ [Fintype ι] (m m' : ∀ i, M₁ i) : f (m+m') = ∑s : Finset ι, f (s.piecewise m m') :=
  f.to_multilinear_map.map_add_univ _ _

section ApplySum

open Fintype Finset

variable{α : ι → Type _}[Fintype ι](g : ∀ i, α i → M₁ i)(A : ∀ i, Finset (α i))

/-- If `f` is continuous multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset : (f fun i => ∑j in A i, g i j) = ∑r in pi_finset A, f fun i => g i (r i) :=
  f.to_multilinear_map.map_sum_finset _ _

/-- If `f` is continuous multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum [∀ i, Fintype (α i)] : (f fun i => ∑j, g i j) = ∑r : ∀ i, α i, f fun i => g i (r i) :=
  f.to_multilinear_map.map_sum _

end ApplySum

section RestrictScalar

variable(R){A :
    Type
      _}[Semiringₓ
      A][HasScalar R A][∀ (i : ι), Module A (M₁ i)][Module A M₂][∀ i, IsScalarTower R A (M₁ i)][IsScalarTower R A M₂]

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrict_scalars (f : ContinuousMultilinearMap A M₁ M₂) : ContinuousMultilinearMap R M₁ M₂ :=
  { toMultilinearMap := f.to_multilinear_map.restrict_scalars R, cont := f.cont }

@[simp]
theorem coe_restrict_scalars (f : ContinuousMultilinearMap A M₁ M₂) : «expr⇑ » (f.restrict_scalars R) = f :=
  rfl

end RestrictScalar

end Semiringₓ

section Ringₓ

variable[Ringₓ
      R][∀ i,
      AddCommGroupₓ
        (M₁
          i)][AddCommGroupₓ
      M₂][∀ i,
      Module R
        (M₁ i)][Module R M₂][∀ i, TopologicalSpace (M₁ i)][TopologicalSpace M₂](f f' : ContinuousMultilinearMap R M₁ M₂)

@[simp]
theorem map_sub (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.to_multilinear_map.map_sub _ _ _ _

section TopologicalAddGroup

variable[TopologicalAddGroup M₂]

instance  : Neg (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f => { -f.to_multilinear_map with cont := f.cont.neg }⟩

@[simp]
theorem neg_apply (m : ∀ i, M₁ i) : (-f) m = -f m :=
  rfl

instance  : Sub (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f g => { f.to_multilinear_map - g.to_multilinear_map with cont := f.cont.sub g.cont }⟩

@[simp]
theorem sub_apply (m : ∀ i, M₁ i) : (f - f') m = f m - f' m :=
  rfl

instance  : AddCommGroupₓ (ContinuousMultilinearMap R M₁ M₂) :=
  to_multilinear_map_inj.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) fun _ _ => rfl

end TopologicalAddGroup

end Ringₓ

section CommSemiringₓ

variable[CommSemiringₓ
      R][∀ i,
      AddCommMonoidₓ
        (M₁
          i)][AddCommMonoidₓ
      M₂][∀ i,
      Module R
        (M₁ i)][Module R M₂][∀ i, TopologicalSpace (M₁ i)][TopologicalSpace M₂](f : ContinuousMultilinearMap R M₁ M₂)

theorem map_piecewise_smul (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
  f (s.piecewise (fun i => c i • m i) m) = (∏i in s, c i) • f m :=
  f.to_multilinear_map.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous multilinear map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) : (f fun i => c i • m i) = (∏i, c i) • f m :=
  f.to_multilinear_map.map_smul_univ _ _

variable{R' A :
    Type
      _}[CommSemiringₓ
      R'][Semiringₓ
      A][Algebra R'
      A][∀ i,
      Module A (M₁ i)][Module R' M₂][Module A M₂][IsScalarTower R' A M₂][TopologicalSpace R'][HasContinuousSmul R' M₂]

instance  : HasScalar R' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c f => { c • f.to_multilinear_map with cont := continuous_const.smul f.cont }⟩

@[simp]
theorem smul_apply (f : ContinuousMultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) : (c • f) m = c • f m :=
  rfl

@[simp]
theorem to_multilinear_map_smul (c : R') (f : ContinuousMultilinearMap A M₁ M₂) :
  (c • f).toMultilinearMap = c • f.to_multilinear_map :=
  rfl

instance  {R''} [CommSemiringₓ R''] [HasScalar R' R''] [Algebra R'' A] [Module R'' M₂] [IsScalarTower R'' A M₂]
  [IsScalarTower R' R'' M₂] [TopologicalSpace R''] [HasContinuousSmul R'' M₂] :
  IsScalarTower R' R'' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c₁ c₂ f => ext$ fun x => smul_assoc _ _ _⟩

variable[HasContinuousAdd M₂]

/-- The space of continuous multilinear maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
instance  : Module R' (ContinuousMultilinearMap A M₁ M₂) :=
  { one_smul := fun f => ext$ fun x => one_smul _ _, mul_smul := fun c₁ c₂ f => ext$ fun x => mul_smul _ _ _,
    smul_zero := fun r => ext$ fun x => smul_zero _, smul_add := fun r f₁ f₂ => ext$ fun x => smul_add _ _ _,
    add_smul := fun r₁ r₂ f => ext$ fun x => add_smul _ _ _, zero_smul := fun f => ext$ fun x => zero_smul _ _ }

/-- Linear map version of the map `to_multilinear_map` associating to a continuous multilinear map
the corresponding multilinear map. -/
@[simps]
def to_multilinear_map_linear : ContinuousMultilinearMap A M₁ M₂ →ₗ[R'] MultilinearMap A M₁ M₂ :=
  { toFun := fun f => f.to_multilinear_map, map_add' := fun f g => rfl, map_smul' := fun c f => rfl }

/-- `continuous_multilinear_map.pi` as a `linear_equiv`. -/
@[simps (config := { simpRhs := tt })]
def pi_linear_equiv {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoidₓ (M' i)] [∀ i, TopologicalSpace (M' i)]
  [∀ i, HasContinuousAdd (M' i)] [∀ i, Module R' (M' i)] [∀ i, Module A (M' i)] [∀ i, IsScalarTower R' A (M' i)]
  [∀ i, HasContinuousSmul R' (M' i)] :
  let inst : HasContinuousSmul R' (∀ i, M' i) := Pi.has_continuous_smul
  (∀ i, ContinuousMultilinearMap A M₁ (M' i)) ≃ₗ[R'] ContinuousMultilinearMap A M₁ (∀ i, M' i) :=
  { pi_equiv with map_add' := fun x y => rfl, map_smul' := fun c x => rfl }

end CommSemiringₓ

end ContinuousMultilinearMap

