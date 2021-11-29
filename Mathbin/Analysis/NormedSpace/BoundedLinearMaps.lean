import Mathbin.Analysis.NormedSpace.Multilinear 
import Mathbin.Analysis.NormedSpace.Units 
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# Bounded linear maps

This file defines a class stating that a map between normed vector spaces is (bi)linear and
continuous.
Instead of asking for continuity, the definition takes the equivalent condition (because the space
is normed) that `∥f x∥` is bounded by a multiple of `∥x∥`. Hence the "bounded" in the name refers to
`∥f x∥/∥x∥` rather than `∥f x∥` itself.

## Main definitions

* `is_bounded_linear_map`: Class stating that a map `f : E → F` is linear and has `∥f x∥` bounded
  by a multiple of `∥x∥`.
* `is_bounded_bilinear_map`: Class stating that a map `f : E × F → G` is bilinear and continuous,
  but through the simpler to provide statement that `∥f (x, y)∥` is bounded by a multiple of
  `∥x∥ * ∥y∥`
* `is_bounded_bilinear_map.linear_deriv`: Derivative of a continuous bilinear map as a linear map.
* `is_bounded_bilinear_map.deriv`: Derivative of a continuous bilinear map as a continuous linear
  map. The proof that it is indeed the derivative is `is_bounded_bilinear_map.has_fderiv_at` in
  `analysis.calculus.fderiv`.

## Main theorems

* `is_bounded_bilinear_map.continuous`: A bounded bilinear map is continuous.
* `continuous_linear_equiv.is_open`: The continuous linear equivalences are an open subset of the
  set of continuous linear maps between a pair of Banach spaces.  Placed in this file because its
  proof uses `is_bounded_bilinear_map.continuous`.

## Notes

The main use of this file is `is_bounded_bilinear_map`. The file `analysis.normed_space.multilinear`
already expounds the theory of multilinear maps, but the `2`-variables case is sufficiently simpler
to currently deserve its own treatment.

`is_bounded_linear_map` is effectively an unbundled version of `continuous_linear_map` (defined
in `topology.algebra.module`, theory over normed spaces developed in
`analysis.normed_space.operator_norm`), albeit the name disparity. A bundled
`continuous_linear_map` is to be preferred over a `is_bounded_linear_map` hypothesis. Historical
artifact, really.
-/


noncomputable theory

open_locale Classical BigOperators TopologicalSpace

open filter(Tendsto)

open Metric

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜 E]{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]{G : Type _}[NormedGroup G][NormedSpace 𝕜 G]

/-- A function `f` satisfies `is_bounded_linear_map 𝕜 f` if it is linear and satisfies the
inequality `∥f x∥ ≤ M * ∥x∥` for some positive constant `M`. -/
structure
  IsBoundedLinearMap(𝕜 :
    Type
      _)[NormedField
      𝕜]{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]{F : Type _}[NormedGroup F][NormedSpace 𝕜 F](f : E → F) extends
  IsLinearMap 𝕜 f : Prop where 
  bound : ∃ M, 0 < M ∧ ∀ (x : E), ∥f x∥ ≤ M*∥x∥

theorem IsLinearMap.with_bound {f : E → F} (hf : IsLinearMap 𝕜 f) (M : ℝ) (h : ∀ (x : E), ∥f x∥ ≤ M*∥x∥) :
  IsBoundedLinearMap 𝕜 f :=
  ⟨hf,
    Classical.by_cases
      (fun this : M ≤ 0 =>
        ⟨1, zero_lt_one, fun x => (h x).trans$ mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun this : ¬M ≤ 0 => ⟨M, lt_of_not_geₓ this, h⟩⟩

/-- A continuous linear map satisfies `is_bounded_linear_map` -/
theorem ContinuousLinearMap.is_bounded_linear_map (f : E →L[𝕜] F) : IsBoundedLinearMap 𝕜 f :=
  { f.to_linear_map.is_linear with bound := f.bound }

namespace IsBoundedLinearMap

/-- Construct a linear map from a function `f` satisfying `is_bounded_linear_map 𝕜 f`. -/
def to_linear_map (f : E → F) (h : IsBoundedLinearMap 𝕜 f) : E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.to_is_linear_map

/-- Construct a continuous linear map from is_bounded_linear_map -/
def to_continuous_linear_map {f : E → F} (hf : IsBoundedLinearMap 𝕜 f) : E →L[𝕜] F :=
  { to_linear_map f hf with
    cont :=
      let ⟨C, Cpos, hC⟩ := hf.bound 
      LinearMap.continuous_of_bound _ C hC }

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem zero : is_bounded_linear_map 𝕜 (λ x : E, (0 : F)) :=
«expr $ »((0 : «expr →ₗ[ ] »(E, 𝕜, F)).is_linear.with_bound 0, by simp [] [] [] ["[", expr le_refl, "]"] [] [])

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem id : is_bounded_linear_map 𝕜 (λ x : E, x) :=
«expr $ »(linear_map.id.is_linear.with_bound 1, by simp [] [] [] ["[", expr le_refl, "]"] [] [])

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem fst : is_bounded_linear_map 𝕜 (λ x : «expr × »(E, F), x.1) :=
begin
  refine [expr (linear_map.fst 𝕜 E F).is_linear.with_bound 1 (λ x, _)],
  rw [expr one_mul] [],
  exact [expr le_max_left _ _]
end

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem snd : is_bounded_linear_map 𝕜 (λ x : «expr × »(E, F), x.2) :=
begin
  refine [expr (linear_map.snd 𝕜 E F).is_linear.with_bound 1 (λ x, _)],
  rw [expr one_mul] [],
  exact [expr le_max_right _ _]
end

variable{f g : E → F}

theorem smul (c : 𝕜) (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (c • f) :=
  let ⟨hlf, M, hMp, hM⟩ := hf
  (c • hlf.mk' f).is_linear.with_bound (∥c∥*M)$
    fun x =>
      calc ∥c • f x∥ = ∥c∥*∥f x∥ := norm_smul c (f x)
        _ ≤ ∥c∥*M*∥x∥ := mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
        _ = (∥c∥*M)*∥x∥ := (mul_assocₓ _ _ _).symm
        

theorem neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 fun e => -f e :=
  by 
    rw
      [show (fun e => -f e) = fun e => (-1 : 𝕜) • f e by 
        funext 
        simp ]
    exact smul (-1) hf

theorem add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) : IsBoundedLinearMap 𝕜 fun e => f e+g e :=
  let ⟨hlf, Mf, hMfp, hMf⟩ := hf 
  let ⟨hlg, Mg, hMgp, hMg⟩ := hg
  (hlf.mk' _+hlg.mk' _).is_linear.with_bound (Mf+Mg)$
    fun x =>
      calc ∥f x+g x∥ ≤ (Mf*∥x∥)+Mg*∥x∥ := norm_add_le_of_le (hMf x) (hMg x)
        _ ≤ (Mf+Mg)*∥x∥ :=
        by 
          rw [add_mulₓ]
        

theorem sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) : IsBoundedLinearMap 𝕜 fun e => f e - g e :=
  by 
    simpa [sub_eq_add_neg] using add hf (neg hg)

theorem comp {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (g ∘ f) :=
  (hg.to_continuous_linear_map.comp hf.to_continuous_linear_map).IsBoundedLinearMap

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected theorem tendsto (x : E) (hf : is_bounded_linear_map 𝕜 f) : tendsto f (expr𝓝() x) (expr𝓝() (f x)) :=
let ⟨hf, M, hMp, hM⟩ := hf in
«expr $ »(tendsto_iff_norm_tendsto_zero.2, squeeze_zero (λ
  e, norm_nonneg _) (λ e, calc
    «expr = »(«expr∥ ∥»(«expr - »(f e, f x)), «expr∥ ∥»(hf.mk' f «expr - »(e, x))) : by rw [expr (hf.mk' _).map_sub e x] []; refl
    «expr ≤ »(..., «expr * »(M, «expr∥ ∥»(«expr - »(e, x)))) : hM «expr - »(e, x)) (suffices tendsto (λ
   e : E, «expr * »(M, «expr∥ ∥»(«expr - »(e, x)))) (expr𝓝() x) (expr𝓝() «expr * »(M, 0)), by simpa [] [] [] [] [] [],
  tendsto_const_nhds.mul (tendsto_norm_sub_self _)))

theorem Continuous (hf : IsBoundedLinearMap 𝕜 f) : Continuous f :=
  continuous_iff_continuous_at.2$ fun _ => hf.tendsto _

theorem lim_zero_bounded_linear_map (hf : IsBoundedLinearMap 𝕜 f) : tendsto f (𝓝 0) (𝓝 0) :=
  (hf.1.mk' _).map_zero ▸ continuous_iff_continuous_at.1 hf.continuous 0

section 

open Asymptotics Filter

theorem is_O_id {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) : is_O f (fun x => x) l :=
  let ⟨M, hMp, hM⟩ := h.bound 
  is_O.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)

theorem is_O_comp {E : Type _} {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) {f : E → F} (l : Filter E) :
  is_O (fun x' => g (f x')) f l :=
  (hg.is_O_id ⊤).comp_tendsto le_top

theorem is_O_sub {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E) :
  is_O (fun x' => f (x' - x)) (fun x' => x' - x) l :=
  is_O_comp h l

end 

end IsBoundedLinearMap

section 

variable{ι : Type _}[DecidableEq ι][Fintype ι]

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Taking the cartesian product of two continuous multilinear maps
is a bounded linear operation. -/
theorem is_bounded_linear_map_prod_multilinear
{E : ι → Type*}
[∀ i, normed_group (E i)]
[∀
 i, normed_space 𝕜 (E i)] : is_bounded_linear_map 𝕜 (λ
 p : «expr × »(continuous_multilinear_map 𝕜 E F, continuous_multilinear_map 𝕜 E G), p.1.prod p.2) :=
{ map_add := λ p₁ p₂, by { ext1 [] [ident m],
    refl },
  map_smul := λ c p, by { ext1 [] [ident m],
    refl },
  bound := ⟨1, zero_lt_one, λ p, begin
     rw [expr one_mul] [],
     apply [expr continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λ m, _)],
     rw ["[", expr continuous_multilinear_map.prod_apply, ",", expr norm_prod_le_iff, "]"] [],
     split,
     { exact [expr (p.1.le_op_norm m).trans (mul_le_mul_of_nonneg_right (norm_fst_le p) (finset.prod_nonneg (λ
           i hi, norm_nonneg _)))] },
     { exact [expr (p.2.le_op_norm m).trans (mul_le_mul_of_nonneg_right (norm_snd_le p) (finset.prod_nonneg (λ
           i hi, norm_nonneg _)))] }
   end⟩ }

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
theorem is_bounded_linear_map_continuous_multilinear_map_comp_linear
(g : «expr →L[ ] »(G, 𝕜, E)) : is_bounded_linear_map 𝕜 (λ
 f : continuous_multilinear_map 𝕜 (λ i : ι, E) F, f.comp_continuous_linear_map (λ _, g)) :=
begin
  refine [expr is_linear_map.with_bound ⟨λ f₁ f₂, by { ext [] [ident m] [],
      refl }, λ c f, by { ext [] [ident m] [],
      refl }⟩ «expr ^ »(«expr∥ ∥»(g), fintype.card ι) (λ f, _)],
  apply [expr continuous_multilinear_map.op_norm_le_bound _ _ (λ m, _)],
  { apply_rules ["[", expr mul_nonneg, ",", expr pow_nonneg, ",", expr norm_nonneg, "]"] },
  calc
    «expr ≤ »(«expr∥ ∥»(f «expr ∘ »(g, m)), «expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr∥ ∥»(g (m i))))) : f.le_op_norm _
    «expr ≤ »(..., «expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr * »(«expr∥ ∥»(g), «expr∥ ∥»(m i))))) : begin
      apply [expr mul_le_mul_of_nonneg_left _ (norm_nonneg _)],
      exact [expr finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, g.le_op_norm _)]
    end
    «expr = »(..., «expr * »(«expr * »(«expr ^ »(«expr∥ ∥»(g), fintype.card ι), «expr∥ ∥»(f)), «expr∏ , »((i), «expr∥ ∥»(m i)))) : by { simp [] [] [] ["[", expr finset.prod_mul_distrib, ",", expr finset.card_univ, "]"] [] [],
      ring [] }
end

end 

section BilinearMap

variable(𝕜)

/-- A map `f : E × F → G` satisfies `is_bounded_bilinear_map 𝕜 f` if it is bilinear and
continuous. -/
structure IsBoundedBilinearMap(f : E × F → G) : Prop where 
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁+x₂, y) = f (x₁, y)+f (x₂, y)
  smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁+y₂) = f (x, y₁)+f (x, y₂)
  smulRight : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
  bound : ∃ (C : _)(_ : C > 0), ∀ (x : E) (y : F), ∥f (x, y)∥ ≤ (C*∥x∥)*∥y∥

variable{𝕜}

variable{f : E × F → G}

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_linear_map.is_bounded_bilinear_map
(f : «expr →L[ ] »(E, 𝕜, «expr →L[ ] »(F, 𝕜, G))) : is_bounded_bilinear_map 𝕜 (λ x : «expr × »(E, F), f x.1 x.2) :=
{ add_left := λ x₁ x₂ y, by rw ["[", expr f.map_add, ",", expr continuous_linear_map.add_apply, "]"] [],
  smul_left := λ c x y, by rw ["[", expr f.map_smul _, ",", expr continuous_linear_map.smul_apply, "]"] [],
  add_right := λ x, (f x).map_add,
  smul_right := λ c x y, (f x).map_smul c y,
  bound := ⟨max «expr∥ ∥»(f) 1, zero_lt_one.trans_le (le_max_right _ _), λ
   x
   y, «expr $ »((f.le_op_norm₂ x y).trans, by apply_rules ["[", expr mul_le_mul_of_nonneg_right, ",", expr norm_nonneg, ",", expr le_max_left, "]"])⟩ }

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem is_bounded_bilinear_map.is_O
(h : is_bounded_bilinear_map 𝕜 f) : asymptotics.is_O f (λ
 p : «expr × »(E, F), «expr * »(«expr∥ ∥»(p.1), «expr∥ ∥»(p.2))) «expr⊤»() :=
let ⟨C, Cpos, hC⟩ := h.bound in
«expr $ »(asymptotics.is_O.of_bound _, «expr $ »(filter.eventually_of_forall, λ
  ⟨x, y⟩, by simpa [] [] [] ["[", expr mul_assoc, "]"] [] ["using", expr hC x y]))

theorem IsBoundedBilinearMap.is_O_comp {α : Type _} (H : IsBoundedBilinearMap 𝕜 f) {g : α → E} {h : α → F}
  {l : Filter α} : Asymptotics.IsO (fun x => f (g x, h x)) (fun x => ∥g x∥*∥h x∥) l :=
  H.is_O.comp_tendsto le_top

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem is_bounded_bilinear_map.is_O'
(h : is_bounded_bilinear_map 𝕜 f) : asymptotics.is_O f (λ
 p : «expr × »(E, F), «expr * »(«expr∥ ∥»(p), «expr∥ ∥»(p))) «expr⊤»() :=
h.is_O.trans (asymptotics.is_O_fst_prod'.norm_norm.mul asymptotics.is_O_snd_prod'.norm_norm)

theorem IsBoundedBilinearMap.map_sub_left (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F} :
  f (x - y, z) = f (x, z) - f (y, z) :=
  calc f (x - y, z) = f (x+(-1 : 𝕜) • y, z) :=
    by 
      simp [sub_eq_add_neg]
    _ = f (x, z)+(-1 : 𝕜) • f (y, z) :=
    by 
      simp only [h.add_left, h.smul_left]
    _ = f (x, z) - f (y, z) :=
    by 
      simp [sub_eq_add_neg]
    

theorem IsBoundedBilinearMap.map_sub_right (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F} :
  f (x, y - z) = f (x, y) - f (x, z) :=
  calc f (x, y - z) = f (x, y+(-1 : 𝕜) • z) :=
    by 
      simp [sub_eq_add_neg]
    _ = f (x, y)+(-1 : 𝕜) • f (x, z) :=
    by 
      simp only [h.add_right, h.smul_right]
    _ = f (x, y) - f (x, z) :=
    by 
      simp [sub_eq_add_neg]
    

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_bounded_bilinear_map.continuous (h : is_bounded_bilinear_map 𝕜 f) : continuous f :=
begin
  have [ident one_ne] [":", expr «expr ≠ »((1 : exprℝ()), 0)] [":=", expr by simp [] [] [] [] [] []],
  obtain ["⟨", ident C, ",", "(", ident Cpos, ":", expr «expr < »(0, C), ")", ",", ident hC, "⟩", ":=", expr h.bound],
  rw [expr continuous_iff_continuous_at] [],
  intros [ident x],
  have [ident H] [":", expr ∀
   (a : E)
   (b : F), «expr ≤ »(«expr∥ ∥»(f (a, b)), «expr * »(C, «expr∥ ∥»(«expr * »(«expr∥ ∥»(a), «expr∥ ∥»(b)))))] [],
  { intros [ident a, ident b],
    simpa [] [] [] ["[", expr mul_assoc, "]"] [] ["using", expr hC a b] },
  have [ident h₁] [":", expr asymptotics.is_o (λ
    e : «expr × »(E, F), f («expr - »(e.1, x.1), e.2)) (λ e, (1 : exprℝ())) (expr𝓝() x)] [],
  { refine [expr (asymptotics.is_O_of_le' (expr𝓝() x) (λ e, H «expr - »(e.1, x.1) e.2)).trans_is_o _],
    rw [expr asymptotics.is_o_const_iff one_ne] [],
    convert [] [expr ((continuous_fst.sub continuous_const).norm.mul continuous_snd.norm).continuous_at] [],
    { simp [] [] [] [] [] [] },
    apply_instance },
  have [ident h₂] [":", expr asymptotics.is_o (λ
    e : «expr × »(E, F), f (x.1, «expr - »(e.2, x.2))) (λ e, (1 : exprℝ())) (expr𝓝() x)] [],
  { refine [expr (asymptotics.is_O_of_le' (expr𝓝() x) (λ e, H x.1 «expr - »(e.2, x.2))).trans_is_o _],
    rw [expr asymptotics.is_o_const_iff one_ne] [],
    convert [] [expr (continuous_const.mul (continuous_snd.sub continuous_const).norm).continuous_at] [],
    { simp [] [] [] [] [] [] },
    apply_instance },
  have [] [] [":=", expr h₁.add h₂],
  rw [expr asymptotics.is_o_const_iff one_ne] ["at", ident this],
  change [expr tendsto _ _ _] [] [],
  convert [] [expr this.add_const (f x)] [],
  { ext [] [ident e] [],
    simp [] [] [] ["[", expr h.map_sub_left, ",", expr h.map_sub_right, "]"] [] [] },
  { simp [] [] [] [] [] [] }
end

theorem IsBoundedBilinearMap.continuous_left (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F} :
  Continuous fun e₁ => f (e₁, e₂) :=
  h.continuous.comp (continuous_id.prod_mk continuous_const)

theorem IsBoundedBilinearMap.continuous_right (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E} :
  Continuous fun e₂ => f (e₁, e₂) :=
  h.continuous.comp (continuous_const.prod_mk continuous_id)

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_bounded_bilinear_map.is_bounded_linear_map_left
(h : is_bounded_bilinear_map 𝕜 f)
(y : F) : is_bounded_linear_map 𝕜 (λ x, f (x, y)) :=
{ map_add := λ x x', h.add_left _ _ _,
  map_smul := λ c x, h.smul_left _ _ _,
  bound := begin
    rcases [expr h.bound, "with", "⟨", ident C, ",", ident C_pos, ",", ident hC, "⟩"],
    refine [expr ⟨«expr * »(C, «expr + »(«expr∥ ∥»(y), 1)), mul_pos C_pos (lt_of_lt_of_le zero_lt_one (by simp [] [] [] [] [] [])), λ
      x, _⟩],
    have [] [":", expr «expr ≤ »(«expr∥ ∥»(y), «expr + »(«expr∥ ∥»(y), 1))] [],
    by simp [] [] [] ["[", expr zero_le_one, "]"] [] [],
    calc
      «expr ≤ »(«expr∥ ∥»(f (x, y)), «expr * »(«expr * »(C, «expr∥ ∥»(x)), «expr∥ ∥»(y))) : hC x y
      «expr ≤ »(..., «expr * »(«expr * »(C, «expr∥ ∥»(x)), «expr + »(«expr∥ ∥»(y), 1))) : by apply_rules ["[", expr norm_nonneg, ",", expr mul_le_mul_of_nonneg_left, ",", expr le_of_lt C_pos, ",", expr mul_nonneg, "]"]
      «expr = »(..., «expr * »(«expr * »(C, «expr + »(«expr∥ ∥»(y), 1)), «expr∥ ∥»(x))) : by ring []
  end }

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_bounded_bilinear_map.is_bounded_linear_map_right
(h : is_bounded_bilinear_map 𝕜 f)
(x : E) : is_bounded_linear_map 𝕜 (λ y, f (x, y)) :=
{ map_add := λ y y', h.add_right _ _ _,
  map_smul := λ c y, h.smul_right _ _ _,
  bound := begin
    rcases [expr h.bound, "with", "⟨", ident C, ",", ident C_pos, ",", ident hC, "⟩"],
    refine [expr ⟨«expr * »(C, «expr + »(«expr∥ ∥»(x), 1)), mul_pos C_pos (lt_of_lt_of_le zero_lt_one (by simp [] [] [] [] [] [])), λ
      y, _⟩],
    have [] [":", expr «expr ≤ »(«expr∥ ∥»(x), «expr + »(«expr∥ ∥»(x), 1))] [],
    by simp [] [] [] ["[", expr zero_le_one, "]"] [] [],
    calc
      «expr ≤ »(«expr∥ ∥»(f (x, y)), «expr * »(«expr * »(C, «expr∥ ∥»(x)), «expr∥ ∥»(y))) : hC x y
      «expr ≤ »(..., «expr * »(«expr * »(C, «expr + »(«expr∥ ∥»(x), 1)), «expr∥ ∥»(y))) : by apply_rules ["[", expr mul_le_mul_of_nonneg_right, ",", expr norm_nonneg, ",", expr mul_le_mul_of_nonneg_left, ",", expr le_of_lt C_pos, "]"]
  end }

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_bounded_bilinear_map_smul
{𝕜' : Type*}
[normed_field 𝕜']
[normed_algebra 𝕜 𝕜']
{E : Type*}
[normed_group E]
[normed_space 𝕜 E]
[normed_space 𝕜' E]
[is_scalar_tower 𝕜 𝕜' E] : is_bounded_bilinear_map 𝕜 (λ p : «expr × »(𝕜', E), «expr • »(p.1, p.2)) :=
{ add_left := add_smul,
  smul_left := λ c x y, by simp [] [] [] ["[", expr smul_assoc, "]"] [] [],
  add_right := smul_add,
  smul_right := λ c x y, by simp [] [] [] ["[", expr smul_assoc, ",", expr smul_algebra_smul_comm, "]"] [] [],
  bound := ⟨1, zero_lt_one, λ x y, by simp [] [] [] ["[", expr norm_smul, "]"] [] []⟩ }

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_bounded_bilinear_map_mul : is_bounded_bilinear_map 𝕜 (λ p : «expr × »(𝕜, 𝕜), «expr * »(p.1, p.2)) :=
by simp_rw ["<-", expr smul_eq_mul] []; exact [expr is_bounded_bilinear_map_smul]

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_bounded_bilinear_map_comp : is_bounded_bilinear_map 𝕜 (λ
 p : «expr × »(«expr →L[ ] »(E, 𝕜, F), «expr →L[ ] »(F, 𝕜, G)), p.2.comp p.1) :=
{ add_left := λ x₁ x₂ y, begin
    ext [] [ident z] [],
    change [expr «expr = »(y «expr + »(x₁ z, x₂ z), «expr + »(y (x₁ z), y (x₂ z)))] [] [],
    rw [expr y.map_add] []
  end,
  smul_left := λ c x y, begin
    ext [] [ident z] [],
    change [expr «expr = »(y «expr • »(c, x z), «expr • »(c, y (x z)))] [] [],
    rw [expr continuous_linear_map.map_smul] []
  end,
  add_right := λ x y₁ y₂, rfl,
  smul_right := λ c x y, rfl,
  bound := ⟨1, zero_lt_one, λ x y, calc
     «expr ≤ »(«expr∥ ∥»(continuous_linear_map.comp (x, y).snd (x, y).fst), «expr * »(«expr∥ ∥»(y), «expr∥ ∥»(x))) : continuous_linear_map.op_norm_comp_le _ _
     «expr = »(..., «expr * »(«expr * »(1, «expr∥ ∥»(x)), «expr∥ ∥»(y))) : by ring []⟩ }

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_linear_map.is_bounded_linear_map_comp_left
(g : «expr →L[ ] »(F, 𝕜, G)) : is_bounded_linear_map 𝕜 (λ f : «expr →L[ ] »(E, 𝕜, F), continuous_linear_map.comp g f) :=
is_bounded_bilinear_map_comp.is_bounded_linear_map_left _

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_linear_map.is_bounded_linear_map_comp_right
(f : «expr →L[ ] »(E, 𝕜, F)) : is_bounded_linear_map 𝕜 (λ g : «expr →L[ ] »(F, 𝕜, G), continuous_linear_map.comp g f) :=
is_bounded_bilinear_map_comp.is_bounded_linear_map_right _

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_bounded_bilinear_map_apply : is_bounded_bilinear_map 𝕜 (λ
 p : «expr × »(«expr →L[ ] »(E, 𝕜, F), E), p.1 p.2) :=
{ add_left := by simp [] [] [] [] [] [],
  smul_left := by simp [] [] [] [] [] [],
  add_right := by simp [] [] [] [] [] [],
  smul_right := by simp [] [] [] [] [] [],
  bound := ⟨1, zero_lt_one, by simp [] [] [] ["[", expr continuous_linear_map.le_op_norm, "]"] [] []⟩ }

/-- The function `continuous_linear_map.smul_right`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
theorem is_bounded_bilinear_map_smul_right :
  IsBoundedBilinearMap 𝕜 fun p => (ContinuousLinearMap.smulRight : (E →L[𝕜] 𝕜) → F → E →L[𝕜] F) p.1 p.2 :=
  { add_left :=
      fun m₁ m₂ f =>
        by 
          ext z 
          simp [add_smul],
    smul_left :=
      fun c m f =>
        by 
          ext z 
          simp [mul_smul],
    add_right :=
      fun m f₁ f₂ =>
        by 
          ext z 
          simp [smul_add],
    smulRight :=
      fun c m f =>
        by 
          ext z 
          simp [smul_smul, mul_commₓ],
    bound :=
      ⟨1, zero_lt_one,
        fun m f =>
          by 
            simp ⟩ }

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
theorem is_bounded_bilinear_map_comp_multilinear
{ι : Type*}
{E : ι → Type*}
[decidable_eq ι]
[fintype ι]
[∀ i, normed_group (E i)]
[∀
 i, normed_space 𝕜 (E i)] : is_bounded_bilinear_map 𝕜 (λ
 p : «expr × »(«expr →L[ ] »(F, 𝕜, G), continuous_multilinear_map 𝕜 E F), p.1.comp_continuous_multilinear_map p.2) :=
{ add_left := λ g₁ g₂ f, by { ext [] [ident m] [],
    refl },
  smul_left := λ c g f, by { ext [] [ident m] [],
    refl },
  add_right := λ g f₁ f₂, by { ext [] [ident m] [],
    simp [] [] [] [] [] [] },
  smul_right := λ c g f, by { ext [] [ident m] [],
    simp [] [] [] [] [] [] },
  bound := ⟨1, zero_lt_one, λ g f, begin
     apply [expr continuous_multilinear_map.op_norm_le_bound _ _ (λ m, _)],
     { apply_rules ["[", expr mul_nonneg, ",", expr zero_le_one, ",", expr norm_nonneg, "]"] },
     calc
       «expr ≤ »(«expr∥ ∥»(g (f m)), «expr * »(«expr∥ ∥»(g), «expr∥ ∥»(f m))) : g.le_op_norm _
       «expr ≤ »(..., «expr * »(«expr∥ ∥»(g), «expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr∥ ∥»(m i))))) : mul_le_mul_of_nonneg_left (f.le_op_norm _) (norm_nonneg _)
       «expr = »(..., «expr * »(«expr * »(«expr * »(1, «expr∥ ∥»(g)), «expr∥ ∥»(f)), «expr∏ , »((i), «expr∥ ∥»(m i)))) : by ring []
   end⟩ }

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `is_bounded_bilinear_map.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
``. -/
def IsBoundedBilinearMap.linearDeriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →ₗ[𝕜] G :=
  { toFun := fun q => f (p.1, q.2)+f (q.1, p.2),
    map_add' :=
      fun q₁ q₂ =>
        by 
          change (f (p.1, q₁.2+q₂.2)+f (q₁.1+q₂.1, p.2)) = (f (p.1, q₁.2)+f (q₁.1, p.2))+f (p.1, q₂.2)+f (q₂.1, p.2)
          simp [h.add_left, h.add_right]
          abel,
    map_smul' :=
      fun c q =>
        by 
          change (f (p.1, c • q.2)+f (c • q.1, p.2)) = c • f (p.1, q.2)+f (q.1, p.2)
          simp [h.smul_left, h.smul_right, smul_add] }

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`is_bounded_bilinear_map.has_fderiv_at` in `analysis.calculus.fderiv`. -/
def IsBoundedBilinearMap.deriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →L[𝕜] G :=
  (h.linear_deriv p).mkContinuousOfExistsBound$
    by 
      rcases h.bound with ⟨C, Cpos, hC⟩
      refine' ⟨(C*∥p.1∥)+C*∥p.2∥, fun q => _⟩
      calc ∥f (p.1, q.2)+f (q.1, p.2)∥ ≤ ((C*∥p.1∥)*∥q.2∥)+(C*∥q.1∥)*∥p.2∥ :=
        norm_add_le_of_le (hC _ _) (hC _ _)_ ≤ ((C*∥p.1∥)*∥q∥)+(C*∥q∥)*∥p.2∥ :=
        by 
          apply add_le_add 
          exact mul_le_mul_of_nonneg_left (le_max_rightₓ _ _) (mul_nonneg (le_of_ltₓ Cpos) (norm_nonneg _))
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (le_max_leftₓ _ _) (le_of_ltₓ Cpos)_ = ((C*∥p.1∥)+C*∥p.2∥)*∥q∥ :=
        by 
          ring

@[simp]
theorem is_bounded_bilinear_map_deriv_coe (h : IsBoundedBilinearMap 𝕜 f) (p q : E × F) :
  h.deriv p q = f (p.1, q.2)+f (q.1, p.2) :=
  rfl

variable(𝕜)

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The function `lmul_left_right : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded bilinear map. -/
theorem continuous_linear_map.lmul_left_right_is_bounded_bilinear
(𝕜' : Type*)
[normed_ring 𝕜']
[normed_algebra 𝕜 𝕜'] : is_bounded_bilinear_map 𝕜 (λ
 p : «expr × »(𝕜', 𝕜'), continuous_linear_map.lmul_left_right 𝕜 𝕜' p.1 p.2) :=
(continuous_linear_map.lmul_left_right 𝕜 𝕜').is_bounded_bilinear_map

variable{𝕜}

-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
theorem is_bounded_bilinear_map.is_bounded_linear_map_deriv
(h : is_bounded_bilinear_map 𝕜 f) : is_bounded_linear_map 𝕜 (λ p : «expr × »(E, F), h.deriv p) :=
begin
  rcases [expr h.bound, "with", "⟨", ident C, ",", ident Cpos, ":", expr «expr < »(0, C), ",", ident hC, "⟩"],
  refine [expr is_linear_map.with_bound ⟨λ p₁ p₂, _, λ c p, _⟩ «expr + »(C, C) (λ p, _)],
  { ext [] [] []; simp [] [] [] ["[", expr h.add_left, ",", expr h.add_right, "]"] [] []; abel [] [] [] },
  { ext [] [] []; simp [] [] [] ["[", expr h.smul_left, ",", expr h.smul_right, ",", expr smul_add, "]"] [] [] },
  { refine [expr continuous_linear_map.op_norm_le_bound _ (mul_nonneg (add_nonneg Cpos.le Cpos.le) (norm_nonneg _)) (λ
      q, _)],
    calc
      «expr ≤ »(«expr∥ ∥»(«expr + »(f (p.1, q.2), f (q.1, p.2))), «expr + »(«expr * »(«expr * »(C, «expr∥ ∥»(p.1)), «expr∥ ∥»(q.2)), «expr * »(«expr * »(C, «expr∥ ∥»(q.1)), «expr∥ ∥»(p.2)))) : norm_add_le_of_le (hC _ _) (hC _ _)
      «expr ≤ »(..., «expr + »(«expr * »(«expr * »(C, «expr∥ ∥»(p)), «expr∥ ∥»(q)), «expr * »(«expr * »(C, «expr∥ ∥»(q)), «expr∥ ∥»(p)))) : by apply_rules ["[", expr add_le_add, ",", expr mul_le_mul, ",", expr norm_nonneg, ",", expr Cpos.le, ",", expr le_refl, ",", expr le_max_left, ",", expr le_max_right, ",", expr mul_nonneg, "]"]
      «expr = »(..., «expr * »(«expr * »(«expr + »(C, C), «expr∥ ∥»(p)), «expr∥ ∥»(q))) : by ring [] }
end

end BilinearMap

namespace ContinuousLinearEquiv

open Set

/-!
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences between two Banach
spaces is an open subset of the space of linear maps between them.
-/


-- error in Analysis.NormedSpace.BoundedLinearMaps: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem is_open [complete_space E] : is_open (range (coe : «expr ≃L[ ] »(E, 𝕜, F) → «expr →L[ ] »(E, 𝕜, F))) :=
begin
  nontriviality [expr E] [],
  rw ["[", expr is_open_iff_mem_nhds, ",", expr forall_range_iff, "]"] [],
  refine [expr λ e, is_open.mem_nhds _ (mem_range_self _)],
  let [ident O] [":", expr «expr →L[ ] »(E, 𝕜, F) → «expr →L[ ] »(E, 𝕜, E)] [":=", expr λ
   f, (e.symm : «expr →L[ ] »(F, 𝕜, E)).comp f],
  have [ident h_O] [":", expr continuous O] [":=", expr is_bounded_bilinear_map_comp.continuous_left],
  convert [] [expr units.is_open.preimage h_O] ["using", 1],
  ext [] [ident f'] [],
  split,
  { rintros ["⟨", ident e', ",", ident rfl, "⟩"],
    exact [expr ⟨(e'.trans e.symm).to_unit, rfl⟩] },
  { rintros ["⟨", ident w, ",", ident hw, "⟩"],
    use [expr (units_equiv 𝕜 E w).trans e],
    ext [] [ident x] [],
    simp [] [] [] ["[", expr coe_fn_coe_base' w, ",", expr hw, "]"] [] [] }
end

protected theorem nhds [CompleteSpace E] (e : E ≃L[𝕜] F) : range (coeₓ : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (e : E →L[𝕜] F) :=
  IsOpen.mem_nhds ContinuousLinearEquiv.is_open
    (by 
      simp )

end ContinuousLinearEquiv

