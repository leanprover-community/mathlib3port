import Mathbin.Topology.ContinuousOn 
import Mathbin.GroupTheory.Submonoid.Operations 
import Mathbin.Algebra.Group.Prod 
import Mathbin.Algebra.Pointwise 
import Mathbin.Algebra.BigOperators.Finprod

/-!
# Theory of topological monoids

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/


universe u v

open Classical Set Filter TopologicalSpace

open_locale Classical TopologicalSpace BigOperators Pointwise

variable {ι α X M N : Type _} [TopologicalSpace X]

@[toAdditive]
theorem continuous_one [TopologicalSpace M] [HasOne M] : Continuous (1 : X → M) :=
  @continuous_const _ _ _ _ 1

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `add_monoid M` and `has_continuous_add M`. -/
class HasContinuousAdd (M : Type u) [TopologicalSpace M] [Add M] : Prop where 
  continuous_add : Continuous fun p : M × M => p.1+p.2

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `monoid M`
and `has_continuous_mul M`. -/
@[toAdditive]
class HasContinuousMul (M : Type u) [TopologicalSpace M] [Mul M] : Prop where 
  continuous_mul : Continuous fun p : M × M => p.1*p.2

section HasContinuousMul

variable [TopologicalSpace M] [Mul M] [HasContinuousMul M]

@[toAdditive]
theorem continuous_mul : Continuous fun p : M × M => p.1*p.2 :=
  HasContinuousMul.continuous_mul

@[continuity, toAdditive]
theorem Continuous.mul {f g : X → M} (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x*g x :=
  continuous_mul.comp (hf.prod_mk hg : _)

@[toAdditive]
theorem continuous_mul_left (a : M) : Continuous fun b : M => a*b :=
  continuous_const.mul continuous_id

@[toAdditive]
theorem continuous_mul_right (a : M) : Continuous fun b : M => b*a :=
  continuous_id.mul continuous_const

@[toAdditive]
theorem ContinuousOn.mul {f g : X → M} {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
  ContinuousOn (fun x => f x*g x) s :=
  (continuous_mul.comp_continuous_on (hf.prod hg) : _)

@[toAdditive]
theorem tendsto_mul {a b : M} : tendsto (fun p : M × M => p.fst*p.snd) (𝓝 (a, b)) (𝓝 (a*b)) :=
  continuous_iff_continuous_at.mp HasContinuousMul.continuous_mul (a, b)

@[toAdditive]
theorem Filter.Tendsto.mul {f g : α → M} {x : Filter α} {a b : M} (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (fun x => f x*g x) x (𝓝 (a*b)) :=
  tendsto_mul.comp (hf.prod_mk_nhds hg)

@[toAdditive]
theorem Filter.Tendsto.const_mul (b : M) {c : M} {f : α → M} {l : Filter α} (h : tendsto (fun k : α => f k) l (𝓝 c)) :
  tendsto (fun k : α => b*f k) l (𝓝 (b*c)) :=
  tendsto_const_nhds.mul h

@[toAdditive]
theorem Filter.Tendsto.mul_const (b : M) {c : M} {f : α → M} {l : Filter α} (h : tendsto (fun k : α => f k) l (𝓝 c)) :
  tendsto (fun k : α => f k*b) l (𝓝 (c*b)) :=
  h.mul tendsto_const_nhds

@[toAdditive]
theorem ContinuousAt.mul {f g : X → M} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
  ContinuousAt (fun x => f x*g x) x :=
  hf.mul hg

@[toAdditive]
theorem ContinuousWithinAt.mul {f g : X → M} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x)
  (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (fun x => f x*g x) s x :=
  hf.mul hg

@[toAdditive]
instance [TopologicalSpace N] [Mul N] [HasContinuousMul N] : HasContinuousMul (M × N) :=
  ⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk
      ((continuous_snd.comp continuous_fst).mul (continuous_snd.comp continuous_snd))⟩

@[toAdditive]
instance Pi.has_continuous_mul {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
  [∀ i, HasContinuousMul (C i)] : HasContinuousMul (∀ i, C i) :=
  { continuous_mul :=
      continuous_pi
        fun i => Continuous.mul ((continuous_apply i).comp continuous_fst) ((continuous_apply i).comp continuous_snd) }

/-- A version of `pi.has_continuous_mul` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_mul` for non-dependent functions. -/
@[toAdditive
      "A version of `pi.has_continuous_add` for non-dependent functions. It is needed\nbecause sometimes Lean fails to use `pi.has_continuous_add` for non-dependent functions."]
instance Pi.has_continuous_mul' : HasContinuousMul (ι → M) :=
  Pi.has_continuous_mul

@[toAdditive]
instance (priority := 100) has_continuous_mul_of_discrete_topology [TopologicalSpace N] [Mul N] [DiscreteTopology N] :
  HasContinuousMul N :=
  ⟨continuous_of_discrete_topology⟩

open_locale Filter

open Function

-- error in Topology.Algebra.Monoid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem has_continuous_mul.of_nhds_one
{M : Type u}
[monoid M]
[topological_space M]
(hmul : «expr $ »(tendsto (uncurry ((«expr * ») : M → M → M)) «expr ×ᶠ »(expr𝓝() 1, expr𝓝() 1), expr𝓝() 1))
(hleft : ∀ x₀ : M, «expr = »(expr𝓝() x₀, map (λ x, «expr * »(x₀, x)) (expr𝓝() 1)))
(hright : ∀ x₀ : M, «expr = »(expr𝓝() x₀, map (λ x, «expr * »(x, x₀)) (expr𝓝() 1))) : has_continuous_mul M :=
⟨begin
   rw [expr continuous_iff_continuous_at] [],
   rintros ["⟨", ident x₀, ",", ident y₀, "⟩"],
   have [ident key] [":", expr «expr = »(λ
     p : «expr × »(M, M), «expr * »(«expr * »(x₀, p.1), «expr * »(p.2, y₀)), «expr ∘ »(«expr ∘ »(λ
       x, «expr * »(x₀, x), λ x, «expr * »(x, y₀)), uncurry ((«expr * »))))] [],
   { ext [] [ident p] [],
     simp [] [] [] ["[", expr uncurry, ",", expr mul_assoc, "]"] [] [] },
   have [ident key₂] [":", expr «expr = »(«expr ∘ »(λ
      x, «expr * »(x₀, x), λ x, «expr * »(y₀, x)), λ x, «expr * »(«expr * »(x₀, y₀), x))] [],
   { ext [] [ident x] [],
     simp [] [] [] [] [] [] },
   calc
     «expr = »(map (uncurry ((«expr * »))) (expr𝓝() (x₀, y₀)), map (uncurry ((«expr * »))) «expr ×ᶠ »(expr𝓝() x₀, expr𝓝() y₀)) : by rw [expr nhds_prod_eq] []
     «expr = »(..., map (λ
       p : «expr × »(M, M), «expr * »(«expr * »(x₀, p.1), «expr * »(p.2, y₀))) «expr ×ᶠ »(expr𝓝() 1, expr𝓝() 1)) : by rw ["[", expr uncurry, ",", expr hleft x₀, ",", expr hright y₀, ",", expr prod_map_map_eq, ",", expr filter.map_map, "]"] []
     «expr = »(..., map «expr ∘ »(λ
       x, «expr * »(x₀, x), λ
       x, «expr * »(x, y₀)) (map (uncurry ((«expr * »))) «expr ×ᶠ »(expr𝓝() 1, expr𝓝() 1))) : by { rw ["[", expr key, ",", "<-", expr filter.map_map, "]"] [] }
     «expr ≤ »(..., map «expr ∘ »(λ x : M, «expr * »(x₀, x), λ x, «expr * »(x, y₀)) (expr𝓝() 1)) : map_mono hmul
     «expr = »(..., expr𝓝() «expr * »(x₀, y₀)) : by rw ["[", "<-", expr filter.map_map, ",", "<-", expr hright, ",", expr hleft y₀, ",", expr filter.map_map, ",", expr key₂, ",", "<-", expr hleft, "]"] []
 end⟩

@[toAdditive]
theorem has_continuous_mul_of_comm_of_nhds_one (M : Type u) [CommMonoidₓ M] [TopologicalSpace M]
  (hmul : tendsto (uncurry (·*· : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1)) (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀*x) (𝓝 1)) :
  HasContinuousMul M :=
  by 
    apply HasContinuousMul.of_nhds_one hmul hleft 
    intro x₀ 
    simpRw [mul_commₓ, hleft x₀]

end HasContinuousMul

namespace Submonoid

@[toAdditive]
instance [TopologicalSpace α] [Monoidₓ α] [HasContinuousMul α] (S : Submonoid α) : HasContinuousMul S :=
  { continuous_mul :=
      by 
        rw [embedding_subtype_coe.to_inducing.continuous_iff]
        exact (continuous_subtype_coe.comp continuous_fst).mul (continuous_subtype_coe.comp continuous_snd) }

end Submonoid

section HasContinuousMul

variable [TopologicalSpace M] [Monoidₓ M] [HasContinuousMul M]

@[toAdditive]
theorem Submonoid.top_closure_mul_self_subset (s : Submonoid M) :
  (Closure (s : Set M)*Closure (s : Set M)) ⊆ Closure (s : Set M) :=
  calc (Closure (s : Set M)*Closure (s : Set M)) = (fun p : M × M => p.1*p.2) '' Closure ((s : Set M).Prod s) :=
    by 
      simp [closure_prod_eq]
    _ ⊆ Closure ((fun p : M × M => p.1*p.2) '' (s : Set M).Prod s) := image_closure_subset_closure_image continuous_mul 
    _ = Closure s :=
    by 
      simp [s.coe_mul_self_eq]
    

@[toAdditive]
theorem Submonoid.top_closure_mul_self_eq (s : Submonoid M) :
  (Closure (s : Set M)*Closure (s : Set M)) = Closure (s : Set M) :=
  subset.antisymm s.top_closure_mul_self_subset fun x hx => ⟨x, 1, hx, subset_closure s.one_mem, mul_oneₓ _⟩

/-- The (topological-space) closure of a submonoid of a space `M` with `has_continuous_mul` is
itself a submonoid. -/
@[toAdditive
      "The (topological-space) closure of an additive submonoid of a space `M` with\n`has_continuous_add` is itself an additive submonoid."]
def Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M :=
  { Carrier := Closure (s : Set M), one_mem' := subset_closure s.one_mem,
    mul_mem' := fun a b ha hb => s.top_closure_mul_self_subset ⟨a, b, ha, hb, rfl⟩ }

@[toAdditive]
instance Submonoid.topological_closure_has_continuous_mul (s : Submonoid M) : HasContinuousMul s.topological_closure :=
  { continuous_mul :=
      by 
        apply continuous_induced_rng 
        change Continuous fun p : s.topological_closure × s.topological_closure => (p.1 : M)*(p.2 : M)
        continuity }

theorem Submonoid.submonoid_topological_closure (s : Submonoid M) : s ≤ s.topological_closure :=
  subset_closure

theorem Submonoid.is_closed_topological_closure (s : Submonoid M) : IsClosed (s.topological_closure : Set M) :=
  by 
    convert is_closed_closure

theorem Submonoid.topological_closure_minimal (s : Submonoid M) {t : Submonoid M} (h : s ≤ t)
  (ht : IsClosed (t : Set M)) : s.topological_closure ≤ t :=
  closure_minimal h ht

@[toAdditive exists_open_nhds_zero_half]
theorem exists_open_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
  ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ ∀ v _ : v ∈ V w _ : w ∈ V, (v*w) ∈ s :=
  have  : (fun a : M × M => a.1*a.2) ⁻¹' s ∈ 𝓝 ((1, 1) : M × M) :=
    tendsto_mul
      (by 
        simpa only [one_mulₓ] using hs)
  by 
    simpa only [prod_subset_iff] using exists_nhds_square this

@[toAdditive exists_nhds_zero_half]
theorem exists_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
  ∃ (V : _)(_ : V ∈ 𝓝 (1 : M)), ∀ v _ : v ∈ V w _ : w ∈ V, (v*w) ∈ s :=
  let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩

@[toAdditive exists_nhds_zero_quarter]
theorem exists_nhds_one_split4 {u : Set M} (hu : u ∈ 𝓝 (1 : M)) :
  ∃ (V : _)(_ : V ∈ 𝓝 (1 : M)), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → (((v*w)*s)*t) ∈ u :=
  by 
    rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
    rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
    use V, V1 
    intro v w s t v_in w_in s_in t_in 
    simpa only [mul_assocₓ] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `VV ⊆ U`. -/
@[toAdditive "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`\n  such that `V + V ⊆ U`."]
theorem exists_open_nhds_one_mul_subset {U : Set M} (hU : U ∈ 𝓝 (1 : M)) :
  ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ (V*V) ⊆ U :=
  by 
    rcases exists_open_nhds_one_split hU with ⟨V, Vo, V1, hV⟩
    use V, Vo, V1 
    rintro _ ⟨x, y, hx, hy, rfl⟩
    exact hV _ hx _ hy

@[toAdditive]
theorem tendsto_list_prod {f : ι → α → M} {x : Filter α} {a : ι → M} :
  ∀ l : List ι,
    (∀ i _ : i ∈ l, tendsto (f i) x (𝓝 (a i))) → tendsto (fun b => (l.map fun c => f c b).Prod) x (𝓝 (l.map a).Prod)
| [], _ =>
  by 
    simp [tendsto_const_nhds]
| f :: l, h =>
  by 
    simp only [List.map_consₓ, List.prod_cons]
    exact (h f (List.mem_cons_selfₓ _ _)).mul (tendsto_list_prod l fun c hc => h c (List.mem_cons_of_memₓ _ hc))

@[toAdditive]
theorem continuous_list_prod {f : ι → X → M} (l : List ι) (h : ∀ i _ : i ∈ l, Continuous (f i)) :
  Continuous fun a => (l.map fun i => f i a).Prod :=
  continuous_iff_continuous_at.2$ fun x => tendsto_list_prod l$ fun c hc => continuous_iff_continuous_at.1 (h c hc) x

@[continuity]
theorem continuous_pow : ∀ n : ℕ, Continuous fun a : M => a ^ n
| 0 =>
  by 
    simpa using continuous_const
| k+1 =>
  by 
    simp only [pow_succₓ]
    exact continuous_id.mul (continuous_pow _)

@[continuity]
theorem Continuous.pow {f : X → M} (h : Continuous f) (n : ℕ) : Continuous fun b => f b ^ n :=
  (continuous_pow n).comp h

theorem continuous_on_pow {s : Set M} (n : ℕ) : ContinuousOn (fun x => x ^ n) s :=
  (continuous_pow n).ContinuousOn

theorem continuous_at_pow (x : M) (n : ℕ) : ContinuousAt (fun x => x ^ n) x :=
  (continuous_pow n).ContinuousAt

theorem Filter.Tendsto.pow {l : Filter α} {f : α → M} {x : M} (hf : tendsto f l (𝓝 x)) (n : ℕ) :
  tendsto (fun x => f x ^ n) l (𝓝 (x ^ n)) :=
  (continuous_at_pow _ _).Tendsto.comp hf

theorem ContinuousWithinAt.pow {f : X → M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x) (n : ℕ) :
  ContinuousWithinAt (fun x => f x ^ n) s x :=
  hf.pow n

theorem ContinuousAt.pow {f : X → M} {x : X} (hf : ContinuousAt f x) (n : ℕ) : ContinuousAt (fun x => f x ^ n) x :=
  hf.pow n

theorem ContinuousOn.pow {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) : ContinuousOn (fun x => f x ^ n) s :=
  fun x hx => (hf x hx).pow n

end HasContinuousMul

section Op

open MulOpposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
instance [_i : TopologicalSpace α] : TopologicalSpace («expr ᵐᵒᵖ» α) :=
  TopologicalSpace.induced (unop : «expr ᵐᵒᵖ» α → α) _i

variable [TopologicalSpace α]

theorem continuous_unop : Continuous (unop : «expr ᵐᵒᵖ» α → α) :=
  continuous_induced_dom

theorem continuous_op : Continuous (op : α → «expr ᵐᵒᵖ» α) :=
  continuous_induced_rng continuous_id

variable [Monoidₓ α] [HasContinuousMul α]

/-- If multiplication is continuous in the monoid `α`, then it also is in the monoid `αᵐᵒᵖ`. -/
instance : HasContinuousMul («expr ᵐᵒᵖ» α) :=
  ⟨let h₁ := @continuous_mul α _ _ _ 
    let h₂ : Continuous fun p : α × α => _ := continuous_snd.prod_mk continuous_fst 
    continuous_induced_rng$ (h₁.comp h₂).comp (continuous_unop.prod_map continuous_unop)⟩

end Op

namespace Units

open MulOpposite

variable [TopologicalSpace α] [Monoidₓ α]

/-- The units of a monoid are equipped with a topology, via the embedding into `α × α`. -/
instance : TopologicalSpace (Units α) :=
  TopologicalSpace.induced (embedProduct α)
    (by 
      infer_instance)

theorem continuous_embed_product : Continuous (embedProduct α) :=
  continuous_induced_dom

theorem continuous_coe : Continuous (coeₓ : Units α → α) :=
  by 
    convert continuous_fst.comp continuous_induced_dom

variable [HasContinuousMul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `topology.algebra.group`,
because the predicate `has_continuous_inv` has not yet been defined. -/
instance : HasContinuousMul (Units α) :=
  ⟨let h := @continuous_mul (α × «expr ᵐᵒᵖ» α) _ _ _ 
    continuous_induced_rng$ h.comp$ continuous_embed_product.prod_map continuous_embed_product⟩

end Units

section 

variable [TopologicalSpace M] [CommMonoidₓ M]

@[toAdditive]
theorem Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) : (S : Set M) ∈ 𝓝 (1 : M) :=
  IsOpen.mem_nhds oS S.one_mem

variable [HasContinuousMul M]

@[toAdditive]
theorem tendsto_multiset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Multiset ι) :
  (∀ i _ : i ∈ s, tendsto (f i) x (𝓝 (a i))) → tendsto (fun b => (s.map fun c => f c b).Prod) x (𝓝 (s.map a).Prod) :=
  by 
    rcases s with ⟨l⟩
    simpa using tendsto_list_prod l

@[toAdditive]
theorem tendsto_finset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
  (∀ i _ : i ∈ s, tendsto (f i) x (𝓝 (a i))) → tendsto (fun b => ∏c in s, f c b) x (𝓝 (∏c in s, a c)) :=
  tendsto_multiset_prod _

@[continuity, toAdditive]
theorem continuous_multiset_prod {f : ι → X → M} (s : Multiset ι) :
  (∀ i _ : i ∈ s, Continuous (f i)) → Continuous fun a => (s.map fun i => f i a).Prod :=
  by 
    rcases s with ⟨l⟩
    simpa using continuous_list_prod l

@[continuity, toAdditive]
theorem continuous_finset_prod {f : ι → X → M} (s : Finset ι) :
  (∀ i _ : i ∈ s, Continuous (f i)) → Continuous fun a => ∏i in s, f i a :=
  continuous_multiset_prod _

open Function

-- error in Topology.Algebra.Monoid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem continuous_finprod
{f : ι → X → M}
(hc : ∀ i, continuous (f i))
(hf : locally_finite (λ i, mul_support (f i))) : continuous (λ x, «expr∏ᶠ , »((i), f i x)) :=
begin
  refine [expr continuous_iff_continuous_at.2 (λ x, _)],
  rcases [expr hf x, "with", "⟨", ident U, ",", ident hxU, ",", ident hUf, "⟩"],
  have [] [":", expr continuous_at (λ x, «expr∏ in , »((i), hUf.to_finset, f i x)) x] [],
  from [expr tendsto_finset_prod _ (λ i hi, (hc i).continuous_at)],
  refine [expr this.congr «expr $ »(mem_of_superset hxU, λ y hy, _)],
  refine [expr (finprod_eq_prod_of_mul_support_subset _ (λ i hi, _)).symm],
  rw ["[", expr hUf.coe_to_finset, "]"] [],
  exact [expr ⟨y, hi, hy⟩]
end

@[toAdditive]
theorem continuous_finprod_cond {f : ι → X → M} {p : ι → Prop} (hc : ∀ i, p i → Continuous (f i))
  (hf : LocallyFinite fun i => mul_support (f i)) : Continuous fun x => ∏ᶠ(i : _)(hi : p i), f i x :=
  by 
    simp only [←finprod_subtype_eq_finprod_cond]
    exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

end 

instance Additive.has_continuous_add {M} [h : TopologicalSpace M] [Mul M] [HasContinuousMul M] :
  @HasContinuousAdd (Additive M) h _ :=
  { continuous_add := @continuous_mul M _ _ _ }

instance Multiplicative.has_continuous_mul {M} [h : TopologicalSpace M] [Add M] [HasContinuousAdd M] :
  @HasContinuousMul (Multiplicative M) h _ :=
  { continuous_mul := @continuous_add M _ _ _ }

