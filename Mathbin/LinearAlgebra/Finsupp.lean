import Mathbin.Data.Finsupp.Basic 
import Mathbin.LinearAlgebra.Pi

/-!
# Properties of the module `α →₀ M`

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`data.finsupp.basic`.

In this file we define `finsupp.supported s` to be the set `{f : α →₀ M | f.support ⊆ s}`
interpreted as a submodule of `α →₀ M`. We also define `linear_map` versions of various maps:

* `finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `finsupp.single a` as a linear map;

* `finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `λ f, f a` as a linear map;

* `finsupp.lsubtype_domain (s : set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;

* `finsupp.restrict_dom`: `finsupp.filter` as a linear map to `finsupp.supported s`;

* `finsupp.lsum`: `finsupp.sum` or `finsupp.lift_add_hom` as a `linear_map`;

* `finsupp.total α M R (v : ι → M)`: sends `l : ι → R` to the linear combination of `v i` with
  coefficients `l i`;

* `finsupp.total_on`: a restricted version of `finsupp.total` with domain `finsupp.supported R R s`
  and codomain `submodule.span R (v '' s)`;

* `finsupp.supported_equiv_finsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;

* `finsupp.lmap_domain`: a linear map version of `finsupp.map_domain`;

* `finsupp.dom_lcongr`: a `linear_equiv` version of `finsupp.dom_congr`;

* `finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;

* `finsupp.lcongr`: a `linear_equiv`alence between `α →₀ M` and `β →₀ N` constructed using `e : α ≃
  β` and `e' : M ≃ₗ[R] N`.

## Tags

function with finite support, module, linear algebra
-/


noncomputable theory

open Set LinearMap Submodule

open_locale Classical BigOperators

namespace Finsupp

variable {α : Type _} {M : Type _} {N : Type _} {P : Type _} {R : Type _} {S : Type _}

variable [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ M] [Module R M]

variable [AddCommMonoidₓ N] [Module R N]

variable [AddCommMonoidₓ P] [Module R P]

/-- Interpret `finsupp.single a` as a linear map. -/
def lsingle (a : α) : M →ₗ[R] α →₀ M :=
  { Finsupp.singleAddHom a with map_smul' := fun a b => (smul_single _ _ _).symm }

/-- Two `R`-linear maps from `finsupp X M` which agree on each `single x y` agree everywhere. -/
theorem lhom_ext ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
  LinearMap.to_add_monoid_hom_injective$ add_hom_ext h

/-- Two `R`-linear maps from `finsupp X M` which agree on each `single x y` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext]
theorem lhom_ext' ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ :=
  lhom_ext$ fun a => LinearMap.congr_fun (h a)

/-- Interpret `λ (f : α →₀ M), f a` as a linear map. -/
def lapply (a : α) : (α →₀ M) →ₗ[R] M :=
  { Finsupp.applyAddHom a with map_smul' := fun a b => rfl }

section LsubtypeDomain

variable (s : Set α)

/-- Interpret `finsupp.subtype_domain s` as a linear map. -/
def lsubtype_domain : (α →₀ M) →ₗ[R] s →₀ M :=
  { toFun := subtype_domain fun x => x ∈ s, map_add' := fun a b => subtype_domain_add,
    map_smul' := fun c a => ext$ fun a => rfl }

theorem lsubtype_domain_apply (f : α →₀ M) :
  (lsubtype_domain s : (α →₀ M) →ₗ[R] s →₀ M) f = subtype_domain (fun x => x ∈ s) f :=
  rfl

end LsubtypeDomain

@[simp]
theorem lsingle_apply (a : α) (b : M) : (lsingle a : M →ₗ[R] α →₀ M) b = single a b :=
  rfl

@[simp]
theorem lapply_apply (a : α) (f : α →₀ M) : (lapply a : (α →₀ M) →ₗ[R] M) f = f a :=
  rfl

@[simp]
theorem ker_lsingle (a : α) : (lsingle a : M →ₗ[R] α →₀ M).ker = ⊥ :=
  ker_eq_bot_of_injective (single_injective a)

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lsingle_range_le_ker_lapply
(s t : set α)
(h : disjoint s t) : «expr ≤ »(«expr⨆ , »((a «expr ∈ » s), (lsingle a : «expr →ₗ[ ] »(M, R, «expr →₀ »(α, M))).range), «expr⨅ , »((a «expr ∈ » t), ker (lapply a))) :=
begin
  refine [expr supr_le (assume a₁, «expr $ »(supr_le, assume h₁, range_le_iff_comap.2 _))],
  simp [] [] ["only"] ["[", expr (ker_comp _ _).symm, ",", expr eq_top_iff, ",", expr set_like.le_def, ",", expr mem_ker, ",", expr comap_infi, ",", expr mem_infi, "]"] [] [],
  assume [binders (b hb a₂ h₂)],
  have [] [":", expr «expr ≠ »(a₁, a₂)] [":=", expr assume eq, h ⟨h₁, «expr ▸ »(eq.symm, h₂)⟩],
  exact [expr single_eq_of_ne this]
end

theorem infi_ker_lapply_le_bot : (⨅a, ker (lapply a : (α →₀ M) →ₗ[R] M)) ≤ ⊥ :=
  by 
    simp only [SetLike.le_def, mem_infi, mem_ker, mem_bot, lapply_apply]
    exact fun a h => Finsupp.ext h

theorem supr_lsingle_range : (⨆a, (lsingle a : M →ₗ[R] α →₀ M).range) = ⊤ :=
  by 
    refine' eq_top_iff.2$ SetLike.le_def.2$ fun f _ => _ 
    rw [←sum_single f]
    exact sum_mem _ fun a ha => Submodule.mem_supr_of_mem a ⟨_, rfl⟩

theorem disjoint_lsingle_lsingle (s t : Set α) (hs : Disjoint s t) :
  Disjoint (⨆(a : _)(_ : a ∈ s), (lsingle a : M →ₗ[R] α →₀ M).range) (⨆(a : _)(_ : a ∈ t), (lsingle a).range) :=
  by 
    refine'
      Disjoint.mono (lsingle_range_le_ker_lapply _ _$ disjoint_compl_right)
        (lsingle_range_le_ker_lapply _ _$ disjoint_compl_right) (le_transₓ (le_infi$ fun i => _) infi_ker_lapply_le_bot)
    classical 
    byCases' his : i ∈ s
    ·
      byCases' hit : i ∈ t
      ·
        exact (hs ⟨his, hit⟩).elim 
      exact inf_le_of_right_le (infi_le_of_le i$ infi_le _ hit)
    exact inf_le_of_left_le (infi_le_of_le i$ infi_le _ his)

theorem span_single_image (s : Set M) (a : α) :
  Submodule.span R (single a '' s) = (Submodule.span R s).map (lsingle a) :=
  by 
    rw [←span_image] <;> rfl

variable (M R)

/-- `finsupp.supported M R s` is the `R`-submodule of all `p : α →₀ M` such that `p.support ⊆ s`. -/
def supported (s : Set α) : Submodule R (α →₀ M) :=
  by 
    refine' ⟨{ p | «expr↑ » p.support ⊆ s }, _, _, _⟩
    ·
      simp only [subset_def, Finset.mem_coe, Set.mem_set_of_eq, mem_support_iff, zero_apply]
      intro h ha 
      exact (ha rfl).elim
    ·
      intro p q hp hq 
      refine' subset.trans (subset.trans (Finset.coe_subset.2 support_add) _) (union_subset hp hq)
      rw [Finset.coe_union]
    ·
      intro a p hp 
      refine' subset.trans (Finset.coe_subset.2 support_smul) hp

variable {M}

theorem mem_supported {s : Set α} (p : α →₀ M) : p ∈ supported M R s ↔ «expr↑ » p.support ⊆ s :=
  Iff.rfl

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_supported'
{s : set α}
(p : «expr →₀ »(α, M)) : «expr ↔ »(«expr ∈ »(p, supported M R s), ∀ x «expr ∉ » s, «expr = »(p x, 0)) :=
by haveI [] [] [":=", expr classical.dec_pred (λ
  x : α, «expr ∈ »(x, s))]; simp [] [] [] ["[", expr mem_supported, ",", expr set.subset_def, ",", expr not_imp_comm, "]"] [] []

theorem mem_supported_support (p : α →₀ M) : p ∈ Finsupp.supported M R (p.support : Set α) :=
  by 
    rw [Finsupp.mem_supported]

theorem single_mem_supported {s : Set α} {a : α} (b : M) (h : a ∈ s) : single a b ∈ supported M R s :=
  Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)

theorem supported_eq_span_single (s : Set α) : supported R R s = span R ((fun i => single i 1) '' s) :=
  by 
    refine' (span_eq_of_le _ _ (SetLike.le_def.2$ fun l hl => _)).symm
    ·
      rintro _ ⟨_, hp, rfl⟩
      exact single_mem_supported R 1 hp
    ·
      rw [←l.sum_single]
      refine' sum_mem _ fun i il => _ 
      convert @smul_mem R (α →₀ R) _ _ _ _ (single i 1) (l i) _
      ·
        simp 
      apply subset_span 
      apply Set.mem_image_of_mem _ (hl il)

variable (M R)

/-- Interpret `finsupp.filter s` as a linear map from `α →₀ M` to `supported M R s`. -/
def restrict_dom (s : Set α) : (α →₀ M) →ₗ[R] supported M R s :=
  LinearMap.codRestrict _
    { toFun := filter (· ∈ s), map_add' := fun l₁ l₂ => filter_add, map_smul' := fun a l => filter_smul }
    fun l => (mem_supported' _ _).2$ fun x => filter_apply_neg (· ∈ s) l

variable {M R}

section 

@[simp]
theorem restrict_dom_apply (s : Set α) (l : α →₀ M) :
  ((restrict_dom M R s : (α →₀ M) →ₗ[R] supported M R s) l : α →₀ M) = Finsupp.filter (· ∈ s) l :=
  rfl

end 

theorem restrict_dom_comp_subtype (s : Set α) : (restrict_dom M R s).comp (Submodule.subtype _) = LinearMap.id :=
  by 
    ext l a 
    byCases' a ∈ s <;> simp [h]
    exact ((mem_supported' R l.1).1 l.2 a h).symm

theorem range_restrict_dom (s : Set α) : (restrict_dom M R s).range = ⊤ :=
  range_eq_top.2$ Function.RightInverse.surjective$ LinearMap.congr_fun (restrict_dom_comp_subtype s)

theorem supported_mono {s t : Set α} (st : s ⊆ t) : supported M R s ≤ supported M R t :=
  fun l h => Set.Subset.trans h st

@[simp]
theorem supported_empty : supported M R (∅ : Set α) = ⊥ :=
  eq_bot_iff.2$
    fun l h =>
      (Submodule.mem_bot R).2$
        by 
          ext <;> simp_all [mem_supported']

@[simp]
theorem supported_univ : supported M R (Set.Univ : Set α) = ⊤ :=
  eq_top_iff.2$ fun l _ => Set.subset_univ _

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem supported_Union
{δ : Type*}
(s : δ → set α) : «expr = »(supported M R «expr⋃ , »((i), s i), «expr⨆ , »((i), supported M R (s i))) :=
begin
  refine [expr le_antisymm _ «expr $ »(supr_le, λ i, «expr $ »(supported_mono, set.subset_Union _ _))],
  haveI [] [] [":=", expr classical.dec_pred (λ x, «expr ∈ »(x, «expr⋃ , »((i), s i)))],
  suffices [] [":", expr «expr ≤ »(((submodule.subtype _).comp (restrict_dom M R «expr⋃ , »((i), s i))).range, «expr⨆ , »((i), supported M R (s i)))],
  { rwa ["[", expr linear_map.range_comp, ",", expr range_restrict_dom, ",", expr map_top, ",", expr range_subtype, "]"] ["at", ident this] },
  rw ["[", expr range_le_iff_comap, ",", expr eq_top_iff, "]"] [],
  rintro [ident l, "⟨", "⟩"],
  apply [expr finsupp.induction l],
  { exact [expr zero_mem _] },
  refine [expr λ x a l hl a0, add_mem _ _],
  by_cases [expr «expr∃ , »((i), «expr ∈ »(x, s i))]; simp [] [] [] ["[", expr h, "]"] [] [],
  { cases [expr h] ["with", ident i, ident hi],
    exact [expr le_supr (λ i, supported M R (s i)) i (single_mem_supported R _ hi)] }
end

theorem supported_union (s t : Set α) : supported M R (s ∪ t) = supported M R s⊔supported M R t :=
  by 
    erw [Set.union_eq_Union, supported_Union, supr_bool_eq] <;> rfl

theorem supported_Inter {ι : Type _} (s : ι → Set α) : supported M R (⋂i, s i) = ⨅i, supported M R (s i) :=
  Submodule.ext$
    fun x =>
      by 
        simp [mem_supported, subset_Inter_iff]

theorem supported_inter (s t : Set α) : supported M R (s ∩ t) = supported M R s⊓supported M R t :=
  by 
    rw [Set.inter_eq_Inter, supported_Inter, infi_bool_eq] <;> rfl

theorem disjoint_supported_supported {s t : Set α} (h : Disjoint s t) : Disjoint (supported M R s) (supported M R t) :=
  disjoint_iff.2$
    by 
      rw [←supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem disjoint_supported_supported_iff
[nontrivial M]
{s t : set α} : «expr ↔ »(disjoint (supported M R s) (supported M R t), disjoint s t) :=
begin
  refine [expr ⟨λ h x hx, _, disjoint_supported_supported⟩],
  rcases [expr exists_ne (0 : M), "with", "⟨", ident y, ",", ident hy, "⟩"],
  have [] [] [":=", expr h ⟨single_mem_supported R y hx.1, single_mem_supported R y hx.2⟩],
  rw ["[", expr mem_bot, ",", expr single_eq_zero, "]"] ["at", ident this],
  exact [expr hy this]
end

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Interpret `finsupp.restrict_support_equiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
def supported_equiv_finsupp (s : set α) : «expr ≃ₗ[ ] »(supported M R s, R, «expr →₀ »(s, M)) :=
begin
  let [ident F] [":", expr «expr ≃ »(supported M R s, «expr →₀ »(s, M))] [":=", expr restrict_support_equiv s M],
  refine [expr F.to_linear_equiv _],
  have [] [":", expr «expr = »((F : supported M R s → «expr →₀ »(«expr↥ »(s), M)), (lsubtype_domain s : «expr →ₗ[ ] »(«expr →₀ »(α, M), R, «expr →₀ »(s, M))).comp (submodule.subtype (supported M R s)))] [":=", expr rfl],
  rw [expr this] [],
  exact [expr linear_map.is_linear _]
end

section Lsum

variable (S) [Module S N] [SmulCommClass R S N]

/-- Lift a family of linear maps `M →ₗ[R] N` indexed by `x : α` to a linear map from `α →₀ M` to
`N` using `finsupp.sum`. This is an upgraded version of `finsupp.lift_add_hom`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
def lsum : (α → M →ₗ[R] N) ≃ₗ[S] (α →₀ M) →ₗ[R] N :=
  { toFun :=
      fun F =>
        { toFun := fun d => d.sum fun i => F i, map_add' := (lift_add_hom fun x => (F x).toAddMonoidHom).map_add,
          map_smul' :=
            fun c f =>
              by 
                simp [sum_smul_index', smul_sum] },
    invFun := fun F x => F.comp (lsingle x),
    left_inv :=
      fun F =>
        by 
          ext x y 
          simp ,
    right_inv :=
      fun F =>
        by 
          ext x y 
          simp ,
    map_add' :=
      fun F G =>
        by 
          ext x y 
          simp ,
    map_smul' :=
      fun F G =>
        by 
          ext x y 
          simp  }

@[simp]
theorem coe_lsum (f : α → M →ₗ[R] N) : (lsum S f : (α →₀ M) → N) = fun d => d.sum fun i => f i :=
  rfl

theorem lsum_apply (f : α → M →ₗ[R] N) (l : α →₀ M) : Finsupp.lsum S f l = l.sum fun b => f b :=
  rfl

theorem lsum_single (f : α → M →ₗ[R] N) (i : α) (m : M) : Finsupp.lsum S f (Finsupp.single i m) = f i m :=
  Finsupp.sum_single_index (f i).map_zero

theorem lsum_symm_apply (f : (α →₀ M) →ₗ[R] N) (x : α) : (lsum S).symm f x = f.comp (lsingle x) :=
  rfl

end Lsum

section 

variable (M) (R) (X : Type _)

/--
A slight rearrangement from `lsum` gives us
the bijection underlying the free-forgetful adjunction for R-modules.
-/
noncomputable def lift : (X → M) ≃+ ((X →₀ R) →ₗ[R] M) :=
  (AddEquiv.arrowCongr (Equiv.refl X) (ring_lmap_equiv_self R ℕ M).toAddEquiv.symm).trans
    (lsum _ : _ ≃ₗ[ℕ] _).toAddEquiv

@[simp]
theorem lift_symm_apply f x : ((lift M R X).symm f) x = f (single x 1) :=
  rfl

@[simp]
theorem lift_apply f g : ((lift M R X) f) g = g.sum fun x r => r • f x :=
  rfl

end 

section LmapDomain

variable {α' : Type _} {α'' : Type _} (M R)

/-- Interpret `finsupp.map_domain` as a linear map. -/
def lmap_domain (f : α → α') : (α →₀ M) →ₗ[R] α' →₀ M :=
  { toFun := map_domain f, map_add' := fun a b => map_domain_add, map_smul' := map_domain_smul }

@[simp]
theorem lmap_domain_apply (f : α → α') (l : α →₀ M) : (lmap_domain M R f : (α →₀ M) →ₗ[R] α' →₀ M) l = map_domain f l :=
  rfl

@[simp]
theorem lmap_domain_id : (lmap_domain M R id : (α →₀ M) →ₗ[R] α →₀ M) = LinearMap.id :=
  LinearMap.ext$ fun l => map_domain_id

theorem lmap_domain_comp (f : α → α') (g : α' → α'') :
  lmap_domain M R (g ∘ f) = (lmap_domain M R g).comp (lmap_domain M R f) :=
  LinearMap.ext$ fun l => map_domain_comp

theorem supported_comap_lmap_domain (f : α → α') (s : Set α') :
  supported M R (f ⁻¹' s) ≤ (supported M R s).comap (lmap_domain M R f) :=
  fun l hl : «expr↑ » l.support ⊆ f ⁻¹' s =>
    show «expr↑ » (map_domain f l).Support ⊆ s by 
      rw [←Set.image_subset_iff, ←Finset.coe_image] at hl 
      exact Set.Subset.trans map_domain_support hl

theorem lmap_domain_supported [Nonempty α] (f : α → α') (s : Set α) :
  (supported M R s).map (lmap_domain M R f) = supported M R (f '' s) :=
  by 
    inhabit α 
    refine'
      le_antisymmₓ
        (map_le_iff_le_comap.2$
          le_transₓ (supported_mono$ Set.subset_preimage_image _ _) (supported_comap_lmap_domain _ _ _ _))
        _ 
    intro l hl 
    refine' ⟨(lmap_domain M R (Function.invFunOn f s) : (α' →₀ M) →ₗ[R] α →₀ M) l, fun x hx => _, _⟩
    ·
      rcases Finset.mem_image.1 (map_domain_support hx) with ⟨c, hc, rfl⟩
      exact
        Function.inv_fun_on_memₓ
          (by 
            simpa using hl hc)
    ·
      rw [←LinearMap.comp_apply, ←lmap_domain_comp]
      refine' (map_domain_congr$ fun c hc => _).trans map_domain_id 
      exact
        Function.inv_fun_on_eqₓ
          (by 
            simpa using hl hc)

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lmap_domain_disjoint_ker
(f : α → α')
{s : set α}
(H : ∀ a b «expr ∈ » s, «expr = »(f a, f b) → «expr = »(a, b)) : disjoint (supported M R s) (lmap_domain M R f).ker :=
begin
  rintro [ident l, "⟨", ident h₁, ",", ident h₂, "⟩"],
  rw ["[", expr set_like.mem_coe, ",", expr mem_ker, ",", expr lmap_domain_apply, ",", expr map_domain, "]"] ["at", ident h₂],
  simp [] [] [] [] [] [],
  ext [] [ident x] [],
  haveI [] [] [":=", expr classical.dec_pred (λ x, «expr ∈ »(x, s))],
  by_cases [expr xs, ":", expr «expr ∈ »(x, s)],
  { have [] [":", expr «expr = »(finsupp.sum l (λ a, finsupp.single (f a)) (f x), 0)] [],
    { rw [expr h₂] [],
      refl },
    rw ["[", expr finsupp.sum_apply, ",", expr finsupp.sum, ",", expr finset.sum_eq_single x, "]"] ["at", ident this],
    { simpa [] [] [] ["[", expr finsupp.single_apply, "]"] [] [] },
    { intros [ident y, ident hy, ident xy],
      simp [] [] [] ["[", expr mt (H _ _ (h₁ hy) xs) xy, "]"] [] [] },
    { simp [] [] [] [] [] [] { contextual := tt } } },
  { by_contra [ident h],
    exact [expr xs «expr $ »(h₁, finsupp.mem_support_iff.2 h)] }
end

end LmapDomain

section Total

variable (α) {α' : Type _} (M) {M' : Type _} (R) [AddCommMonoidₓ M'] [Module R M'] (v : α → M) {v' : α' → M'}

/-- Interprets (l : α →₀ R) as linear combination of the elements in the family (v : α → M) and
    evaluates this linear combination. -/
protected def Total : (α →₀ R) →ₗ[R] M :=
  Finsupp.lsum ℕ fun i => LinearMap.id.smulRight (v i)

variable {α M v}

theorem total_apply (l : α →₀ R) : Finsupp.total α M R v l = l.sum fun i a => a • v i :=
  rfl

theorem total_apply_of_mem_supported {l : α →₀ R} {s : Finset α} (hs : l ∈ supported R R («expr↑ » s : Set α)) :
  Finsupp.total α M R v l = s.sum fun i => l i • v i :=
  Finset.sum_subset hs$
    fun x _ hxg =>
      show l x • v x = 0 by 
        rw [not_mem_support_iff.1 hxg, zero_smul]

@[simp]
theorem total_single (c : R) (a : α) : Finsupp.total α M R v (single a c) = c • v a :=
  by 
    simp [total_apply, sum_single_index]

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem apply_total
(f : «expr →ₗ[ ] »(M, R, M'))
(v)
(l : «expr →₀ »(α, R)) : «expr = »(f (finsupp.total α M R v l), finsupp.total α M' R «expr ∘ »(f, v) l) :=
by apply [expr finsupp.induction_linear l]; simp [] [] [] [] [] [] { contextual := tt }

theorem total_unique [Unique α] (l : α →₀ R) v : Finsupp.total α M R v l = l (default α) • v (default α) :=
  by 
    rw [←total_single, ←unique_single l]

theorem total_surjective (h : Function.Surjective v) : Function.Surjective (Finsupp.total α M R v) :=
  by 
    intro x 
    obtain ⟨y, hy⟩ := h x 
    exact
      ⟨Finsupp.single y 1,
        by 
          simp [hy]⟩

theorem total_range (h : Function.Surjective v) : (Finsupp.total α M R v).range = ⊤ :=
  range_eq_top.2$ total_surjective R h

/-- Any module is a quotient of a free module. This is stated as surjectivity of
`finsupp.total M M R id : (M →₀ R) →ₗ[R] M`. -/
theorem total_id_surjective M [AddCommMonoidₓ M] [Module R M] : Function.Surjective (Finsupp.total M M R id) :=
  total_surjective R Function.surjective_id

theorem range_total : (Finsupp.total α M R v).range = span R (range v) :=
  by 
    ext x 
    split 
    ·
      intro hx 
      rw [LinearMap.mem_range] at hx 
      rcases hx with ⟨l, hl⟩
      rw [←hl]
      rw [Finsupp.total_apply]
      unfold Finsupp.sum 
      apply sum_mem (span R (range v))
      exact fun i hi => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
    ·
      apply span_le.2
      intro x hx 
      rcases hx with ⟨i, hi⟩
      rw [SetLike.mem_coe, LinearMap.mem_range]
      use Finsupp.single i 1
      simp [hi]

theorem lmap_domain_total (f : α → α') (g : M →ₗ[R] M') (h : ∀ i, g (v i) = v' (f i)) :
  (Finsupp.total α' M' R v').comp (lmap_domain R R f) = g.comp (Finsupp.total α M R v) :=
  by 
    ext l <;> simp [total_apply, Finsupp.sum_map_domain_index, add_smul, h]

@[simp]
theorem total_emb_domain (f : α ↪ α') (l : α →₀ R) :
  (Finsupp.total α' M' R v') (emb_domain f l) = (Finsupp.total α M' R (v' ∘ f)) l :=
  by 
    simp [total_apply, Finsupp.sum, support_emb_domain, emb_domain_apply]

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem total_map_domain
(f : α → α')
(hf : function.injective f)
(l : «expr →₀ »(α, R)) : «expr = »(finsupp.total α' M' R v' (map_domain f l), finsupp.total α M' R «expr ∘ »(v', f) l) :=
begin
  have [] [":", expr «expr = »(map_domain f l, emb_domain ⟨f, hf⟩ l)] [],
  { rw [expr emb_domain_eq_map_domain ⟨f, hf⟩] [],
    refl },
  rw [expr this] [],
  apply [expr total_emb_domain R ⟨f, hf⟩ l]
end

@[simp]
theorem total_equiv_map_domain (f : α ≃ α') (l : α →₀ R) :
  (Finsupp.total α' M' R v') (equiv_map_domain f l) = (Finsupp.total α M' R (v' ∘ f)) l :=
  by 
    rw [equiv_map_domain_eq_map_domain, total_map_domain _ _ f.injective]

/-- A version of `finsupp.range_total` which is useful for going in the other direction -/
theorem span_eq_range_total (s : Set M) : span R s = (Finsupp.total s M R coeₓ).range :=
  by 
    rw [range_total, Subtype.range_coe_subtype, Set.set_of_mem_eq]

theorem mem_span_iff_total (s : Set M) (x : M) : x ∈ span R s ↔ ∃ l : s →₀ R, Finsupp.total s M R coeₓ l = x :=
  (SetLike.ext_iff.1$ span_eq_range_total _ _) x

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem span_image_eq_map_total
(s : set α) : «expr = »(span R «expr '' »(v, s), submodule.map (finsupp.total α M R v) (supported R R s)) :=
begin
  apply [expr span_eq_of_le],
  { intros [ident x, ident hx],
    rw [expr set.mem_image] ["at", ident hx],
    apply [expr exists.elim hx],
    intros [ident i, ident hi],
    exact [expr ⟨_, finsupp.single_mem_supported R 1 hi.1, by simp [] [] [] ["[", expr hi.2, "]"] [] []⟩] },
  { refine [expr map_le_iff_le_comap.2 (λ z hz, _)],
    have [] [":", expr ∀ i, «expr ∈ »(«expr • »(z i, v i), span R «expr '' »(v, s))] [],
    { intro [ident c],
      haveI [] [] [":=", expr classical.dec_pred (λ x, «expr ∈ »(x, s))],
      by_cases [expr «expr ∈ »(c, s)],
      { exact [expr smul_mem _ _ (subset_span (set.mem_image_of_mem _ h))] },
      { simp [] [] [] ["[", expr (finsupp.mem_supported' R _).1 hz _ h, "]"] [] [] } },
    refine [expr sum_mem _ _],
    simp [] [] [] ["[", expr this, "]"] [] [] }
end

theorem mem_span_image_iff_total {s : Set α} {x : M} :
  x ∈ span R (v '' s) ↔ ∃ (l : _)(_ : l ∈ supported R R s), Finsupp.total α M R v l = x :=
  by 
    rw [span_image_eq_map_total]
    simp 

theorem total_option (v : Option α → M) (f : Option α →₀ R) :
  Finsupp.total (Option α) M R v f = (f none • v none)+Finsupp.total α M R (v ∘ Option.some) f.some :=
  by 
    rw [total_apply, sum_option_index_smul, total_apply]

theorem total_total {α β : Type _} (A : α → M) (B : β → α →₀ R) (f : β →₀ R) :
  Finsupp.total α M R A (Finsupp.total β (α →₀ R) R B f) =
    Finsupp.total β M R (fun b => Finsupp.total α M R A (B b)) f :=
  by 
    simp only [total_apply]
    apply induction_linear f
    ·
      simp only [sum_zero_index]
    ·
      intro f₁ f₂ h₁ h₂ 
      simp [sum_add_index, h₁, h₂, add_smul]
    ·
      simp [sum_single_index, sum_smul_index, smul_sum, mul_smul]

@[simp]
theorem total_fin_zero (f : Finₓ 0 → M) : Finsupp.total (Finₓ 0) M R f = 0 :=
  by 
    ext i 
    apply finZeroElim i

variable (α) (M) (v)

/-- `finsupp.total_on M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : set α` of indices.
-/
protected def total_on (s : Set α) : supported R R s →ₗ[R] span R (v '' s) :=
  LinearMap.codRestrict _ ((Finsupp.total _ _ _ v).comp (Submodule.subtype (supported R R s)))$
    fun ⟨l, hl⟩ => (mem_span_image_iff_total _).2 ⟨l, hl, rfl⟩

variable {α} {M} {v}

theorem total_on_range (s : Set α) : (Finsupp.totalOn α M R v s).range = ⊤ :=
  by 
    rw [Finsupp.totalOn, LinearMap.range_eq_map, LinearMap.map_cod_restrict, ←LinearMap.range_le_iff_comap,
      range_subtype, map_top, LinearMap.range_comp, range_subtype]
    exact (span_image_eq_map_total _ _).le

theorem total_comp (f : α' → α) : Finsupp.total α' M R (v ∘ f) = (Finsupp.total α M R v).comp (lmap_domain R R f) :=
  by 
    ext 
    simp [total_apply]

theorem total_comap_domain (f : α → α') (l : α' →₀ R) (hf : Set.InjOn f (f ⁻¹' «expr↑ » l.support)) :
  Finsupp.total α M R v (Finsupp.comapDomain f l hf) = (l.support.preimage f hf).Sum fun i => l (f i) • v i :=
  by 
    rw [Finsupp.total_apply] <;> rfl

theorem total_on_finset {s : Finset α} {f : α → R} (g : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) :
  Finsupp.total α M R g (Finsupp.onFinset s f hf) = Finset.sum s fun x : α => f x • g x :=
  by 
    simp only [Finsupp.total_apply, Finsupp.sum, Finsupp.on_finset_apply, Finsupp.support_on_finset]
    rw [Finset.sum_filter_of_ne]
    intro x hx h 
    contrapose! h 
    simp [h]

end Total

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `finsupp.dom_congr` as a `linear_equiv`.
See also `linear_map.fun_congr_left` for the case of arbitrary functions. -/
protected def dom_lcongr {α₁ α₂ : Type _} (e : α₁ ≃ α₂) : (α₁ →₀ M) ≃ₗ[R] α₂ →₀ M :=
  (Finsupp.domCongr e : (α₁ →₀ M) ≃+ (α₂ →₀ M)).toLinearEquiv$
    by 
      simpa only [equiv_map_domain_eq_map_domain, dom_congr_apply] using (lmap_domain M R e).map_smul

@[simp]
theorem dom_lcongr_apply {α₁ : Type _} {α₂ : Type _} (e : α₁ ≃ α₂) (v : α₁ →₀ M) :
  (Finsupp.domLcongr e : _ ≃ₗ[R] _) v = Finsupp.domCongr e v :=
  rfl

@[simp]
theorem dom_lcongr_refl : Finsupp.domLcongr (Equiv.refl α) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext$ fun _ => equiv_map_domain_refl _

theorem dom_lcongr_trans {α₁ α₂ α₃ : Type _} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃) :
  (Finsupp.domLcongr f).trans (Finsupp.domLcongr f₂) = (Finsupp.domLcongr (f.trans f₂) : (_ →₀ M) ≃ₗ[R] _) :=
  LinearEquiv.ext$ fun _ => (equiv_map_domain_trans _ _ _).symm

@[simp]
theorem dom_lcongr_symm {α₁ α₂ : Type _} (f : α₁ ≃ α₂) :
  ((Finsupp.domLcongr f).symm : (_ →₀ M) ≃ₗ[R] _) = Finsupp.domLcongr f.symm :=
  LinearEquiv.ext$ fun x => rfl

@[simp]
theorem dom_lcongr_single {α₁ : Type _} {α₂ : Type _} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
  (Finsupp.domLcongr e : _ ≃ₗ[R] _) (Finsupp.single i m) = Finsupp.single (e i) m :=
  by 
    simp [Finsupp.domLcongr, Finsupp.domCongr, equiv_map_domain_single]

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An equivalence of sets induces a linear equivalence of `finsupp`s supported on those sets. -/
noncomputable
def congr
{α' : Type*}
(s : set α)
(t : set α')
(e : «expr ≃ »(s, t)) : «expr ≃ₗ[ ] »(supported M R s, R, supported M R t) :=
begin
  haveI [] [] [":=", expr classical.dec_pred (λ x, «expr ∈ »(x, s))],
  haveI [] [] [":=", expr classical.dec_pred (λ x, «expr ∈ »(x, t))],
  refine [expr «expr ≪≫ₗ »(finsupp.supported_equiv_finsupp s, «expr ≪≫ₗ »(_, (finsupp.supported_equiv_finsupp t).symm))],
  exact [expr finsupp.dom_lcongr e]
end

/-- `finsupp.map_range` as a `linear_map`. -/
@[simps]
def map_range.linear_map (f : M →ₗ[R] N) : (α →₀ M) →ₗ[R] α →₀ N :=
  { map_range.add_monoid_hom f.to_add_monoid_hom with toFun := (map_range f f.map_zero : (α →₀ M) → α →₀ N),
    map_smul' := fun c v => map_range_smul c v (f.map_smul c) }

@[simp]
theorem map_range.linear_map_id : map_range.linear_map LinearMap.id = (LinearMap.id : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext map_range_id

theorem map_range.linear_map_comp (f : N →ₗ[R] P) (f₂ : M →ₗ[R] N) :
  (map_range.linear_map (f.comp f₂) : (α →₀ _) →ₗ[R] _) = (map_range.linear_map f).comp (map_range.linear_map f₂) :=
  LinearMap.ext$ map_range_comp _ _ _ _ _

@[simp]
theorem map_range.linear_map_to_add_monoid_hom (f : M →ₗ[R] N) :
  (map_range.linear_map f).toAddMonoidHom = (map_range.add_monoid_hom f.to_add_monoid_hom : (α →₀ M) →+ _) :=
  AddMonoidHom.ext$ fun _ => rfl

/-- `finsupp.map_range` as a `linear_equiv`. -/
@[simps apply]
def map_range.linear_equiv (e : M ≃ₗ[R] N) : (α →₀ M) ≃ₗ[R] α →₀ N :=
  { map_range.linear_map e.to_linear_map, map_range.add_equiv e.to_add_equiv with toFun := map_range e e.map_zero,
    invFun := map_range e.symm e.symm.map_zero }

@[simp]
theorem map_range.linear_equiv_refl : map_range.linear_equiv (LinearEquiv.refl R M) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext map_range_id

theorem map_range.linear_equiv_trans (f : M ≃ₗ[R] N) (f₂ : N ≃ₗ[R] P) :
  (map_range.linear_equiv (f.trans f₂) : (α →₀ _) ≃ₗ[R] _) =
    (map_range.linear_equiv f).trans (map_range.linear_equiv f₂) :=
  LinearEquiv.ext$ map_range_comp _ _ _ _ _

@[simp]
theorem map_range.linear_equiv_symm (f : M ≃ₗ[R] N) :
  ((map_range.linear_equiv f).symm : (α →₀ _) ≃ₗ[R] _) = map_range.linear_equiv f.symm :=
  LinearEquiv.ext$ fun x => rfl

@[simp]
theorem map_range.linear_equiv_to_add_equiv (f : M ≃ₗ[R] N) :
  (map_range.linear_equiv f).toAddEquiv = (map_range.add_equiv f.to_add_equiv : (α →₀ M) ≃+ _) :=
  AddEquiv.ext$ fun _ => rfl

@[simp]
theorem map_range.linear_equiv_to_linear_map (f : M ≃ₗ[R] N) :
  (map_range.linear_equiv f).toLinearMap = (map_range.linear_map f.to_linear_map : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext$ fun _ => rfl

/-- An equivalence of domain and a linear equivalence of codomain induce a linear equivalence of the
corresponding finitely supported functions. -/
def lcongr {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) : (ι →₀ M) ≃ₗ[R] κ →₀ N :=
  (Finsupp.domLcongr e₁).trans (map_range.linear_equiv e₂)

@[simp]
theorem lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (i : ι) (m : M) :
  lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single (e₁ i) (e₂ m) :=
  by 
    simp [lcongr]

@[simp]
theorem lcongr_apply_apply {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (f : ι →₀ M) (k : κ) :
  lcongr e₁ e₂ f k = e₂ (f (e₁.symm k)) :=
  rfl

theorem lcongr_symm_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (k : κ) (n : N) :
  (lcongr e₁ e₂).symm (Finsupp.single k n) = Finsupp.single (e₁.symm k) (e₂.symm n) :=
  by 
    applyFun lcongr e₁ e₂ using (lcongr e₁ e₂).Injective 
    simp 

@[simp]
theorem lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm :=
  by 
    ext f i 
    simp only [Equiv.symm_symm, Finsupp.lcongr_apply_apply]
    apply Finsupp.induction_linear f
    ·
      simp 
    ·
      intro f g hf hg 
      simp [map_add, hf, hg]
    ·
      intro k m 
      simp only [Finsupp.lcongr_symm_single]
      simp only [Finsupp.single, Equiv.symm_apply_eq, Finsupp.coe_mk]
      splitIfs <;> simp 

section Sum

variable (R)

/-- The linear equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `linear_equiv` version of `finsupp.sum_finsupp_equiv_prod_finsupp`. -/
@[simps apply symmApply]
def sum_finsupp_lequiv_prod_finsupp {α β : Type _} : (Sum α β →₀ M) ≃ₗ[R] (α →₀ M) × (β →₀ M) :=
  { sum_finsupp_add_equiv_prod_finsupp with
    map_smul' :=
      by 
        intros 
        ext <;>
          simp only [AddEquiv.to_fun_eq_coe, Prod.smul_fst, Prod.smul_snd, smul_apply,
            snd_sum_finsupp_add_equiv_prod_finsupp, fst_sum_finsupp_add_equiv_prod_finsupp, RingHom.id_apply] }

theorem fst_sum_finsupp_lequiv_prod_finsupp {α β : Type _} (f : Sum α β →₀ M) (x : α) :
  (sum_finsupp_lequiv_prod_finsupp R f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sum_finsupp_lequiv_prod_finsupp {α β : Type _} (f : Sum α β →₀ M) (y : β) :
  (sum_finsupp_lequiv_prod_finsupp R f).2 y = f (Sum.inr y) :=
  rfl

theorem sum_finsupp_lequiv_prod_finsupp_symm_inl {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
  ((sum_finsupp_lequiv_prod_finsupp R).symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sum_finsupp_lequiv_prod_finsupp_symm_inr {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
  ((sum_finsupp_lequiv_prod_finsupp R).symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

section Sigma

variable {η : Type _} [Fintype η] {ιs : η → Type _} [HasZero α]

variable (R)

/-- On a `fintype η`, `finsupp.split` is a linear equivalence between
`(Σ (j : η), ιs j) →₀ M` and `Π j, (ιs j →₀ M)`.

This is the `linear_equiv` version of `finsupp.sigma_finsupp_add_equiv_pi_finsupp`. -/
noncomputable def sigma_finsupp_lequiv_pi_finsupp {M : Type _} {ιs : η → Type _} [AddCommMonoidₓ M] [Module R M] :
  ((Σj, ιs j) →₀ M) ≃ₗ[R] ∀ j, ιs j →₀ M :=
  { sigma_finsupp_add_equiv_pi_finsupp with
    map_smul' :=
      fun c f =>
        by 
          ext 
          simp  }

@[simp]
theorem sigma_finsupp_lequiv_pi_finsupp_apply {M : Type _} {ιs : η → Type _} [AddCommMonoidₓ M] [Module R M]
  (f : (Σj, ιs j) →₀ M) j i : sigma_finsupp_lequiv_pi_finsupp R f j i = f ⟨j, i⟩ :=
  rfl

@[simp]
theorem sigma_finsupp_lequiv_pi_finsupp_symm_apply {M : Type _} {ιs : η → Type _} [AddCommMonoidₓ M] [Module R M]
  (f : ∀ j, ιs j →₀ M) ji : (Finsupp.sigmaFinsuppLequivPiFinsupp R).symm f ji = f ji.1 ji.2 :=
  rfl

end Sigma

section Prod

/-- The linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M`.

This is the `linear_equiv` version of `finsupp.finsupp_prod_equiv`. -/
noncomputable def finsupp_prod_lequiv {α β : Type _} (R : Type _) {M : Type _} [Semiringₓ R] [AddCommMonoidₓ M]
  [Module R M] : (α × β →₀ M) ≃ₗ[R] α →₀ β →₀ M :=
  { finsupp_prod_equiv with
    map_add' :=
      fun f g =>
        by 
          ext 
          simp [finsupp_prod_equiv, curry_apply],
    map_smul' :=
      fun c f =>
        by 
          ext 
          simp [finsupp_prod_equiv, curry_apply] }

@[simp]
theorem finsupp_prod_lequiv_apply {α β R M : Type _} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (f : α × β →₀ M) x
  y : finsupp_prod_lequiv R f x y = f (x, y) :=
  by 
    rw [finsupp_prod_lequiv, LinearEquiv.coe_mk, finsupp_prod_equiv, Finsupp.curry_apply]

@[simp]
theorem finsupp_prod_lequiv_symm_apply {α β R M : Type _} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]
  (f : α →₀ β →₀ M) xy : (finsupp_prod_lequiv R).symm f xy = f xy.1 xy.2 :=
  by 
    convRHS => rw [←(finsupp_prod_lequiv R).apply_symm_apply f, finsupp_prod_lequiv_apply, Prod.mk.eta]

end Prod

end Finsupp

variable {R : Type _} {M : Type _} {N : Type _}

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [AddCommMonoidₓ N] [Module R N]

section 

variable (R)

/--
Pick some representation of `x : span R w` as a linear combination in `w`,
using the axiom of choice.
-/
def Span.repr (w : Set M) (x : span R w) : w →₀ R :=
  ((Finsupp.mem_span_iff_total _ _ _).mp x.2).some

@[simp]
theorem Span.finsupp_total_repr {w : Set M} (x : span R w) : Finsupp.total w M R coeₓ (Span.repr R w x) = x :=
  ((Finsupp.mem_span_iff_total _ _ _).mp x.2).some_spec

end 

theorem Submodule.finsupp_sum_mem {ι β : Type _} [HasZero β] (S : Submodule R M) (f : ι →₀ β) (g : ι → β → M)
  (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.sum g ∈ S :=
  S.to_add_submonoid.finsupp_sum_mem f g h

theorem LinearMap.map_finsupp_total (f : M →ₗ[R] N) {ι : Type _} {g : ι → M} (l : ι →₀ R) :
  f (Finsupp.total ι M R g l) = Finsupp.total ι N R (f ∘ g) l :=
  by 
    simp only [Finsupp.total_apply, Finsupp.total_apply, Finsupp.sum, f.map_sum, f.map_smul]

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem submodule.exists_finset_of_mem_supr
{ι : Sort*}
(p : ι → submodule R M)
{m : M}
(hm : «expr ∈ »(m, «expr⨆ , »((i), p i))) : «expr∃ , »((s : finset ι), «expr ∈ »(m, «expr⨆ , »((i «expr ∈ » s), p i))) :=
begin
  obtain ["⟨", ident f, ",", ident hf, ",", ident rfl, "⟩", ":", expr «expr∃ , »((f «expr ∈ » finsupp.supported R R «expr⋃ , »((i), «expr↑ »(p i))), «expr = »(finsupp.total M M R id f, m))],
  { have [ident aux] [":", expr «expr = »(«expr '' »((id : M → M), «expr⋃ , »((i : ι), «expr↑ »(p i))), «expr⋃ , »((i : ι), «expr↑ »(p i)))] [":=", expr set.image_id _],
    rwa ["[", expr supr_eq_span, ",", "<-", expr aux, ",", expr finsupp.mem_span_image_iff_total R, "]"] ["at", ident hm] },
  let [ident t] [":", expr finset M] [":=", expr f.support],
  have [ident ht] [":", expr ∀ x : {x // «expr ∈ »(x, t)}, «expr∃ , »((i), «expr ∈ »(«expr↑ »(x), p i))] [],
  { intros [ident x],
    rw [expr finsupp.mem_supported] ["at", ident hf],
    specialize [expr hf x.2],
    rwa [expr set.mem_Union] ["at", ident hf] },
  choose [] [ident g] [ident hg] ["using", expr ht],
  let [ident s] [":", expr finset ι] [":=", expr finset.univ.image g],
  use [expr s],
  simp [] [] ["only"] ["[", expr mem_supr, ",", expr supr_le_iff, "]"] [] [],
  assume [binders (N hN)],
  rw ["[", expr finsupp.total_apply, ",", expr finsupp.sum, ",", "<-", expr set_like.mem_coe, "]"] [],
  apply [expr N.sum_mem],
  assume [binders (x hx)],
  apply [expr submodule.smul_mem],
  let [ident i] [":", expr ι] [":=", expr g ⟨x, hx⟩],
  have [ident hi] [":", expr «expr ∈ »(i, s)] [],
  { rw [expr finset.mem_image] [],
    exact [expr ⟨⟨x, hx⟩, finset.mem_univ _, rfl⟩] },
  exact [expr hN i hi (hg _)]
end

/-- `submodule.exists_finset_of_mem_supr` as an `iff` -/
theorem Submodule.mem_supr_iff_exists_finset {ι : Sort _} {p : ι → Submodule R M} {m : M} :
  (m ∈ ⨆i, p i) ↔ ∃ s : Finset ι, m ∈ ⨆(i : _)(_ : i ∈ s), p i :=
  ⟨Submodule.exists_finset_of_mem_supr p, fun ⟨_, hs⟩ => supr_le_supr (fun i => (supr_const_le : _ ≤ p i)) hs⟩

theorem mem_span_finset {s : Finset M} {x : M} :
  x ∈ span R («expr↑ » s : Set M) ↔ ∃ f : M → R, (∑i in s, f i • i) = x :=
  ⟨fun hx =>
      let ⟨v, hvs, hvx⟩ :=
        (Finsupp.mem_span_image_iff_total _).1
          (show x ∈ span R (id '' («expr↑ » s : Set M))by 
            rwa [Set.image_id])
      ⟨v, hvx ▸ (Finsupp.total_apply_of_mem_supported _ hvs).symm⟩,
    fun ⟨f, hf⟩ => hf ▸ sum_mem _ fun i hi => smul_mem _ _$ subset_span hi⟩

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses `finsupp.sum`. -/
theorem mem_span_set {m : M} {s : Set M} :
  m ∈ Submodule.span R s ↔ ∃ c : M →₀ R, (c.support : Set M) ⊆ s ∧ (c.sum fun mi r => r • mi) = m :=
  by 
    convLHS => rw [←Set.image_id s]
    simpRw [←exists_prop]
    exact Finsupp.mem_span_image_iff_total R

-- error in LinearAlgebra.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `subsingleton R`, then `M ≃ₗ[R] ι →₀ R` for any type `ι`. -/
@[simps #[]]
def module.subsingleton_equiv
(R M ι : Type*)
[semiring R]
[subsingleton R]
[add_comm_monoid M]
[module R M] : «expr ≃ₗ[ ] »(M, R, «expr →₀ »(ι, R)) :=
{ to_fun := λ m, 0,
  inv_fun := λ f, 0,
  left_inv := λ m, by { letI [] [] [":=", expr module.subsingleton R M],
    simp [] [] ["only"] ["[", expr eq_iff_true_of_subsingleton, "]"] [] [] },
  right_inv := λ f, by simp [] [] ["only"] ["[", expr eq_iff_true_of_subsingleton, "]"] [] [],
  map_add' := λ m n, (add_zero 0).symm,
  map_smul' := λ r m, (smul_zero r).symm }

namespace LinearMap

variable {R M} {α : Type _}

open Finsupp Function

/-- A surjective linear map to finitely supported functions has a splitting. -/
def splitting_of_finsupp_surjective (f : M →ₗ[R] α →₀ R) (s : surjective f) : (α →₀ R) →ₗ[R] M :=
  Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).some

theorem splitting_of_finsupp_surjective_splits (f : M →ₗ[R] α →₀ R) (s : surjective f) :
  f.comp (splitting_of_finsupp_surjective f s) = LinearMap.id :=
  by 
    ext x y 
    dsimp [splitting_of_finsupp_surjective]
    congr 
    rw [sum_single_index, one_smul]
    ·
      exact (s (Finsupp.single x 1)).some_spec
    ·
      rw [zero_smul]

theorem left_inverse_splitting_of_finsupp_surjective (f : M →ₗ[R] α →₀ R) (s : surjective f) :
  left_inverse f (splitting_of_finsupp_surjective f s) :=
  fun g => LinearMap.congr_fun (splitting_of_finsupp_surjective_splits f s) g

theorem splitting_of_finsupp_surjective_injective (f : M →ₗ[R] α →₀ R) (s : surjective f) :
  injective (splitting_of_finsupp_surjective f s) :=
  (left_inverse_splitting_of_finsupp_surjective f s).Injective

/-- A surjective linear map to functions on a finite type has a splitting. -/
def splitting_of_fun_on_fintype_surjective [Fintype α] (f : M →ₗ[R] α → R) (s : surjective f) : (α → R) →ₗ[R] M :=
  (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).some).comp
    (linear_equiv_fun_on_fintype R R α).symm.toLinearMap

theorem splitting_of_fun_on_fintype_surjective_splits [Fintype α] (f : M →ₗ[R] α → R) (s : surjective f) :
  f.comp (splitting_of_fun_on_fintype_surjective f s) = LinearMap.id :=
  by 
    ext x y 
    dsimp [splitting_of_fun_on_fintype_surjective]
    rw [linear_equiv_fun_on_fintype_symm_single, Finsupp.sum_single_index, one_smul, LinearMap.id_coe, id_def,
      (s (Finsupp.single x 1)).some_spec, Finsupp.single_eq_pi_single]
    rw [zero_smul]

theorem left_inverse_splitting_of_fun_on_fintype_surjective [Fintype α] (f : M →ₗ[R] α → R) (s : surjective f) :
  left_inverse f (splitting_of_fun_on_fintype_surjective f s) :=
  fun g => LinearMap.congr_fun (splitting_of_fun_on_fintype_surjective_splits f s) g

theorem splitting_of_fun_on_fintype_surjective_injective [Fintype α] (f : M →ₗ[R] α → R) (s : surjective f) :
  injective (splitting_of_fun_on_fintype_surjective f s) :=
  (left_inverse_splitting_of_fun_on_fintype_surjective f s).Injective

end LinearMap

