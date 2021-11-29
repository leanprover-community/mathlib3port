import Mathbin.LinearAlgebra.Finsupp 
import Mathbin.LinearAlgebra.Prod 
import Mathbin.Data.Equiv.Fin 
import Mathbin.SetTheory.Cardinal

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `linear_independent R v` as `ker (finsupp.total ι M R v) = ⊥`. Here `finsupp.total` is the
linear map sending a function `f : ι →₀ R` with finite support to the linear combination of vectors
from `v` with these coefficients. Then we prove that several other statements are equivalent to this
one, including injectivity of `finsupp.total ι M R v` and some versions with explicitly written
linear combinations.

## Main definitions
All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `linear_independent R v` states that the elements of the family `v` are linearly independent.

* `linear_independent.repr hv x` returns the linear combination representing `x : span R (range v)`
on the linearly independent vectors `v`, given `hv : linear_independent R v`
(using classical choice). `linear_independent.repr hv` is provided as a linear map.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `fintype.linear_independent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : finset ι`;
* `linear_independent_empty_type`: a family indexed by an empty type is linearly independent;
* `linear_independent_unique_iff`: if `ι` is a singleton, then `linear_independent K v` is
  equivalent to `v (default ι) ≠ 0`;
* linear_independent_option`, `linear_independent_sum`, `linear_independent_fin_cons`,
  `linear_independent_fin_succ`: type-specific tests for linear independence of families of vector
  fields;
* `linear_independent_insert`, `linear_independent_union`, `linear_independent_pair`,
  `linear_independent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `linear_independent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that, when working over a division ring,
any family of vectors includes a linear independent subfamily spanning the same subspace.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent.

If you want to use sets, use the family `(λ x, x : s → M)` given a set `s : set M`. The lemmas
`linear_independent.to_subtype_range` and `linear_independent.of_subtype_range` connect those two
worlds.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/


noncomputable theory

open Function Set Submodule

open_locale Classical BigOperators Cardinal

universe u

variable{ι : Type _}{ι' : Type _}{R : Type _}{K : Type _}

variable{M : Type _}{M' M'' : Type _}{V : Type u}{V' : Type _}

section Module

variable{v : ι → M}

variable[Semiringₓ R][AddCommMonoidₓ M][AddCommMonoidₓ M'][AddCommMonoidₓ M'']

variable[Module R M][Module R M'][Module R M'']

variable{a b : R}{x y : M}

variable(R)(v)

/-- `linear_independent R v` states the family of vectors `v` is linearly independent over `R`. -/
def LinearIndependent : Prop :=
  (Finsupp.total ι M R v).ker = ⊥

variable{R}{v}

theorem linear_independent_iff : LinearIndependent R v ↔ ∀ l, Finsupp.total ι M R v l = 0 → l = 0 :=
  by 
    simp [LinearIndependent, LinearMap.ker_eq_bot']

theorem linear_independent_iff' :
  LinearIndependent R v ↔ ∀ (s : Finset ι), ∀ (g : ι → R), (∑i in s, g i • v i) = 0 → ∀ i (_ : i ∈ s), g i = 0 :=
  linear_independent_iff.trans
    ⟨fun hf s g hg i his =>
        have h :=
          hf (∑i in s, Finsupp.single i (g i))$
            by 
              simpa only [LinearMap.map_sum, Finsupp.total_single] using hg 
        calc g i = (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single i (g i)) :=
          by 
            rw [Finsupp.lapply_apply, Finsupp.single_eq_same]
          _ = ∑j in s, (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single j (g j)) :=
          Eq.symm$
            Finset.sum_eq_single i
              (fun j hjs hji =>
                by 
                  rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hji])
              fun hnis => hnis.elim his 
          _ = (∑j in s, Finsupp.single j (g j)) i := (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R).map_sum.symm 
          _ = 0 := Finsupp.ext_iff.1 h i
          ,
      fun hf l hl =>
        Finsupp.ext$ fun i => Classical.by_contradiction$ fun hni => hni$ hf _ _ hl _$ Finsupp.mem_support_iff.2 hni⟩

theorem linear_independent_iff'' :
  LinearIndependent R v ↔
    ∀ (s : Finset ι) (g : ι → R) (hg : ∀ i (_ : i ∉ s), g i = 0), (∑i in s, g i • v i) = 0 → ∀ i, g i = 0 :=
  linear_independent_iff'.trans
    ⟨fun H s g hg hv i => if his : i ∈ s then H s g hv i his else hg i his,
      fun H s g hg i hi =>
        by 
          convert
            H s (fun j => if j ∈ s then g j else 0) (fun j hj => if_neg hj)
              (by 
                simpRw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg])
              i 
          exact (if_pos hi).symm⟩

theorem linear_dependent_iff :
  ¬LinearIndependent R v ↔ ∃ s : Finset ι, ∃ g : ι → R, (∑i in s, g i • v i) = 0 ∧ ∃ (i : _)(_ : i ∈ s), g i ≠ 0 :=
  by 
    rw [linear_independent_iff']
    simp only [exists_prop, not_forall]

theorem Fintype.linear_independent_iff [Fintype ι] :
  LinearIndependent R v ↔ ∀ (g : ι → R), (∑i, g i • v i) = 0 → ∀ i, g i = 0 :=
  by 
    refine'
      ⟨fun H g =>
          by 
            simpa using linear_independent_iff'.1 H Finset.univ g,
        fun H => linear_independent_iff''.2$ fun s g hg hs i => H _ _ _⟩
    rw [←hs]
    refine' (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => _).symm 
    rw [hg i hi, zero_smul]

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` has the trivial kernel. -/
theorem fintype.linear_independent_iff'
[fintype ι] : «expr ↔ »(linear_independent R v, «expr = »((linear_map.lsum R (λ
    i : ι, R) exprℕ() (λ i, linear_map.id.smul_right (v i))).ker, «expr⊥»())) :=
by simp [] [] [] ["[", expr fintype.linear_independent_iff, ",", expr linear_map.ker_eq_bot', ",", expr funext_iff, "]"] [] []

theorem linear_independent_empty_type [IsEmpty ι] : LinearIndependent R v :=
  linear_independent_iff.mpr$ fun v hv => Subsingleton.elimₓ v 0

theorem LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R v) : v i ≠ 0 :=
  fun h =>
    @zero_ne_one R _ _$
      Eq.symm
        (by 
          suffices  : (Finsupp.single i 1 : ι →₀ R) i = 0
          ·
            simpa 
          rw [linear_independent_iff.1 hv (Finsupp.single i 1)]
          ·
            simp 
          ·
            simp [h])

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
theorem linear_independent.comp
(h : linear_independent R v)
(f : ι' → ι)
(hf : injective f) : linear_independent R «expr ∘ »(v, f) :=
begin
  rw ["[", expr linear_independent_iff, ",", expr finsupp.total_comp, "]"] [],
  intros [ident l, ident hl],
  have [ident h_map_domain] [":", expr ∀ x, «expr = »(finsupp.map_domain f l (f x), 0)] [],
  by rw [expr linear_independent_iff.1 h (finsupp.map_domain f l) hl] []; simp [] [] [] [] [] [],
  ext [] [ident x] [],
  convert [] [expr h_map_domain x] [],
  rw ["[", expr finsupp.map_domain_apply hf, "]"] []
end

theorem LinearIndependent.coe_range (i : LinearIndependent R v) : LinearIndependent R (coeₓ : range v → M) :=
  by 
    simpa using i.comp _ (range_splitting_injective v)

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `v` is a linearly independent family of vectors and the kernel of a linear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `linear_independent.map'` for a special case assuming `ker f = ⊥`. -/
theorem linear_independent.map
(hv : linear_independent R v)
{f : «expr →ₗ[ ] »(M, R, M')}
(hf_inj : disjoint (span R (range v)) f.ker) : linear_independent R «expr ∘ »(f, v) :=
begin
  rw ["[", expr disjoint, ",", "<-", expr set.image_univ, ",", expr finsupp.span_image_eq_map_total, ",", expr map_inf_eq_map_inf_comap, ",", expr map_le_iff_le_comap, ",", expr comap_bot, ",", expr finsupp.supported_univ, ",", expr top_inf_eq, "]"] ["at", ident hf_inj],
  unfold [ident linear_independent] ["at", ident hv, "⊢"],
  rw ["[", expr hv, ",", expr le_bot_iff, "]"] ["at", ident hf_inj],
  haveI [] [":", expr inhabited M] [":=", expr ⟨0⟩],
  rw ["[", expr finsupp.total_comp, ",", expr @finsupp.lmap_domain_total _ _ R _ _ _ _ _ _ _ _ _ _ f, ",", expr linear_map.ker_comp, ",", expr hf_inj, "]"] [],
  exact [expr λ _, rfl]
end

/-- An injective linear map sends linearly independent families of vectors to linearly independent
families of vectors. See also `linear_independent.map` for a more general statement. -/
theorem LinearIndependent.map' (hv : LinearIndependent R v) (f : M →ₗ[R] M') (hf_inj : f.ker = ⊥) :
  LinearIndependent R (f ∘ v) :=
  hv.map$
    by 
      simp [hf_inj]

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
theorem LinearIndependent.of_comp (f : M →ₗ[R] M') (hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v :=
  linear_independent_iff'.2$
    fun s g hg i his =>
      have  : (∑i : ι in s, g i • f (v i)) = 0 :=
        by 
          simpRw [←f.map_smul, ←f.map_sum, hg, f.map_zero]
      linear_independent_iff'.1 hfv s g this i his

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected theorem LinearMap.linear_independent_iff (f : M →ₗ[R] M') (hf_inj : f.ker = ⊥) :
  LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  ⟨fun h => h.of_comp f,
    fun h =>
      h.map$
        by 
          simp only [hf_inj, disjoint_bot_right]⟩

@[nontriviality]
theorem linear_independent_of_subsingleton [Subsingleton R] : LinearIndependent R v :=
  linear_independent_iff.2 fun l hl => Subsingleton.elimₓ _ _

theorem linear_independent_equiv (e : ι ≃ ι') {f : ι' → M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f :=
  ⟨fun h => Function.comp.right_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective, fun h => h.comp _ e.injective⟩

theorem linear_independent_equiv' (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ e = g) :
  LinearIndependent R g ↔ LinearIndependent R f :=
  h ▸ linear_independent_equiv e

theorem linear_independent_subtype_range {ι} {f : ι → M} (hf : injective f) :
  LinearIndependent R (coeₓ : range f → M) ↔ LinearIndependent R f :=
  Iff.symm$ linear_independent_equiv' (Equiv.ofInjective f hf) rfl

alias linear_independent_subtype_range ↔ LinearIndependent.of_subtype_range _

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem linear_independent_image
{ι}
{s : set ι}
{f : ι → M}
(hf : set.inj_on f s) : «expr ↔ »(linear_independent R (λ
  x : s, f x), linear_independent R (λ x : «expr '' »(f, s), (x : M))) :=
linear_independent_equiv' (equiv.set.image_of_inj_on _ _ hf) rfl

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem linear_independent_span
(hs : linear_independent R v) : @linear_independent ι R (span R (range v)) (λ
 i : ι, ⟨v i, subset_span (mem_range_self i)⟩) _ _ _ :=
linear_independent.of_comp (span R (range v)).subtype hs

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- See `linear_independent.fin_cons` for a family of elements in a vector space. -/
theorem linear_independent.fin_cons'
{m : exprℕ()}
(x : M)
(v : fin m → M)
(hli : linear_independent R v)
(x_ortho : ∀
 (c : R)
 (y : submodule.span R (set.range v)), «expr = »(«expr + »(«expr • »(c, x), y), (0 : M)) → «expr = »(c, 0)) : linear_independent R (fin.cons x v : fin m.succ → M) :=
begin
  rw [expr fintype.linear_independent_iff] ["at", ident hli, "⊢"],
  rintros [ident g, ident total_eq, ident j],
  have [ident zero_not_mem] [":", expr «expr ∉ »((0 : fin m.succ), finset.univ.image (fin.succ : fin m → fin m.succ))] [],
  { rw [expr finset.mem_image] [],
    rintro ["⟨", ident x, ",", ident hx, ",", ident succ_eq, "⟩"],
    exact [expr fin.succ_ne_zero _ succ_eq] },
  simp [] [] ["only"] ["[", expr submodule.coe_mk, ",", expr fin.univ_succ, ",", expr finset.sum_insert zero_not_mem, ",", expr fin.cons_zero, ",", expr fin.cons_succ, ",", expr forall_true_iff, ",", expr imp_self, ",", expr fin.succ_inj, ",", expr finset.sum_image, "]"] [] ["at", ident total_eq],
  have [] [":", expr «expr = »(g 0, 0)] [],
  { refine [expr x_ortho (g 0) ⟨«expr∑ , »((i : fin m), «expr • »(g i.succ, v i)), _⟩ total_eq],
    exact [expr sum_mem _ (λ i _, smul_mem _ _ (subset_span ⟨i, rfl⟩))] },
  refine [expr fin.cases this (λ j, _) j],
  apply [expr hli (λ i, g i.succ)],
  simpa [] [] ["only"] ["[", expr this, ",", expr zero_smul, ",", expr zero_add, "]"] [] ["using", expr total_eq]
end

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A set of linearly independent vectors in a module `M` over a semiring `K` is also linearly
independent over a subring `R` of `K`.
The implementation uses minimal assumptions about the relationship between `R`, `K` and `M`.
The version where `K` is an `R`-algebra is `linear_independent.restrict_scalars_algebras`.
 -/
theorem linear_independent.restrict_scalars
[semiring K]
[smul_with_zero R K]
[module K M]
[is_scalar_tower R K M]
(hinj : function.injective (λ r : R, «expr • »(r, (1 : K))))
(li : linear_independent K v) : linear_independent R v :=
begin
  refine [expr linear_independent_iff'.mpr (λ s g hg i hi, hinj (eq.trans _ (zero_smul _ _).symm))],
  refine [expr (linear_independent_iff'.mp li : _) _ _ _ i hi],
  simp_rw ["[", expr smul_assoc, ",", expr one_smul, "]"] [],
  exact [expr hg]
end

/-- Every finite subset of a linearly independent set is linearly independent. -/
theorem linear_independent_finset_map_embedding_subtype (s : Set M) (li : LinearIndependent R (coeₓ : s → M))
  (t : Finset s) : LinearIndependent R (coeₓ : Finset.map (embedding.subtype s) t → M) :=
  by 
    let f : t.map (embedding.subtype s) → s :=
      fun x =>
        ⟨x.1,
          by 
            obtain ⟨x, h⟩ := x 
            rw [Finset.mem_map] at h 
            obtain ⟨a, ha, rfl⟩ := h 
            simp only [Subtype.coe_prop, embedding.coe_subtype]⟩
    convert LinearIndependent.comp li f _ 
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [Finset.mem_map] at hx hy 
    obtain ⟨a, ha, rfl⟩ := hx 
    obtain ⟨b, hb, rfl⟩ := hy 
    simp only [imp_self, Subtype.mk_eq_mk]

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
If every finite set of linearly independent vectors has cardinality at most `n`,
then the same is true for arbitrary sets of linearly independent vectors.
-/
theorem linear_independent_bounded_of_finset_linear_independent_bounded
{n : exprℕ()}
(H : ∀
 s : finset M, linear_independent R (λ
  i : s, (i : M)) → «expr ≤ »(s.card, n)) : ∀
s : set M, linear_independent R (coe : s → M) → «expr ≤ »(«expr#»() s, n) :=
begin
  intros [ident s, ident li],
  apply [expr cardinal.card_le_of],
  intro [ident t],
  rw ["<-", expr finset.card_map (embedding.subtype s)] [],
  apply [expr H],
  apply [expr linear_independent_finset_map_embedding_subtype _ li]
end

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/


-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent_comp_subtype
{s : set ι} : «expr ↔ »(linear_independent R («expr ∘ »(v, coe) : s → M), ∀
 l «expr ∈ » finsupp.supported R R s, «expr = »(finsupp.total ι M R v l, 0) → «expr = »(l, 0)) :=
begin
  simp [] [] ["only"] ["[", expr linear_independent_iff, ",", expr («expr ∘ »), ",", expr finsupp.mem_supported, ",", expr finsupp.total_apply, ",", expr set.subset_def, ",", expr finset.mem_coe, "]"] [] [],
  split,
  { intros [ident h, ident l, ident hl₁, ident hl₂],
    have [] [] [":=", expr h (l.subtype_domain s) ((finsupp.sum_subtype_domain_index hl₁).trans hl₂)],
    exact [expr (finsupp.subtype_domain_eq_zero_iff hl₁).1 this] },
  { intros [ident h, ident l, ident hl],
    refine [expr finsupp.emb_domain_eq_zero.1 (h «expr $ »(l.emb_domain, function.embedding.subtype s) _ _)],
    { suffices [] [":", expr ∀ i hi, «expr¬ »(«expr = »(l ⟨i, hi⟩, 0)) → «expr ∈ »(i, s)],
      by simpa [] [] [] [] [] [],
      intros [],
      assumption },
    { rwa ["[", expr finsupp.emb_domain_eq_map_domain, ",", expr finsupp.sum_map_domain_index, "]"] [],
      exacts ["[", expr λ _, zero_smul _ _, ",", expr λ _ _ _, add_smul _ _ _, "]"] } }
end

theorem linear_dependent_comp_subtype' {s : Set ι} :
  ¬LinearIndependent R (v ∘ coeₓ : s → M) ↔
    ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ Finsupp.total ι M R v f = 0 ∧ f ≠ 0 :=
  by 
    simp [linear_independent_comp_subtype]

/-- A version of `linear_dependent_comp_subtype'` with `finsupp.total` unfolded. -/
theorem linear_dependent_comp_subtype {s : Set ι} :
  ¬LinearIndependent R (v ∘ coeₓ : s → M) ↔
    ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ (∑i in f.support, f i • v i) = 0 ∧ f ≠ 0 :=
  linear_dependent_comp_subtype'

theorem linear_independent_subtype {s : Set M} :
  LinearIndependent R (fun x => x : s → M) ↔
    ∀ l (_ : l ∈ Finsupp.supported R R s), (Finsupp.total M M R id) l = 0 → l = 0 :=
  by 
    apply @linear_independent_comp_subtype _ _ _ id

theorem linear_independent_comp_subtype_disjoint {s : Set ι} :
  LinearIndependent R (v ∘ coeₓ : s → M) ↔ Disjoint (Finsupp.supported R R s) (Finsupp.total ι M R v).ker :=
  by 
    rw [linear_independent_comp_subtype, LinearMap.disjoint_ker]

theorem linear_independent_subtype_disjoint {s : Set M} :
  LinearIndependent R (fun x => x : s → M) ↔ Disjoint (Finsupp.supported R R s) (Finsupp.total M M R id).ker :=
  by 
    apply @linear_independent_comp_subtype_disjoint _ _ _ id

theorem linear_independent_iff_total_on {s : Set M} :
  LinearIndependent R (fun x => x : s → M) ↔ (Finsupp.totalOn M M R id s).ker = ⊥ :=
  by 
    rw [Finsupp.totalOn, LinearMap.ker, LinearMap.comap_cod_restrict, map_bot, comap_bot, LinearMap.ker_comp,
      linear_independent_subtype_disjoint, Disjoint, ←map_comap_subtype, map_le_iff_le_comap, comap_bot, ker_subtype,
      le_bot_iff]

theorem LinearIndependent.restrict_of_comp_subtype {s : Set ι} (hs : LinearIndependent R (v ∘ coeₓ : s → M)) :
  LinearIndependent R (s.restrict v) :=
  hs

variable(R M)

theorem linear_independent_empty : LinearIndependent R (fun x => x : (∅ : Set M) → M) :=
  by 
    simp [linear_independent_subtype_disjoint]

variable{R M}

theorem LinearIndependent.mono {t s : Set M} (h : t ⊆ s) :
  LinearIndependent R (fun x => x : s → M) → LinearIndependent R (fun x => x : t → M) :=
  by 
    simp only [linear_independent_subtype_disjoint]
    exact Disjoint.mono_left (Finsupp.supported_mono h)

theorem linear_independent_of_finite (s : Set M)
  (H : ∀ t (_ : t ⊆ s), finite t → LinearIndependent R (fun x => x : t → M)) :
  LinearIndependent R (fun x => x : s → M) :=
  linear_independent_subtype.2$
    fun l hl => linear_independent_subtype.1 (H _ hl (Finset.finite_to_set _)) l (subset.refl _)

theorem linear_independent_Union_of_directed {η : Type _} {s : η → Set M} (hs : Directed (· ⊆ ·) s)
  (h : ∀ i, LinearIndependent R (fun x => x : s i → M)) : LinearIndependent R (fun x => x : (⋃i, s i) → M) :=
  by 
    byCases' hη : Nonempty η
    ·
      skip 
      refine' linear_independent_of_finite (⋃i, s i) fun t ht ft => _ 
      rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩
      rcases hs.finset_le fi.to_finset with ⟨i, hi⟩
      exact (h i).mono (subset.trans hI$ bUnion_subset$ fun j hj => hi j (fi.mem_to_finset.2 hj))
    ·
      refine' (linear_independent_empty _ _).mono _ 
      rintro _ ⟨_, ⟨i, _⟩, _⟩
      exact hη ⟨i⟩

theorem linear_independent_sUnion_of_directed {s : Set (Set M)} (hs : DirectedOn (· ⊆ ·) s)
  (h : ∀ a (_ : a ∈ s), LinearIndependent R (fun x => x : (a : Set M) → M)) :
  LinearIndependent R (fun x => x : ⋃₀s → M) :=
  by 
    rw [sUnion_eq_Union] <;>
      exact
        linear_independent_Union_of_directed hs.directed_coe
          (by 
            simpa using h)

theorem linear_independent_bUnion_of_directed {η} {s : Set η} {t : η → Set M} (hs : DirectedOn (t ⁻¹'o (· ⊆ ·)) s)
  (h : ∀ a (_ : a ∈ s), LinearIndependent R (fun x => x : t a → M)) :
  LinearIndependent R (fun x => x : (⋃(a : _)(_ : a ∈ s), t a) → M) :=
  by 
    rw [bUnion_eq_Union] <;>
      exact
        linear_independent_Union_of_directed (directed_comp.2$ hs.directed_coe)
          (by 
            simpa using h)

end Subtype

end Module

/-! ### Properties which require `ring R` -/


section Module

variable{v : ι → M}

variable[Ringₓ R][AddCommGroupₓ M][AddCommGroupₓ M'][AddCommGroupₓ M'']

variable[Module R M][Module R M'][Module R M'']

variable{a b : R}{x y : M}

theorem linear_independent_iff_injective_total : LinearIndependent R v ↔ Function.Injective (Finsupp.total ι M R v) :=
  linear_independent_iff.trans (Finsupp.total ι M R v).toAddMonoidHom.injective_iff.symm

alias linear_independent_iff_injective_total ↔ LinearIndependent.injective_total _

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent.injective [nontrivial R] (hv : linear_independent R v) : injective v :=
begin
  intros [ident i, ident j, ident hij],
  let [ident l] [":", expr «expr →₀ »(ι, R)] [":=", expr «expr - »(finsupp.single i (1 : R), finsupp.single j 1)],
  have [ident h_total] [":", expr «expr = »(finsupp.total ι M R v l, 0)] [],
  { simp_rw ["[", expr linear_map.map_sub, ",", expr finsupp.total_apply, "]"] [],
    simp [] [] [] ["[", expr hij, "]"] [] [] },
  have [ident h_single_eq] [":", expr «expr = »(finsupp.single i (1 : R), finsupp.single j 1)] [],
  { rw [expr linear_independent_iff] ["at", ident hv],
    simp [] [] [] ["[", expr eq_add_of_sub_eq' (hv l h_total), "]"] [] [] },
  simpa [] [] [] ["[", expr finsupp.single_eq_single_iff, "]"] [] ["using", expr h_single_eq]
end

theorem LinearIndependent.to_subtype_range {ι} {f : ι → M} (hf : LinearIndependent R f) :
  LinearIndependent R (coeₓ : range f → M) :=
  by 
    nontriviality R 
    exact (linear_independent_subtype_range hf.injective).2 hf

theorem LinearIndependent.to_subtype_range' {ι} {f : ι → M} (hf : LinearIndependent R f) {t} (ht : range f = t) :
  LinearIndependent R (coeₓ : t → M) :=
  ht ▸ hf.to_subtype_range

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent.image_of_comp
{ι ι'}
(s : set ι)
(f : ι → ι')
(g : ι' → M)
(hs : linear_independent R (λ x : s, g (f x))) : linear_independent R (λ x : «expr '' »(f, s), g x) :=
begin
  nontriviality [expr R] [],
  have [] [":", expr inj_on f s] [],
  from [expr inj_on_iff_injective.2 hs.injective.of_comp],
  exact [expr (linear_independent_equiv' (equiv.set.image_of_inj_on f s this) rfl).1 hs]
end

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem linear_independent.image
{ι}
{s : set ι}
{f : ι → M}
(hs : linear_independent R (λ x : s, f x)) : linear_independent R (λ x : «expr '' »(f, s), (x : M)) :=
by convert [] [expr linear_independent.image_of_comp s f id hs] []

theorem LinearIndependent.group_smul {G : Type _} [hG : Groupₓ G] [DistribMulAction G R] [DistribMulAction G M]
  [IsScalarTower G R M] [SmulCommClass G R M] {v : ι → M} (hv : LinearIndependent R v) (w : ι → G) :
  LinearIndependent R (w • v) :=
  by 
    rw [linear_independent_iff''] at hv⊢
    intro s g hgs hsum i 
    refine' (smul_eq_zero_iff_eq (w i)).1 _ 
    refine' hv s (fun i => w i • g i) (fun i hi => _) _ i
    ·
      dsimp only 
      exact (hgs i hi).symm ▸ smul_zero _
    ·
      rw [←hsum, Finset.sum_congr rfl _]
      intros 
      erw [Pi.smul_apply, smul_assoc, smul_comm]

theorem LinearIndependent.units_smul {v : ι → M} (hv : LinearIndependent R v) (w : ι → Units R) :
  LinearIndependent R (w • v) :=
  by 
    rw [linear_independent_iff''] at hv⊢
    intro s g hgs hsum i 
    rw [←(w i).mul_left_eq_zero]
    refine' hv s (fun i => g i • w i) (fun i hi => _) _ i
    ·
      dsimp only 
      exact (hgs i hi).symm ▸ zero_smul _ _
    ·
      rw [←hsum, Finset.sum_congr rfl _]
      intros 
      erw [Pi.smul_apply, smul_assoc]
      rfl

section Maximal

universe v w

/--
A linearly independent family is maximal if there is no strictly larger linearly independent family.
-/
@[nolint unused_arguments]
def LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiringₓ R] {M : Type v} [AddCommMonoidₓ M] [Module R M]
  {v : ι → M} (i : LinearIndependent R v) : Prop :=
  ∀ (s : Set M) (i' : LinearIndependent R (coeₓ : s → M)) (h : range v ≤ s), range v = s

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An alternative characterization of a maximal linearly independent family,
quantifying over types (in the same universe as `M`) into which the indexing family injects.
-/
theorem linear_independent.maximal_iff
{ι : Type w}
{R : Type u}
[ring R]
[nontrivial R]
{M : Type v}
[add_comm_group M]
[module R M]
{v : ι → M}
(i : linear_independent R v) : «expr ↔ »(i.maximal, ∀
 (κ : Type v)
 (w : κ → M)
 (i' : linear_independent R w)
 (j : ι → κ)
 (h : «expr = »(«expr ∘ »(w, j), v)), surjective j) :=
begin
  fsplit,
  { rintros [ident p, ident κ, ident w, ident i', ident j, ident rfl],
    specialize [expr p (range w) i'.coe_range (range_comp_subset_range _ _)],
    rw ["[", expr range_comp, ",", "<-", expr @image_univ _ _ w, "]"] ["at", ident p],
    exact [expr range_iff_surjective.mp (image_injective.mpr i'.injective p)] },
  { intros [ident p, ident w, ident i', ident h],
    specialize [expr p w (coe : w → M) i' (λ
      i, ⟨v i, range_subset_iff.mp h i⟩) (by { ext [] [] [], simp [] [] [] [] [] [] })],
    have [ident q] [] [":=", expr congr_arg (λ s, «expr '' »((coe : w → M), s)) p.range_eq],
    dsimp [] [] [] ["at", ident q],
    rw ["[", "<-", expr image_univ, ",", expr image_image, "]"] ["at", ident q],
    simpa [] [] [] [] [] ["using", expr q] }
end

end Maximal

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Linear independent families are injective, even if you multiply either side. -/
theorem linear_independent.eq_of_smul_apply_eq_smul_apply
{M : Type*}
[add_comm_group M]
[module R M]
{v : ι → M}
(li : linear_independent R v)
(c d : R)
(i j : ι)
(hc : «expr ≠ »(c, 0))
(h : «expr = »(«expr • »(c, v i), «expr • »(d, v j))) : «expr = »(i, j) :=
begin
  let [ident l] [":", expr «expr →₀ »(ι, R)] [":=", expr «expr - »(finsupp.single i c, finsupp.single j d)],
  have [ident h_total] [":", expr «expr = »(finsupp.total ι M R v l, 0)] [],
  { simp_rw ["[", expr linear_map.map_sub, ",", expr finsupp.total_apply, "]"] [],
    simp [] [] [] ["[", expr h, "]"] [] [] },
  have [ident h_single_eq] [":", expr «expr = »(finsupp.single i c, finsupp.single j d)] [],
  { rw [expr linear_independent_iff] ["at", ident li],
    simp [] [] [] ["[", expr eq_add_of_sub_eq' (li l h_total), "]"] [] [] },
  rcases [expr (finsupp.single_eq_single_iff _ _ _ _).mp h_single_eq, "with", "⟨", ident this, ",", "_", "⟩", "|", "⟨", ident hc, ",", "_", "⟩"],
  { exact [expr this] },
  { contradiction }
end

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/


-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent.disjoint_span_image
(hv : linear_independent R v)
{s t : set ι}
(hs : disjoint s t) : disjoint «expr $ »(submodule.span R, «expr '' »(v, s)) «expr $ »(submodule.span R, «expr '' »(v, t)) :=
begin
  simp [] [] ["only"] ["[", expr disjoint_def, ",", expr finsupp.mem_span_image_iff_total, "]"] [] [],
  rintros ["_", "⟨", ident l₁, ",", ident hl₁, ",", ident rfl, "⟩", "⟨", ident l₂, ",", ident hl₂, ",", ident H, "⟩"],
  rw ["[", expr hv.injective_total.eq_iff, "]"] ["at", ident H],
  subst [expr l₂],
  have [] [":", expr «expr = »(l₁, 0)] [":=", expr finsupp.disjoint_supported_supported hs (submodule.mem_inf.2 ⟨hl₁, hl₂⟩)],
  simp [] [] [] ["[", expr this, "]"] [] []
end

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent.not_mem_span_image
[nontrivial R]
(hv : linear_independent R v)
{s : set ι}
{x : ι}
(h : «expr ∉ »(x, s)) : «expr ∉ »(v x, submodule.span R «expr '' »(v, s)) :=
begin
  have [ident h'] [":", expr «expr ∈ »(v x, submodule.span R «expr '' »(v, {x}))] [],
  { rw [expr set.image_singleton] [],
    exact [expr mem_span_singleton_self (v x)] },
  intro [ident w],
  apply [expr linear_independent.ne_zero x hv],
  refine [expr disjoint_def.1 (hv.disjoint_span_image _) (v x) h' w],
  simpa [] [] [] [] [] ["using", expr h]
end

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent.total_ne_of_not_mem_support
[nontrivial R]
(hv : linear_independent R v)
{x : ι}
(f : «expr →₀ »(ι, R))
(h : «expr ∉ »(x, f.support)) : «expr ≠ »(finsupp.total ι M R v f, v x) :=
begin
  replace [ident h] [":", expr «expr ∉ »(x, (f.support : set ι))] [":=", expr h],
  have [ident p] [] [":=", expr hv.not_mem_span_image h],
  intro [ident w],
  rw ["<-", expr w] ["at", ident p],
  rw [expr finsupp.span_image_eq_map_total] ["at", ident p],
  simp [] [] ["only"] ["[", expr not_exists, ",", expr not_and, ",", expr mem_map, "]"] [] ["at", ident p],
  exact [expr p f (f.mem_supported_support R) rfl]
end

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent_sum
{v : «expr ⊕ »(ι, ι') → M} : «expr ↔ »(linear_independent R v, «expr ∧ »(linear_independent R «expr ∘ »(v, sum.inl), «expr ∧ »(linear_independent R «expr ∘ »(v, sum.inr), disjoint (submodule.span R (range «expr ∘ »(v, sum.inl))) (submodule.span R (range «expr ∘ »(v, sum.inr)))))) :=
begin
  rw ["[", expr range_comp v, ",", expr range_comp v, "]"] [],
  refine [expr ⟨λ
    h, ⟨h.comp _ sum.inl_injective, h.comp _ sum.inr_injective, h.disjoint_span_image is_compl_range_inl_range_inr.1⟩, _⟩],
  rintro ["⟨", ident hl, ",", ident hr, ",", ident hlr, "⟩"],
  rw ["[", expr linear_independent_iff', "]"] ["at", "*"],
  intros [ident s, ident g, ident hg, ident i, ident hi],
  have [] [":", expr «expr = »(«expr + »(«expr∑ in , »((i), s.preimage sum.inl (sum.inl_injective.inj_on _), λ
      x, «expr • »(g x, v x) (sum.inl i)), «expr∑ in , »((i), s.preimage sum.inr (sum.inr_injective.inj_on _), λ
      x, «expr • »(g x, v x) (sum.inr i))), 0)] [],
  { rw ["[", expr finset.sum_preimage', ",", expr finset.sum_preimage', ",", "<-", expr finset.sum_union, ",", "<-", expr finset.filter_or, "]"] [],
    { simpa [] [] ["only"] ["[", "<-", expr mem_union, ",", expr range_inl_union_range_inr, ",", expr mem_univ, ",", expr finset.filter_true, "]"] [] [] },
    { exact [expr finset.disjoint_filter.2 (λ x hx, disjoint_left.1 is_compl_range_inl_range_inr.1)] } },
  { rw ["<-", expr eq_neg_iff_add_eq_zero] ["at", ident this],
    rw ["[", expr disjoint_def', "]"] ["at", ident hlr],
    have [ident A] [] [":=", expr hlr _ «expr $ »(sum_mem _, λ
      i hi, _) _ «expr $ »(neg_mem _, «expr $ »(sum_mem _, λ i hi, _)) this],
    { cases [expr i] ["with", ident i, ident i],
      { exact [expr hl _ _ A i (finset.mem_preimage.2 hi)] },
      { rw ["[", expr this, ",", expr neg_eq_zero, "]"] ["at", ident A],
        exact [expr hr _ _ A i (finset.mem_preimage.2 hi)] } },
    { exact [expr smul_mem _ _ (subset_span ⟨sum.inl i, mem_range_self _, rfl⟩)] },
    { exact [expr smul_mem _ _ (subset_span ⟨sum.inr i, mem_range_self _, rfl⟩)] } }
end

theorem LinearIndependent.sum_type {v' : ι' → M} (hv : LinearIndependent R v) (hv' : LinearIndependent R v')
  (h : Disjoint (Submodule.span R (range v)) (Submodule.span R (range v'))) : LinearIndependent R (Sum.elim v v') :=
  linear_independent_sum.2 ⟨hv, hv', h⟩

theorem LinearIndependent.union {s t : Set M} (hs : LinearIndependent R (fun x => x : s → M))
  (ht : LinearIndependent R (fun x => x : t → M)) (hst : Disjoint (span R s) (span R t)) :
  LinearIndependent R (fun x => x : s ∪ t → M) :=
  (hs.sum_type ht$
        by 
          simpa).to_subtype_range'$
    by 
      simp 

theorem linear_independent_Union_finite_subtype {ι : Type _} {f : ι → Set M}
  (hl : ∀ i, LinearIndependent R (fun x => x : f i → M))
  (hd : ∀ i, ∀ (t : Set ι), finite t → i ∉ t → Disjoint (span R (f i)) (⨆(i : _)(_ : i ∈ t), span R (f i))) :
  LinearIndependent R (fun x => x : (⋃i, f i) → M) :=
  by 
    rw [Union_eq_Union_finset f]
    apply linear_independent_Union_of_directed
    ·
      apply directed_of_sup 
      exact fun t₁ t₂ ht => Union_subset_Union$ fun i => Union_subset_Union_const$ fun h => ht h 
    intro t 
    induction' t using Finset.induction_on with i s his ih
    ·
      refine' (linear_independent_empty _ _).mono _ 
      simp 
    ·
      rw [Finset.set_bUnion_insert]
      refine' (hl _).union ih _ 
      refine' (hd i s s.finite_to_set his).mono_right _ 
      simp only [(span_Union _).symm]
      refine' span_mono (@supr_le_supr2 (Set M) _ _ _ _ _ _)
      exact fun i => ⟨i, le_rfl⟩

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent_Union_finite
{η : Type*}
{ιs : η → Type*}
{f : ∀ j : η, ιs j → M}
(hindep : ∀ j, linear_independent R (f j))
(hd : ∀
 i, ∀
 t : set η, finite t → «expr ∉ »(i, t) → disjoint (span R (range (f i))) «expr⨆ , »((i «expr ∈ » t), span R (range (f i)))) : linear_independent R (λ
 ji : «exprΣ , »((j), ιs j), f ji.1 ji.2) :=
begin
  nontriviality [expr R] [],
  apply [expr linear_independent.of_subtype_range],
  { rintros ["⟨", ident x₁, ",", ident x₂, "⟩", "⟨", ident y₁, ",", ident y₂, "⟩", ident hxy],
    by_cases [expr h_cases, ":", expr «expr = »(x₁, y₁)],
    subst [expr h_cases],
    { apply [expr sigma.eq],
      rw [expr linear_independent.injective (hindep _) hxy] [],
      refl },
    { have [ident h0] [":", expr «expr = »(f x₁ x₂, 0)] [],
      { apply [expr disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) (λ
           h, h_cases (eq_of_mem_singleton h))) (f x₁ x₂) (subset_span (mem_range_self _))],
        rw [expr supr_singleton] [],
        simp [] [] ["only"] [] [] ["at", ident hxy],
        rw [expr hxy] [],
        exact [expr subset_span (mem_range_self y₂)] },
      exact [expr false.elim ((hindep x₁).ne_zero _ h0)] } },
  rw [expr range_sigma_eq_Union_range] [],
  apply [expr linear_independent_Union_finite_subtype (λ j, (hindep j).to_subtype_range) hd]
end

end Subtype

section reprₓ

variable(hv : LinearIndependent R v)

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
@[simps]
def LinearIndependent.totalEquiv (hv : LinearIndependent R v) : (ι →₀ R) ≃ₗ[R] span R (range v) :=
  by 
    apply LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v)) (Finsupp.total ι M R v) _)
    ·
      rw [←LinearMap.ker_eq_bot, LinearMap.ker_cod_restrict]
      apply hv
    ·
      rw [←LinearMap.range_eq_top, LinearMap.range_eq_map, LinearMap.map_cod_restrict, ←LinearMap.range_le_iff_comap,
        range_subtype, map_top]
      rw [Finsupp.range_total]
      apply le_reflₓ (span R (range v))
    ·
      intro l 
      rw [←Finsupp.range_total]
      rw [LinearMap.mem_range]
      apply mem_range_self l

/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `linear_independent.total_equiv`. -/
def LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) →ₗ[R] ι →₀ R :=
  hv.total_equiv.symm

@[simp]
theorem LinearIndependent.total_repr x : Finsupp.total ι M R v (hv.repr x) = x :=
  Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.total_equiv x)

theorem LinearIndependent.total_comp_repr : (Finsupp.total ι M R v).comp hv.repr = Submodule.subtype _ :=
  LinearMap.ext$ hv.total_repr

theorem LinearIndependent.repr_ker : hv.repr.ker = ⊥ :=
  by 
    rw [LinearIndependent.repr, LinearEquiv.ker]

theorem LinearIndependent.repr_range : hv.repr.range = ⊤ :=
  by 
    rw [LinearIndependent.repr, LinearEquiv.range]

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent.repr_eq
{l : «expr →₀ »(ι, R)}
{x}
(eq : «expr = »(finsupp.total ι M R v l, «expr↑ »(x))) : «expr = »(hv.repr x, l) :=
begin
  have [] [":", expr «expr = »(«expr↑ »((linear_independent.total_equiv hv : «expr →ₗ[ ] »(«expr →₀ »(ι, R), R, span R (range v))) l), finsupp.total ι M R v l)] [":=", expr rfl],
  have [] [":", expr «expr = »((linear_independent.total_equiv hv : «expr →ₗ[ ] »(«expr →₀ »(ι, R), R, span R (range v))) l, x)] [],
  { rw [expr eq] ["at", ident this],
    exact [expr subtype.ext_iff.2 this] },
  rw ["<-", expr linear_equiv.symm_apply_apply hv.total_equiv l] [],
  rw ["<-", expr this] [],
  refl
end

theorem LinearIndependent.repr_eq_single i x (hx : «expr↑ » x = v i) : hv.repr x = Finsupp.single i 1 :=
  by 
    apply hv.repr_eq 
    simp [Finsupp.total_single, hx]

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent.span_repr_eq
[nontrivial R]
(x) : «expr = »(span.repr R (set.range v) x, (hv.repr x).equiv_map_domain (equiv.of_injective _ hv.injective)) :=
begin
  have [ident p] [":", expr «expr = »((span.repr R (set.range v) x).equiv_map_domain (equiv.of_injective _ hv.injective).symm, hv.repr x)] [],
  { apply [expr (linear_independent.total_equiv hv).injective],
    ext [] [] [],
    simp [] [] [] [] [] [] },
  ext [] ["⟨", "_", ",", "⟨", ident i, ",", ident rfl, "⟩", "⟩"] [],
  simp [] [] [] ["[", "<-", expr p, "]"] [] []
end

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem linear_independent_iff_not_smul_mem_span : «expr ↔ »(linear_independent R v, ∀
 (i : ι)
 (a : R), «expr ∈ »(«expr • »(a, v i), span R «expr '' »(v, «expr \ »(univ, {i}))) → «expr = »(a, 0)) :=
⟨λ hv i a ha, begin
   rw ["[", expr finsupp.span_image_eq_map_total, ",", expr mem_map, "]"] ["at", ident ha],
   rcases [expr ha, "with", "⟨", ident l, ",", ident hl, ",", ident e, "⟩"],
   rw [expr sub_eq_zero.1 (linear_independent_iff.1 hv «expr - »(l, finsupp.single i a) (by simp [] [] [] ["[", expr e, "]"] [] []))] ["at", ident hl],
   by_contra [ident hn],
   exact [expr not_mem_of_mem_diff «expr $ »(hl, by simp [] [] [] ["[", expr hn, "]"] [] []) (mem_singleton _)]
 end, λ
 H, «expr $ »(linear_independent_iff.2, λ l hl, begin
    ext [] [ident i] [],
    simp [] [] ["only"] ["[", expr finsupp.zero_apply, "]"] [] [],
    by_contra [ident hn],
    refine [expr hn (H i _ _)],
    refine [expr (finsupp.mem_span_image_iff_total _).2 ⟨«expr - »(finsupp.single i (l i), l), _, _⟩],
    { rw [expr finsupp.mem_supported'] [],
      intros [ident j, ident hj],
      have [ident hij] [":", expr «expr = »(j, i)] [":=", expr not_not.1 (λ
        hij : «expr ≠ »(j, i), hj ((mem_diff _).2 ⟨mem_univ _, λ h, hij (eq_of_mem_singleton h)⟩))],
      simp [] [] [] ["[", expr hij, "]"] [] [] },
    { simp [] [] [] ["[", expr hl, "]"] [] [] }
  end)⟩

variable(R)

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_maximal_independent'
(s : ι → M) : «expr∃ , »((I : set ι), «expr ∧ »(linear_independent R (λ
   x : I, s x), ∀ J : set ι, «expr ⊆ »(I, J) → linear_independent R (λ x : J, s x) → «expr = »(I, J))) :=
begin
  let [ident indep] [":", expr set ι → exprProp()] [":=", expr λ I, linear_independent R («expr ∘ »(s, coe) : I → M)],
  let [ident X] [] [":=", expr {I : set ι // indep I}],
  let [ident r] [":", expr X → X → exprProp()] [":=", expr λ I J, «expr ⊆ »(I.1, J.1)],
  have [ident key] [":", expr ∀ c : set X, zorn.chain r c → indep «expr⋃ , »((I : X) (H : «expr ∈ »(I, c)), I)] [],
  { intros [ident c, ident hc],
    dsimp [] ["[", expr indep, "]"] [] [],
    rw ["[", expr linear_independent_comp_subtype, "]"] [],
    intros [ident f, ident hsupport, ident hsum],
    rcases [expr eq_empty_or_nonempty c, "with", ident rfl, "|", "⟨", ident a, ",", ident hac, "⟩"],
    { simpa [] [] [] [] [] ["using", expr hsupport] },
    haveI [] [":", expr is_refl X r] [":=", expr ⟨λ _, set.subset.refl _⟩],
    obtain ["⟨", ident I, ",", ident I_mem, ",", ident hI, "⟩", ":", expr «expr∃ , »((I «expr ∈ » c), «expr ⊆ »((f.support : set ι), I)), ":=", expr finset.exists_mem_subset_of_subset_bUnion_of_directed_on hac hc.directed_on hsupport],
    exact [expr linear_independent_comp_subtype.mp I.2 f hI hsum] },
  have [ident trans] [":", expr transitive r] [":=", expr λ I J K, set.subset.trans],
  obtain ["⟨", "⟨", ident I, ",", ident hli, ":", expr indep I, "⟩", ",", ident hmax, ":", expr ∀
   a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩, "⟩", ":=", expr @zorn.exists_maximal_of_chains_bounded _ r (λ
    c hc, ⟨⟨«expr⋃ , »((I «expr ∈ » c), (I : set ι)), key c hc⟩, λ I, set.subset_bUnion_of_mem⟩) trans],
  exact [expr ⟨I, hli, λ J hsub hli, set.subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩]
end

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_maximal_independent
(s : ι → M) : «expr∃ , »((I : set ι), «expr ∧ »(linear_independent R (λ
   x : I, s x), ∀
  i «expr ∉ » I, «expr∃ , »((a : R), «expr ∧ »(«expr ≠ »(a, 0), «expr ∈ »(«expr • »(a, s i), span R «expr '' »(s, I)))))) :=
begin
  classical,
  rcases [expr exists_maximal_independent' R s, "with", "⟨", ident I, ",", ident hIlinind, ",", ident hImaximal, "⟩"],
  use ["[", expr I, ",", expr hIlinind, "]"],
  intros [ident i, ident hi],
  specialize [expr hImaximal «expr ∪ »(I, {i}) (by simp [] [] [] [] [] [])],
  set [] [ident J] [] [":="] [expr «expr ∪ »(I, {i})] ["with", ident hJ],
  have [ident memJ] [":", expr ∀ {x}, «expr ↔ »(«expr ∈ »(x, J), «expr ∨ »(«expr = »(x, i), «expr ∈ »(x, I)))] [],
  by simp [] [] [] ["[", expr hJ, "]"] [] [],
  have [ident hiJ] [":", expr «expr ∈ »(i, J)] [":=", expr by simp [] [] [] [] [] []],
  have [ident h] [] [":=", expr mt hImaximal _],
  swap,
  { intro [ident h2],
    rw [expr h2] ["at", ident hi],
    exact [expr absurd hiJ hi] },
  obtain ["⟨", ident f, ",", ident supp_f, ",", ident sum_f, ",", ident f_ne, "⟩", ":=", expr linear_dependent_comp_subtype.mp h],
  have [ident hfi] [":", expr «expr ≠ »(f i, 0)] [],
  { contrapose [] [ident hIlinind],
    refine [expr linear_dependent_comp_subtype.mpr ⟨f, _, sum_f, f_ne⟩],
    simp [] [] ["only"] ["[", expr finsupp.mem_supported, ",", expr hJ, "]"] [] ["at", "⊢", ident supp_f],
    rintro [ident x, ident hx],
    refine [expr (memJ.mp (supp_f hx)).resolve_left _],
    rintro [ident rfl],
    exact [expr hIlinind (finsupp.mem_support_iff.mp hx)] },
  use ["[", expr f i, ",", expr hfi, "]"],
  have [ident hfi'] [":", expr «expr ∈ »(i, f.support)] [":=", expr finsupp.mem_support_iff.mpr hfi],
  rw ["[", "<-", expr finset.insert_erase hfi', ",", expr finset.sum_insert (finset.not_mem_erase _ _), ",", expr add_eq_zero_iff_eq_neg, "]"] ["at", ident sum_f],
  rw [expr sum_f] [],
  refine [expr neg_mem _ (sum_mem _ (λ c hc, smul_mem _ _ (subset_span ⟨c, _, rfl⟩)))],
  exact [expr (memJ.mp (supp_f (finset.erase_subset _ _ hc))).resolve_left (finset.ne_of_mem_erase hc)]
end

end reprₓ

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem surjective_of_linear_independent_of_span
[nontrivial R]
(hv : linear_independent R v)
(f : «expr ↪ »(ι', ι))
(hss : «expr ⊆ »(range v, span R (range «expr ∘ »(v, f)))) : surjective f :=
begin
  intros [ident i],
  let [ident repr] [":", expr (span R (range «expr ∘ »(v, f)) : Type*) → «expr →₀ »(ι', R)] [":=", expr (hv.comp f f.injective).repr],
  let [ident l] [] [":=", expr (repr ⟨v i, hss (mem_range_self i)⟩).map_domain f],
  have [ident h_total_l] [":", expr «expr = »(finsupp.total ι M R v l, v i)] [],
  { dsimp ["only"] ["[", expr l, "]"] [] [],
    rw [expr finsupp.total_map_domain] [],
    rw [expr (hv.comp f f.injective).total_repr] [],
    { refl },
    { exact [expr f.injective] } },
  have [ident h_total_eq] [":", expr «expr = »(finsupp.total ι M R v l, finsupp.total ι M R v (finsupp.single i 1))] [],
  by rw ["[", expr h_total_l, ",", expr finsupp.total_single, ",", expr one_smul, "]"] [],
  have [ident l_eq] [":", expr «expr = »(l, _)] [":=", expr linear_map.ker_eq_bot.1 hv h_total_eq],
  dsimp ["only"] ["[", expr l, "]"] [] ["at", ident l_eq],
  rw ["<-", expr finsupp.emb_domain_eq_map_domain] ["at", ident l_eq],
  rcases [expr finsupp.single_of_emb_domain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq, "with", "⟨", ident i', ",", ident hi', "⟩"],
  use [expr i'],
  exact [expr hi'.2]
end

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_linear_independent_of_span_subtype
[nontrivial R]
{s t : set M}
(hs : linear_independent R (λ x, x : s → M))
(h : «expr ⊆ »(t, s))
(hst : «expr ⊆ »(s, span R t)) : «expr = »(s, t) :=
begin
  let [ident f] [":", expr «expr ↪ »(t, s)] [":=", expr ⟨λ
    x, ⟨x.1, h x.2⟩, λ a b hab, subtype.coe_injective (subtype.mk.inj hab)⟩],
  have [ident h_surj] [":", expr surjective f] [],
  { apply [expr surjective_of_linear_independent_of_span hs f _],
    convert [] [expr hst] []; simp [] [] [] ["[", expr f, ",", expr comp, "]"] [] [] },
  show [expr «expr = »(s, t)],
  { apply [expr subset.antisymm _ h],
    intros [ident x, ident hx],
    rcases [expr h_surj ⟨x, hx⟩, "with", "⟨", ident y, ",", ident hy, "⟩"],
    convert [] [expr y.mem] [],
    rw ["<-", expr subtype.mk.inj hy] [],
    refl }
end

open LinearMap

theorem LinearIndependent.image_subtype {s : Set M} {f : M →ₗ[R] M'} (hs : LinearIndependent R (fun x => x : s → M))
  (hf_inj : Disjoint (span R s) f.ker) : LinearIndependent R (fun x => x : f '' s → M') :=
  by 
    rw [←@Subtype.range_coe _ s] at hf_inj 
    refine' (hs.map hf_inj).to_subtype_range' _ 
    simp [Set.range_comp f]

theorem LinearIndependent.inl_union_inr {s : Set M} {t : Set M'} (hs : LinearIndependent R (fun x => x : s → M))
  (ht : LinearIndependent R (fun x => x : t → M')) :
  LinearIndependent R (fun x => x : inl R M M' '' s ∪ inr R M M' '' t → M × M') :=
  by 
    refine' (hs.image_subtype _).union (ht.image_subtype _) _ <;> [simp , simp , skip]
    simp only [span_image]
    simp [disjoint_iff, prod_inf_prod]

theorem linear_independent_inl_union_inr' {v : ι → M} {v' : ι' → M'} (hv : LinearIndependent R v)
  (hv' : LinearIndependent R v') : LinearIndependent R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) :=
  (hv.map' (inl R M M') ker_inl).sum_type (hv'.map' (inr R M M') ker_inr)$
    by 
      refine' is_compl_range_inl_inr.disjoint.mono _ _ <;> simp only [span_le, range_coe, range_comp_subset_range]

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Dedekind's linear independence of characters -/
theorem linear_independent_monoid_hom
(G : Type*)
[monoid G]
(L : Type*)
[comm_ring L]
[no_zero_divisors L] : @linear_independent _ L (G → L) (λ f, f : «expr →* »(G, L) → G → L) _ _ _ :=
by letI [] [] [":=", expr classical.dec_eq «expr →* »(G, L)]; letI [] [":", expr mul_action L L] [":=", expr distrib_mul_action.to_mul_action]; exact [expr linear_independent_iff'.2 (λ
  s, «expr $ »(finset.induction_on s (λ
    g
    hg
    i, false.elim), λ
   a
   s
   has
   ih
   g
   hg, have h1 : ∀
   i «expr ∈ » s, «expr = »((«expr • »(g i, i) : G → L), «expr • »(g i, a)), from λ
   i
   his, «expr $ »(funext, λ
    x : G, «expr $ »(eq_of_sub_eq_zero, ih (λ
      j, «expr - »(«expr * »(g j, j x), «expr * »(g j, a x))) «expr $ »(funext, λ y : G, calc
        «expr = »(«expr∑ in , »((i), s, («expr • »(«expr - »(«expr * »(g i, i x), «expr * »(g i, a x)), i) : G → L)) y, «expr∑ in , »((i), s, «expr * »(«expr - »(«expr * »(g i, i x), «expr * »(g i, a x)), i y))) : finset.sum_apply _ _ _
        «expr = »(..., «expr∑ in , »((i), s, «expr - »(«expr * »(«expr * »(g i, i x), i y), «expr * »(«expr * »(g i, a x), i y)))) : finset.sum_congr rfl (λ
         _ _, sub_mul _ _ _)
        «expr = »(..., «expr - »(«expr∑ in , »((i), s, «expr * »(«expr * »(g i, i x), i y)), «expr∑ in , »((i), s, «expr * »(«expr * »(g i, a x), i y)))) : finset.sum_sub_distrib
        «expr = »(..., «expr - »(«expr + »(«expr * »(«expr * »(g a, a x), a y), «expr∑ in , »((i), s, «expr * »(«expr * »(g i, i x), i y))), «expr + »(«expr * »(«expr * »(g a, a x), a y), «expr∑ in , »((i), s, «expr * »(«expr * »(g i, a x), i y))))) : by rw [expr add_sub_add_left_eq_sub] []
        «expr = »(..., «expr - »(«expr∑ in , »((i), insert a s, «expr * »(«expr * »(g i, i x), i y)), «expr∑ in , »((i), insert a s, «expr * »(«expr * »(g i, a x), i y)))) : by rw ["[", expr finset.sum_insert has, ",", expr finset.sum_insert has, "]"] []
        «expr = »(..., «expr - »(«expr∑ in , »((i), insert a s, «expr * »(g i, i «expr * »(x, y))), «expr∑ in , »((i), insert a s, «expr * »(a x, «expr * »(g i, i y))))) : congr (congr_arg has_sub.sub «expr $ »(finset.sum_congr rfl, λ
          i
          _, by rw ["[", expr i.map_mul, ",", expr mul_assoc, "]"] [])) «expr $ »(finset.sum_congr rfl, λ
         _ _, by rw ["[", expr mul_assoc, ",", expr mul_left_comm, "]"] [])
        «expr = »(..., «expr - »(«expr∑ in , »((i), insert a s, («expr • »(g i, i) : G → L)) «expr * »(x, y), «expr * »(a x, «expr∑ in , »((i), insert a s, («expr • »(g i, i) : G → L)) y))) : by rw ["[", expr finset.sum_apply, ",", expr finset.sum_apply, ",", expr finset.mul_sum, "]"] []; refl
        «expr = »(..., «expr - »(0, «expr * »(a x, 0))) : by rw [expr hg] []; refl
        «expr = »(..., 0) : by rw ["[", expr mul_zero, ",", expr sub_zero, "]"] []) i his)),
   have h2 : ∀
   i : «expr →* »(G, L), «expr ∈ »(i, s) → «expr∃ , »((y), «expr ≠ »(i y, a y)), from λ
   i
   his, «expr $ »(classical.by_contradiction, λ
    h, have hia : «expr = »(i, a), from «expr $ »(monoid_hom.ext, λ
     y, «expr $ »(classical.by_contradiction, λ hy, h ⟨y, hy⟩)),
    «expr $ »(has, «expr ▸ »(hia, his))),
   have h3 : ∀ i «expr ∈ » s, «expr = »(g i, 0), from λ i his, let ⟨y, hy⟩ := h2 i his in
   have h : «expr = »(«expr • »(g i, i y), «expr • »(g i, a y)), from congr_fun (h1 i his) y,
   or.resolve_right «expr $ »(mul_eq_zero.1, by rw ["[", expr mul_sub, ",", expr sub_eq_zero, "]"] []; exact [expr h]) (sub_ne_zero_of_ne hy),
   have h4 : «expr = »(g a, 0), from calc
     «expr = »(g a, «expr * »(g a, 1)) : (mul_one _).symm
     «expr = »(..., («expr • »(g a, a) : G → L) 1) : by rw ["<-", expr a.map_one] []; refl
     «expr = »(..., «expr∑ in , »((i), insert a s, («expr • »(g i, i) : G → L)) 1) : begin
       rw [expr finset.sum_eq_single a] [],
       { intros [ident i, ident his, ident hia],
         rw [expr finset.mem_insert] ["at", ident his],
         rw ["[", expr h3 i (his.resolve_left hia), ",", expr zero_smul, "]"] [] },
       { intros [ident haas],
         exfalso,
         apply [expr haas],
         exact [expr finset.mem_insert_self a s] }
     end
     «expr = »(..., 0) : by rw [expr hg] []; refl,
   (finset.forall_mem_insert _ _ _).2 ⟨h4, h3⟩))]

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_of_span_le_span
[nontrivial R]
{s t u : set M}
(hl : linear_independent R (coe : u → M))
(hsu : «expr ⊆ »(s, u))
(htu : «expr ⊆ »(t, u))
(hst : «expr ≤ »(span R s, span R t)) : «expr ⊆ »(s, t) :=
begin
  have [] [] [":=", expr eq_of_linear_independent_of_span_subtype (hl.mono (set.union_subset hsu htu)) (set.subset_union_right _ _) (set.union_subset (set.subset.trans subset_span hst) subset_span)],
  rw ["<-", expr this] [],
  apply [expr set.subset_union_left]
end

theorem span_le_span_iff [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R (coeₓ : u → M)) (hsu : s ⊆ u)
  (htu : t ⊆ u) : span R s ≤ span R t ↔ s ⊆ t :=
  ⟨le_of_span_le_span hl hsu htu, span_mono⟩

end Module

section Nontrivial

variable[Ringₓ R][Nontrivial R][AddCommGroupₓ M][AddCommGroupₓ M']

variable[Module R M][NoZeroSmulDivisors R M][Module R M']

variable{v : ι → M}{s t : Set M}{x y z : M}

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent_unique_iff
(v : ι → M)
[unique ι] : «expr ↔ »(linear_independent R v, «expr ≠ »(v (default ι), 0)) :=
begin
  simp [] [] ["only"] ["[", expr linear_independent_iff, ",", expr finsupp.total_unique, ",", expr smul_eq_zero, "]"] [] [],
  refine [expr ⟨λ h hv, _, λ hv l hl, «expr $ »(finsupp.unique_ext, hl.resolve_right hv)⟩],
  have [] [] [":=", expr h (finsupp.single (default ι) 1) (or.inr hv)],
  exact [expr one_ne_zero (finsupp.single_eq_zero.1 this)]
end

alias linear_independent_unique_iff ↔ _ linear_independent_unique

theorem linear_independent_singleton {x : M} (hx : x ≠ 0) : LinearIndependent R (fun x => x : ({x} : Set M) → M) :=
  linear_independent_unique coeₓ hx

end Nontrivial

/-!
### Properties which require `division_ring K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable[DivisionRing K][AddCommGroupₓ V][AddCommGroupₓ V']

variable[Module K V][Module K V']

variable{v : ι → V}{s t : Set V}{x y z : V}

open Submodule

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_span_insert_exchange : «expr ∈ »(x, span K (insert y s)) → «expr ∉ »(x, span K s) → «expr ∈ »(y, span K (insert x s)) :=
begin
  simp [] [] [] ["[", expr mem_span_insert, "]"] [] [],
  rintro [ident a, ident z, ident hz, ident rfl, ident h],
  refine [expr ⟨«expr ⁻¹»(a), «expr • »(«expr- »(«expr ⁻¹»(a)), z), smul_mem _ _ hz, _⟩],
  have [ident a0] [":", expr «expr ≠ »(a, 0)] [],
  { rintro [ident rfl],
    simp [] [] [] ["*"] [] ["at", "*"] },
  simp [] [] [] ["[", expr a0, ",", expr smul_add, ",", expr smul_smul, "]"] [] []
end

theorem linear_independent_iff_not_mem_span : LinearIndependent K v ↔ ∀ i, v i ∉ span K (v '' (univ \ {i})) :=
  by 
    apply linear_independent_iff_not_smul_mem_span.trans 
    split 
    ·
      intro h i h_in_span 
      apply
        one_ne_zero
          (h i 1
            (by 
              simp [h_in_span]))
    ·
      intro h i a ha 
      byContra ha' 
      exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent.insert
(hs : linear_independent K (λ b, b : s → V))
(hx : «expr ∉ »(x, span K s)) : linear_independent K (λ b, b : insert x s → V) :=
begin
  rw ["<-", expr union_singleton] [],
  have [ident x0] [":", expr «expr ≠ »(x, 0)] [":=", expr mt (by rintro [ident rfl]; apply [expr zero_mem _]) hx],
  apply [expr hs.union (linear_independent_singleton x0)],
  rwa ["[", expr disjoint_span_singleton' x0, "]"] []
end

theorem linear_independent_option' :
  LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) ↔
    LinearIndependent K v ∧ x ∉ Submodule.span K (range v) :=
  by 
    rw [←linear_independent_equiv (Equiv.optionEquivSumPunit ι).symm, linear_independent_sum, @range_unique _ PUnit,
      @linear_independent_unique_iff PUnit, disjoint_span_singleton]
    dsimp [· ∘ ·]
    refine' ⟨fun h => ⟨h.1, fun hx => h.2.1$ h.2.2 hx⟩, fun h => ⟨h.1, _, fun hx => (h.2 hx).elim⟩⟩
    rintro rfl 
    exact h.2 (zero_mem _)

theorem LinearIndependent.option (hv : LinearIndependent K v) (hx : x ∉ Submodule.span K (range v)) :
  LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) :=
  linear_independent_option'.2 ⟨hv, hx⟩

theorem linear_independent_option {v : Option ι → V} :
  LinearIndependent K v ↔
    LinearIndependent K (v ∘ coeₓ : ι → V) ∧ v none ∉ Submodule.span K (range (v ∘ coeₓ : ι → V)) :=
  by 
    simp only [←linear_independent_option', Option.cases_on'_none_coe]

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem linear_independent_insert'
{ι}
{s : set ι}
{a : ι}
{f : ι → V}
(has : «expr ∉ »(a, s)) : «expr ↔ »(linear_independent K (λ
  x : insert a s, f x), «expr ∧ »(linear_independent K (λ
   x : s, f x), «expr ∉ »(f a, submodule.span K «expr '' »(f, s)))) :=
by { rw ["[", "<-", expr linear_independent_equiv ((equiv.option_equiv_sum_punit _).trans (equiv.set.insert has).symm), ",", expr linear_independent_option, "]"] [],
  simp [] [] [] ["[", expr («expr ∘ »), ",", expr range_comp f, "]"] [] [] }

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem linear_independent_insert
(hxs : «expr ∉ »(x, s)) : «expr ↔ »(linear_independent K (λ
  b : insert x s, (b : V)), «expr ∧ »(linear_independent K (λ b : s, (b : V)), «expr ∉ »(x, submodule.span K s))) :=
«expr $ »((@linear_independent_insert' _ _ _ _ _ _ _ _ id hxs).trans, by simp [] [] [] [] [] [])

theorem linear_independent_pair {x y : V} (hx : x ≠ 0) (hy : ∀ (a : K), a • x ≠ y) :
  LinearIndependent K (coeₓ : ({x, y} : Set V) → V) :=
  pair_comm y x ▸ (linear_independent_singleton hx).insert$ mt mem_span_singleton.1 (not_exists.2 hy)

theorem linear_independent_fin_cons {n} {v : Finₓ n → V} :
  LinearIndependent K (Finₓ.cons x v : Finₓ (n+1) → V) ↔ LinearIndependent K v ∧ x ∉ Submodule.span K (range v) :=
  by 
    rw [←linear_independent_equiv (finSuccEquiv n).symm, linear_independent_option]
    convert Iff.rfl
    ·
      ext 
      rw [comp_app, comp_app, fin_succ_equiv_symm_coe, Finₓ.cons_succ]
    ·
      ext 
      rw [comp_app, comp_app, fin_succ_equiv_symm_coe, Finₓ.cons_succ]

theorem linear_independent_fin_snoc {n} {v : Finₓ n → V} :
  LinearIndependent K (Finₓ.snoc v x : Finₓ (n+1) → V) ↔ LinearIndependent K v ∧ x ∉ Submodule.span K (range v) :=
  by 
    rw [Finₓ.snoc_eq_cons_rotate, linear_independent_equiv, linear_independent_fin_cons]

/-- See `linear_independent.fin_cons'` for an uglier version that works if you
only have a module over a semiring. -/
theorem LinearIndependent.fin_cons {n} {v : Finₓ n → V} (hv : LinearIndependent K v)
  (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Finₓ.cons x v : Finₓ (n+1) → V) :=
  linear_independent_fin_cons.2 ⟨hv, hx⟩

theorem linear_independent_fin_succ {n} {v : Finₓ (n+1) → V} :
  LinearIndependent K v ↔ LinearIndependent K (Finₓ.tail v) ∧ v 0 ∉ Submodule.span K (range$ Finₓ.tail v) :=
  by 
    rw [←linear_independent_fin_cons, Finₓ.cons_self_tail]

theorem linear_independent_fin_succ' {n} {v : Finₓ (n+1) → V} :
  LinearIndependent K v ↔ LinearIndependent K (Finₓ.init v) ∧ v (Finₓ.last _) ∉ Submodule.span K (range$ Finₓ.init v) :=
  by 
    rw [←linear_independent_fin_snoc, Finₓ.snoc_init_self]

theorem linear_independent_fin2 {f : Finₓ 2 → V} : LinearIndependent K f ↔ f 1 ≠ 0 ∧ ∀ (a : K), a • f 1 ≠ f 0 :=
  by 
    rw [linear_independent_fin_succ, linear_independent_unique_iff, range_unique, mem_span_singleton, not_exists,
      show Finₓ.tail f (default (Finₓ 1)) = f 1by 
        rw [←Finₓ.succ_zero_eq_one] <;> rfl]

theorem exists_linear_independent_extension (hs : LinearIndependent K (coeₓ : s → V)) (hst : s ⊆ t) :
  ∃ (b : _)(_ : b ⊆ t), s ⊆ b ∧ t ⊆ span K b ∧ LinearIndependent K (coeₓ : b → V) :=
  by 
    rcases Zorn.zorn_subset_nonempty { b | b ⊆ t ∧ LinearIndependent K (coeₓ : b → V) } _ _ ⟨hst, hs⟩ with
      ⟨b, ⟨bt, bi⟩, sb, h⟩
    ·
      refine' ⟨b, bt, sb, fun x xt => _, bi⟩
      byContra hn 
      apply hn 
      rw [←h _ ⟨insert_subset.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _)]
      exact subset_span (mem_insert _ _)
    ·
      refine' fun c hc cc c0 => ⟨⋃₀c, ⟨_, _⟩, fun x => _⟩
      ·
        exact sUnion_subset fun x xc => (hc xc).1
      ·
        exact linear_independent_sUnion_of_directed cc.directed_on fun x xc => (hc xc).2
      ·
        exact subset_sUnion_of_mem

variable(K t)

theorem exists_linear_independent : ∃ (b : _)(_ : b ⊆ t), span K b = span K t ∧ LinearIndependent K (coeₓ : b → V) :=
  by 
    obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
      exists_linear_independent_extension (linear_independent_empty K V) (Set.empty_subset t)
    exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩

variable{K t}

/-- `linear_independent.extend` adds vectors to a linear independent set `s ⊆ t` until it spans
all elements of `t`. -/
noncomputable def LinearIndependent.Extend (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) : Set V :=
  Classical.some (exists_linear_independent_extension hs hst)

theorem LinearIndependent.extend_subset (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) :
  hs.extend hst ⊆ t :=
  let ⟨hbt, hsb, htb, hli⟩ := Classical.some_spec (exists_linear_independent_extension hs hst)
  hbt

theorem LinearIndependent.subset_extend (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) :
  s ⊆ hs.extend hst :=
  let ⟨hbt, hsb, htb, hli⟩ := Classical.some_spec (exists_linear_independent_extension hs hst)
  hsb

theorem LinearIndependent.subset_span_extend (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) :
  t ⊆ span K (hs.extend hst) :=
  let ⟨hbt, hsb, htb, hli⟩ := Classical.some_spec (exists_linear_independent_extension hs hst)
  htb

theorem LinearIndependent.linear_independent_extend (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ t) :
  LinearIndependent K (coeₓ : hs.extend hst → V) :=
  let ⟨hbt, hsb, htb, hli⟩ := Classical.some_spec (exists_linear_independent_extension hs hst)
  hli

variable{K V}

-- error in LinearAlgebra.LinearIndependent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_of_linear_independent_of_finite_span
{t : finset V}
(hs : linear_independent K (λ x, x : s → V))
(hst : «expr ⊆ »(s, (span K «expr↑ »(t) : submodule K V))) : «expr∃ , »((t' : finset V), «expr ∧ »(«expr ⊆ »(«expr↑ »(t'), «expr ∪ »(s, «expr↑ »(t))), «expr ∧ »(«expr ⊆ »(s, «expr↑ »(t')), «expr = »(t'.card, t.card)))) :=
have ∀
t, ∀
s' : finset V, «expr ⊆ »(«expr↑ »(s'), s) → «expr = »(«expr ∩ »(s, «expr↑ »(t)), «expr∅»()) → «expr ⊆ »(s, (span K «expr↑ »(«expr ∪ »(s', t)) : submodule K V)) → «expr∃ , »((t' : finset V), «expr ∧ »(«expr ⊆ »(«expr↑ »(t'), «expr ∪ »(s, «expr↑ »(t))), «expr ∧ »(«expr ⊆ »(s, «expr↑ »(t')), «expr = »(t'.card, «expr ∪ »(s', t).card)))) := assume
t, finset.induction_on t (assume
 s'
 hs'
 _
 hss', have «expr = »(s, «expr↑ »(s')), from «expr $ »(eq_of_linear_independent_of_span_subtype hs hs', by simpa [] [] [] [] [] ["using", expr hss']),
 ⟨s', by simp [] [] [] ["[", expr this, "]"] [] []⟩) (assume
 b₁
 t
 hb₁t
 ih
 s'
 hs'
 hst
 hss', have hb₁s : «expr ∉ »(b₁, s), from assume
 h, have «expr ∈ »(b₁, «expr ∩ »(s, «expr↑ »(insert b₁ t))), from ⟨h, finset.mem_insert_self _ _⟩,
 by rwa ["[", expr hst, "]"] ["at", ident this],
 have hb₁s' : «expr ∉ »(b₁, s'), from assume h, «expr $ »(hb₁s, hs' h),
 have hst : «expr = »(«expr ∩ »(s, «expr↑ »(t)), «expr∅»()), from «expr $ »(eq_empty_of_subset_empty, subset.trans (by simp [] [] [] ["[", expr inter_subset_inter, ",", expr subset.refl, "]"] [] []) (le_of_eq hst)),
 classical.by_cases (assume: «expr ⊆ »(s, (span K «expr↑ »(«expr ∪ »(s', t)) : submodule K V)), let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
  have hb₁u : «expr ∉ »(b₁, u), from assume h, (hust h).elim hb₁s hb₁t,
  ⟨insert b₁ u, by simp [] [] [] ["[", expr insert_subset_insert hust, "]"] [] [], subset.trans hsu (by simp [] [] [] [] [] []), by simp [] [] [] ["[", expr eq, ",", expr hb₁t, ",", expr hb₁s', ",", expr hb₁u, "]"] [] []⟩) (assume: «expr¬ »(«expr ⊆ »(s, (span K «expr↑ »(«expr ∪ »(s', t)) : submodule K V))), let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this in
  have hb₂t' : «expr ∉ »(b₂, «expr ∪ »(s', t)), from assume h, «expr $ »(hb₂t, subset_span h),
  have «expr ⊆ »(s, (span K «expr↑ »(«expr ∪ »(insert b₂ s', t)) : submodule K V)), from assume
  b₃
  hb₃, have «expr ⊆ »(«expr↑ »(«expr ∪ »(s', insert b₁ t)), insert b₁ (insert b₂ «expr↑ »(«expr ∪ »(s', t)) : set V)), by simp [] [] [] ["[", expr insert_eq, ",", "-", ident singleton_union, ",", "-", ident union_singleton, ",", expr union_subset_union, ",", expr subset.refl, ",", expr subset_union_right, "]"] [] [],
  have hb₃ : «expr ∈ »(b₃, span K (insert b₁ (insert b₂ «expr↑ »(«expr ∪ »(s', t)) : set V))), from span_mono this (hss' hb₃),
  have «expr ⊆ »(s, (span K (insert b₁ «expr↑ »(«expr ∪ »(s', t))) : submodule K V)), by simpa [] [] [] ["[", expr insert_eq, ",", "-", ident singleton_union, ",", "-", ident union_singleton, "]"] [] ["using", expr hss'],
  have hb₁ : «expr ∈ »(b₁, span K (insert b₂ «expr↑ »(«expr ∪ »(s', t)))), from mem_span_insert_exchange (this hb₂s) hb₂t,
  by rw ["[", expr span_insert_eq_span hb₁, "]"] ["at", ident hb₃]; simpa [] [] [] [] [] ["using", expr hb₃],
  let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [] [] [] ["[", expr insert_subset, ",", expr hb₂s, ",", expr hs', "]"] [] []) hst this in
  ⟨u, «expr $ »(subset.trans hust, union_subset_union (subset.refl _) (by simp [] [] [] ["[", expr subset_insert, "]"] [] [])), hsu, by simp [] [] [] ["[", expr eq, ",", expr hb₂t', ",", expr hb₁t, ",", expr hb₁s', "]"] [] []⟩)),
begin
  have [ident eq] [":", expr «expr = »(«expr ∪ »(t.filter (λ
      x, «expr ∈ »(x, s)), t.filter (λ x, «expr ∉ »(x, s))), t)] [],
  { ext1 [] [ident x],
    by_cases [expr «expr ∈ »(x, s)]; simp [] [] [] ["*"] [] [] },
  apply [expr exists.elim (this (t.filter (λ
      x, «expr ∉ »(x, s))) (t.filter (λ
      x, «expr ∈ »(x, s))) (by simp [] [] [] ["[", expr set.subset_def, "]"] [] []) (by simp [] [] [] ["[", expr set.ext_iff, "]"] [] [] { contextual := tt }) (by rwa ["[", expr eq, "]"] []))],
  intros [ident u, ident h],
  exact [expr ⟨u, subset.trans h.1 (by simp [] [] [] ["[", expr subset_def, ",", expr and_imp, ",", expr or_imp_distrib, "]"] [] [] { contextual := tt }), h.2.1, by simp [] [] ["only"] ["[", expr h.2.2, ",", expr eq, "]"] [] []⟩]
end

theorem exists_finite_card_le_of_finite_of_linear_independent_of_span (ht : finite t)
  (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ span K t) :
  ∃ h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
  have  : s ⊆ (span K («expr↑ » ht.to_finset) : Submodule K V) :=
    by 
      simp  <;> assumption 
  let ⟨u, hust, hsu, Eq⟩ := exists_of_linear_independent_of_finite_span hs this 
  have  : finite s := u.finite_to_set.subset hsu
  ⟨this,
    by 
      rw [←Eq] <;>
        exact
          Finset.card_le_of_subset$
            finset.coe_subset.mp$
              by 
                simp [hsu]⟩

end Module

