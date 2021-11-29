import Mathbin.LinearAlgebra.Quotient 
import Mathbin.LinearAlgebra.Prod

/-!
# Projection to a subspace

In this file we define
* `linear_proj_of_is_compl (p q : submodule R E) (h : is_compl p q)`: the projection of a module `E`
  to a submodule `p` along its complement `q`; it is the unique linear map `f : E → p` such that
  `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.
* `is_compl_equiv_proj p`: equivalence between submodules `q` such that `is_compl p q` and
  projections `f : E → p`, `∀ x ∈ p, f x = x`.

We also provide some lemmas justifying correctness of our definitions.

## Tags

projection, complement subspace
-/


variable {R : Type _} [Ringₓ R] {E : Type _} [AddCommGroupₓ E] [Module R E] {F : Type _} [AddCommGroupₓ F] [Module R F]
  {G : Type _} [AddCommGroupₓ G] [Module R G] (p q : Submodule R E)

noncomputable theory

namespace LinearMap

variable {p}

open Submodule

theorem ker_id_sub_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : ker (id - p.subtype.comp f) = p :=
  by 
    ext x 
    simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero]
    exact
      ⟨fun h => h.symm ▸ Submodule.coe_mem _,
        fun hx =>
          by 
            erw [hf ⟨x, hx⟩, Subtype.coe_mk]⟩

theorem range_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : range f = ⊤ :=
  range_eq_top.2$ fun x => ⟨x, hf x⟩

theorem is_compl_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : IsCompl p f.ker :=
  by 
    split 
    ·
      rintro x ⟨hpx, hfx⟩
      erw [SetLike.mem_coe, mem_ker, hf ⟨x, hpx⟩, mk_eq_zero] at hfx 
      simp only [hfx, SetLike.mem_coe, zero_mem]
    ·
      intro x hx 
      rw [mem_sup']
      refine' ⟨f x, ⟨x - f x, _⟩, add_sub_cancel'_right _ _⟩
      rw [mem_ker, LinearMap.map_sub, hf, sub_self]

end LinearMap

namespace Submodule

open LinearMap

/-- If `q` is a complement of `p`, then `M/p ≃ q`. -/
def quotient_equiv_of_is_compl (h : IsCompl p q) : p.quotient ≃ₗ[R] q :=
  LinearEquiv.symm$
    LinearEquiv.ofBijective (p.mkq.comp q.subtype)
      (by 
        simp only [←ker_eq_bot, ker_comp, ker_mkq, disjoint_iff_comap_eq_bot.1 h.symm.disjoint])
      (by 
        simp only [←range_eq_top, range_comp, range_subtype, map_mkq_eq_top, h.sup_eq_top])

@[simp]
theorem quotient_equiv_of_is_compl_symm_apply (h : IsCompl p q) (x : q) :
  (quotient_equiv_of_is_compl p q h).symm x = Quotientₓ.mk x :=
  rfl

@[simp]
theorem quotient_equiv_of_is_compl_apply_mk_coe (h : IsCompl p q) (x : q) :
  quotient_equiv_of_is_compl p q h (Quotientₓ.mk x) = x :=
  (quotient_equiv_of_is_compl p q h).apply_symm_apply x

@[simp]
theorem mk_quotient_equiv_of_is_compl_apply (h : IsCompl p q) (x : p.quotient) :
  (Quotientₓ.mk (quotient_equiv_of_is_compl p q h x) : p.quotient) = x :=
  (quotient_equiv_of_is_compl p q h).symm_apply_apply x

/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`. -/
def prod_equiv_of_is_compl (h : IsCompl p q) : (p × q) ≃ₗ[R] E :=
  by 
    apply LinearEquiv.ofBijective (p.subtype.coprod q.subtype)
    ·
      simp only [←ker_eq_bot, ker_eq_bot', Prod.forall, subtype_apply, Prod.mk_eq_zero, coprod_apply]
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      simp only [coe_mk, mk_eq_zero, ←eq_neg_iff_add_eq_zero]
      rintro rfl 
      rw [neg_mem_iff] at hx 
      simp [disjoint_def.1 h.disjoint y hx hy]
    ·
      rw [←range_eq_top, ←sup_eq_range, h.sup_eq_top]

@[simp]
theorem coe_prod_equiv_of_is_compl (h : IsCompl p q) :
  (prod_equiv_of_is_compl p q h : p × q →ₗ[R] E) = p.subtype.coprod q.subtype :=
  rfl

@[simp]
theorem coe_prod_equiv_of_is_compl' (h : IsCompl p q) (x : p × q) : prod_equiv_of_is_compl p q h x = x.1+x.2 :=
  rfl

@[simp]
theorem prod_equiv_of_is_compl_symm_apply_left (h : IsCompl p q) (x : p) :
  (prod_equiv_of_is_compl p q h).symm x = (x, 0) :=
  (prod_equiv_of_is_compl p q h).symm_apply_eq.2$
    by 
      simp 

@[simp]
theorem prod_equiv_of_is_compl_symm_apply_right (h : IsCompl p q) (x : q) :
  (prod_equiv_of_is_compl p q h).symm x = (0, x) :=
  (prod_equiv_of_is_compl p q h).symm_apply_eq.2$
    by 
      simp 

@[simp]
theorem prod_equiv_of_is_compl_symm_apply_fst_eq_zero (h : IsCompl p q) {x : E} :
  ((prod_equiv_of_is_compl p q h).symm x).1 = 0 ↔ x ∈ q :=
  by 
    convRHS => rw [←(prod_equiv_of_is_compl p q h).apply_symm_apply x]
    rw [coe_prod_equiv_of_is_compl', Submodule.add_mem_iff_left _ (Submodule.coe_mem _),
      mem_right_iff_eq_zero_of_disjoint h.disjoint]

@[simp]
theorem prod_equiv_of_is_compl_symm_apply_snd_eq_zero (h : IsCompl p q) {x : E} :
  ((prod_equiv_of_is_compl p q h).symm x).2 = 0 ↔ x ∈ p :=
  by 
    convRHS => rw [←(prod_equiv_of_is_compl p q h).apply_symm_apply x]
    rw [coe_prod_equiv_of_is_compl', Submodule.add_mem_iff_right _ (Submodule.coe_mem _),
      mem_left_iff_eq_zero_of_disjoint h.disjoint]

/-- Projection to a submodule along its complement. -/
def linear_proj_of_is_compl (h : IsCompl p q) : E →ₗ[R] p :=
  LinearMap.fst R p q ∘ₗ «expr↑ » (prod_equiv_of_is_compl p q h).symm

variable {p q}

@[simp]
theorem linear_proj_of_is_compl_apply_left (h : IsCompl p q) (x : p) : linear_proj_of_is_compl p q h x = x :=
  by 
    simp [linear_proj_of_is_compl]

@[simp]
theorem linear_proj_of_is_compl_range (h : IsCompl p q) : (linear_proj_of_is_compl p q h).range = ⊤ :=
  range_eq_of_proj (linear_proj_of_is_compl_apply_left h)

@[simp]
theorem linear_proj_of_is_compl_apply_eq_zero_iff (h : IsCompl p q) {x : E} :
  linear_proj_of_is_compl p q h x = 0 ↔ x ∈ q :=
  by 
    simp [linear_proj_of_is_compl]

theorem linear_proj_of_is_compl_apply_right' (h : IsCompl p q) (x : E) (hx : x ∈ q) :
  linear_proj_of_is_compl p q h x = 0 :=
  (linear_proj_of_is_compl_apply_eq_zero_iff h).2 hx

@[simp]
theorem linear_proj_of_is_compl_apply_right (h : IsCompl p q) (x : q) : linear_proj_of_is_compl p q h x = 0 :=
  linear_proj_of_is_compl_apply_right' h x x.2

@[simp]
theorem linear_proj_of_is_compl_ker (h : IsCompl p q) : (linear_proj_of_is_compl p q h).ker = q :=
  ext$ fun x => mem_ker.trans (linear_proj_of_is_compl_apply_eq_zero_iff h)

theorem linear_proj_of_is_compl_comp_subtype (h : IsCompl p q) : (linear_proj_of_is_compl p q h).comp p.subtype = id :=
  LinearMap.ext$ linear_proj_of_is_compl_apply_left h

theorem linear_proj_of_is_compl_idempotent (h : IsCompl p q) (x : E) :
  linear_proj_of_is_compl p q h (linear_proj_of_is_compl p q h x) = linear_proj_of_is_compl p q h x :=
  linear_proj_of_is_compl_apply_left h _

theorem exists_unique_add_of_is_compl_prod (hc : IsCompl p q) (x : E) : ∃!u : p × q, ((u.fst : E)+u.snd) = x :=
  (prod_equiv_of_is_compl _ _ hc).toEquiv.Bijective.ExistsUnique _

theorem exists_unique_add_of_is_compl (hc : IsCompl p q) (x : E) :
  ∃ (u : p)(v : q), ((u : E)+v) = x ∧ ∀ r : p s : q, ((r : E)+s) = x → r = u ∧ s = v :=
  let ⟨u, hu₁, hu₂⟩ := exists_unique_add_of_is_compl_prod hc x
  ⟨u.1, u.2, hu₁, fun r s hrs => Prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩

end Submodule

namespace LinearMap

open Submodule

/-- Given linear maps `φ` and `ψ` from complement submodules, `of_is_compl` is
the induced linear map over the entire module. -/
def of_is_compl {p q : Submodule R E} (h : IsCompl p q) (φ : p →ₗ[R] F) (ψ : q →ₗ[R] F) : E →ₗ[R] F :=
  LinearMap.coprod φ ψ ∘ₗ «expr↑ » (Submodule.prodEquivOfIsCompl _ _ h).symm

variable {p q}

@[simp]
theorem of_is_compl_left_apply (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (u : p) :
  of_is_compl h φ ψ (u : E) = φ u :=
  by 
    simp [of_is_compl]

@[simp]
theorem of_is_compl_right_apply (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (v : q) :
  of_is_compl h φ ψ (v : E) = ψ v :=
  by 
    simp [of_is_compl]

theorem of_is_compl_eq (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F} (hφ : ∀ u, φ u = χ u)
  (hψ : ∀ u, ψ u = χ u) : of_is_compl h φ ψ = χ :=
  by 
    ext x 
    obtain ⟨_, _, rfl, _⟩ := exists_unique_add_of_is_compl h x 
    simp [of_is_compl, hφ, hψ]

theorem of_is_compl_eq' (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F} (hφ : φ = χ.comp p.subtype)
  (hψ : ψ = χ.comp q.subtype) : of_is_compl h φ ψ = χ :=
  of_is_compl_eq h (fun _ => hφ.symm ▸ rfl) fun _ => hψ.symm ▸ rfl

@[simp]
theorem of_is_compl_zero (h : IsCompl p q) : (of_is_compl h 0 0 : E →ₗ[R] F) = 0 :=
  of_is_compl_eq _ (fun _ => rfl) fun _ => rfl

@[simp]
theorem of_is_compl_add (h : IsCompl p q) {φ₁ φ₂ : p →ₗ[R] F} {ψ₁ ψ₂ : q →ₗ[R] F} :
  of_is_compl h (φ₁+φ₂) (ψ₁+ψ₂) = of_is_compl h φ₁ ψ₁+of_is_compl h φ₂ ψ₂ :=
  of_is_compl_eq _
    (by 
      simp )
    (by 
      simp )

@[simp]
theorem of_is_compl_smul {R : Type _} [CommRingₓ R] {E : Type _} [AddCommGroupₓ E] [Module R E] {F : Type _}
  [AddCommGroupₓ F] [Module R F] {p q : Submodule R E} (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (c : R) :
  of_is_compl h (c • φ) (c • ψ) = c • of_is_compl h φ ψ :=
  of_is_compl_eq _
    (by 
      simp )
    (by 
      simp )

section 

variable {R₁ : Type _} [CommRingₓ R₁] [Module R₁ E] [Module R₁ F]

/-- The linear map from `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` to `E →ₗ[R₁] F`. -/
def of_is_compl_prod {p q : Submodule R₁ E} (h : IsCompl p q) : (p →ₗ[R₁] F) × (q →ₗ[R₁] F) →ₗ[R₁] E →ₗ[R₁] F :=
  { toFun := fun φ => of_is_compl h φ.1 φ.2,
    map_add' :=
      by 
        intro φ ψ 
        rw [Prod.snd_add, Prod.fst_add, of_is_compl_add],
    map_smul' :=
      by 
        intro c φ 
        simp [Prod.smul_snd, Prod.smul_fst, of_is_compl_smul] }

@[simp]
theorem of_is_compl_prod_apply {p q : Submodule R₁ E} (h : IsCompl p q) (φ : (p →ₗ[R₁] F) × (q →ₗ[R₁] F)) :
  of_is_compl_prod h φ = of_is_compl h φ.1 φ.2 :=
  rfl

/-- The natural linear equivalence between `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` and `E →ₗ[R₁] F`. -/
def of_is_compl_prod_equiv {p q : Submodule R₁ E} (h : IsCompl p q) : ((p →ₗ[R₁] F) × (q →ₗ[R₁] F)) ≃ₗ[R₁] E →ₗ[R₁] F :=
  { of_is_compl_prod h with invFun := fun φ => ⟨φ.dom_restrict p, φ.dom_restrict q⟩,
    left_inv :=
      by 
        intro φ 
        ext
        ·
          exact of_is_compl_left_apply h x
        ·
          exact of_is_compl_right_apply h x,
    right_inv :=
      by 
        intro φ 
        ext 
        obtain ⟨a, b, hab, _⟩ := exists_unique_add_of_is_compl h x 
        rw [←hab]
        simp  }

end 

-- error in LinearAlgebra.Projection: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem linear_proj_of_is_compl_of_proj
(f : «expr →ₗ[ ] »(E, R, p))
(hf : ∀ x : p, «expr = »(f x, x)) : «expr = »(p.linear_proj_of_is_compl f.ker (is_compl_of_proj hf), f) :=
begin
  ext [] [ident x] [],
  have [] [":", expr «expr ∈ »(x, «expr ⊔ »(p, f.ker))] [],
  { simp [] [] ["only"] ["[", expr (is_compl_of_proj hf).sup_eq_top, ",", expr mem_top, "]"] [] [] },
  rcases [expr mem_sup'.1 this, "with", "⟨", ident x, ",", ident y, ",", ident rfl, "⟩"],
  simp [] [] [] ["[", expr hf, "]"] [] []
end

/-- If `f : E →ₗ[R] F` and `g : E →ₗ[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃ₗ[R] F × G`. -/
def equiv_prod_of_surjective_of_is_compl (f : E →ₗ[R] F) (g : E →ₗ[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
  (hfg : IsCompl f.ker g.ker) : E ≃ₗ[R] F × G :=
  LinearEquiv.ofBijective (f.prod g)
    (by 
      simp [←ker_eq_bot, hfg.inf_eq_bot])
    (by 
      simp [←range_eq_top, range_prod_eq hfg.sup_eq_top])

@[simp]
theorem coe_equiv_prod_of_surjective_of_is_compl {f : E →ₗ[R] F} {g : E →ₗ[R] G} (hf : f.range = ⊤) (hg : g.range = ⊤)
  (hfg : IsCompl f.ker g.ker) : (equiv_prod_of_surjective_of_is_compl f g hf hg hfg : E →ₗ[R] F × G) = f.prod g :=
  rfl

@[simp]
theorem equiv_prod_of_surjective_of_is_compl_apply {f : E →ₗ[R] F} {g : E →ₗ[R] G} (hf : f.range = ⊤) (hg : g.range = ⊤)
  (hfg : IsCompl f.ker g.ker) (x : E) : equiv_prod_of_surjective_of_is_compl f g hf hg hfg x = (f x, g x) :=
  rfl

end LinearMap

namespace Submodule

open LinearMap

/-- Equivalence between submodules `q` such that `is_compl p q` and linear maps `f : E →ₗ[R] p`
such that `∀ x : p, f x = x`. -/
def is_compl_equiv_proj : { q // IsCompl p q } ≃ { f : E →ₗ[R] p // ∀ x : p, f x = x } :=
  { toFun := fun q => ⟨linear_proj_of_is_compl p q q.2, linear_proj_of_is_compl_apply_left q.2⟩,
    invFun := fun f => ⟨(f : E →ₗ[R] p).ker, is_compl_of_proj f.2⟩,
    left_inv :=
      fun ⟨q, hq⟩ =>
        by 
          simp only [linear_proj_of_is_compl_ker, Subtype.coe_mk],
    right_inv := fun ⟨f, hf⟩ => Subtype.eq$ f.linear_proj_of_is_compl_of_proj hf }

@[simp]
theorem coe_is_compl_equiv_proj_apply (q : { q // IsCompl p q }) :
  (p.is_compl_equiv_proj q : E →ₗ[R] p) = linear_proj_of_is_compl p q q.2 :=
  rfl

@[simp]
theorem coe_is_compl_equiv_proj_symm_apply (f : { f : E →ₗ[R] p // ∀ x : p, f x = x }) :
  (p.is_compl_equiv_proj.symm f : Submodule R E) = (f : E →ₗ[R] p).ker :=
  rfl

end Submodule

