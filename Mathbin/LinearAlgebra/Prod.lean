import Mathbin.LinearAlgebra.Basic 
import Mathbin.Order.PartialSups

/-! ### Products of modules

This file defines constructors for linear maps whose domains or codomains are products.

It contains theorems relating these to each other, as well as to `submodule.prod`, `submodule.map`,
`submodule.comap`, `linear_map.range`, and `linear_map.ker`.

## Main definitions

- products in the domain:
  - `linear_map.fst`
  - `linear_map.snd`
  - `linear_map.coprod`
  - `linear_map.prod_ext`
- products in the codomain:
  - `linear_map.inl`
  - `linear_map.inr`
  - `linear_map.prod`
- products in both domain and codomain:
  - `linear_map.prod_map`
  - `linear_equiv.prod_map`
  - `linear_equiv.skew_prod`
-/


universe u v w x y z u' v' w' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}

variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}

section Prod

namespace LinearMap

variable (S : Type _) [Semiringₓ R] [Semiringₓ S]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄]

variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

variable (f : M →ₗ[R] M₂)

section 

variable (R M M₂)

/-- The first projection of a product is a linear map. -/
def fst : M × M₂ →ₗ[R] M :=
  { toFun := Prod.fst, map_add' := fun x y => rfl, map_smul' := fun x y => rfl }

/-- The second projection of a product is a linear map. -/
def snd : M × M₂ →ₗ[R] M₂ :=
  { toFun := Prod.snd, map_add' := fun x y => rfl, map_smul' := fun x y => rfl }

end 

@[simp]
theorem fst_apply (x : M × M₂) : fst R M M₂ x = x.1 :=
  rfl

@[simp]
theorem snd_apply (x : M × M₂) : snd R M M₂ x = x.2 :=
  rfl

theorem fst_surjective : Function.Surjective (fst R M M₂) :=
  fun x => ⟨(x, 0), rfl⟩

theorem snd_surjective : Function.Surjective (snd R M M₂) :=
  fun x => ⟨(0, x), rfl⟩

/-- The prod of two linear maps is a linear map. -/
@[simps]
def Prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : M →ₗ[R] M₂ × M₃ :=
  { toFun := fun x => (f x, g x),
    map_add' :=
      fun x y =>
        by 
          simp only [Prod.mk_add_mk, map_add],
    map_smul' :=
      fun c x =>
        by 
          simp only [Prod.smul_mk, map_smul, RingHom.id_apply] }

@[simp]
theorem fst_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : (fst R M₂ M₃).comp (Prod f g) = f :=
  by 
    ext <;> rfl

@[simp]
theorem snd_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : (snd R M₂ M₃).comp (Prod f g) = g :=
  by 
    ext <;> rfl

@[simp]
theorem pair_fst_snd : Prod (fst R M M₂) (snd R M M₂) = LinearMap.id :=
  by 
    ext <;> rfl

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def prod_equiv [Module S M₂] [Module S M₃] [SmulCommClass R S M₂] [SmulCommClass R S M₃] :
  ((M →ₗ[R] M₂) × (M →ₗ[R] M₃)) ≃ₗ[S] M →ₗ[R] M₂ × M₃ :=
  { toFun := fun f => f.1.Prod f.2, invFun := fun f => ((fst _ _ _).comp f, (snd _ _ _).comp f),
    left_inv :=
      fun f =>
        by 
          ext <;> rfl,
    right_inv :=
      fun f =>
        by 
          ext <;> rfl,
    map_add' := fun a b => rfl, map_smul' := fun r a => rfl }

section 

variable (R M M₂)

/-- The left injection into a product is a linear map. -/
def inl : M →ₗ[R] M × M₂ :=
  Prod LinearMap.id 0

/-- The right injection into a product is a linear map. -/
def inr : M₂ →ₗ[R] M × M₂ :=
  Prod 0 LinearMap.id

theorem range_inl : range (inl R M M₂) = ker (snd R M M₂) :=
  by 
    ext x 
    simp only [mem_ker, mem_range]
    split 
    ·
      rintro ⟨y, rfl⟩
      rfl
    ·
      intro h 
      exact ⟨x.fst, Prod.extₓ rfl h.symm⟩

theorem ker_snd : ker (snd R M M₂) = range (inl R M M₂) :=
  Eq.symm$ range_inl R M M₂

theorem range_inr : range (inr R M M₂) = ker (fst R M M₂) :=
  by 
    ext x 
    simp only [mem_ker, mem_range]
    split 
    ·
      rintro ⟨y, rfl⟩
      rfl
    ·
      intro h 
      exact ⟨x.snd, Prod.extₓ h.symm rfl⟩

theorem ker_fst : ker (fst R M M₂) = range (inr R M M₂) :=
  Eq.symm$ range_inr R M M₂

end 

@[simp]
theorem coe_inl : (inl R M M₂ : M → M × M₂) = fun x => (x, 0) :=
  rfl

theorem inl_apply (x : M) : inl R M M₂ x = (x, 0) :=
  rfl

@[simp]
theorem coe_inr : (inr R M M₂ : M₂ → M × M₂) = Prod.mk 0 :=
  rfl

theorem inr_apply (x : M₂) : inr R M M₂ x = (0, x) :=
  rfl

theorem inl_eq_prod : inl R M M₂ = Prod LinearMap.id 0 :=
  rfl

theorem inr_eq_prod : inr R M M₂ = Prod 0 LinearMap.id :=
  rfl

theorem inl_injective : Function.Injective (inl R M M₂) :=
  fun _ =>
    by 
      simp 

theorem inr_injective : Function.Injective (inr R M M₂) :=
  fun _ =>
    by 
      simp 

/-- The coprod function `λ x : M × M₂, f x.1 + g x.2` is a linear map. -/
def coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : M × M₂ →ₗ[R] M₃ :=
  f.comp (fst _ _ _)+g.comp (snd _ _ _)

@[simp]
theorem coprod_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (x : M × M₂) : coprod f g x = f x.1+g x.2 :=
  rfl

@[simp]
theorem coprod_inl (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (coprod f g).comp (inl R M M₂) = f :=
  by 
    ext <;> simp only [map_zero, add_zeroₓ, coprod_apply, inl_apply, comp_apply]

@[simp]
theorem coprod_inr (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (coprod f g).comp (inr R M M₂) = g :=
  by 
    ext <;> simp only [map_zero, coprod_apply, inr_apply, zero_addₓ, comp_apply]

@[simp]
theorem coprod_inl_inr : coprod (inl R M M₂) (inr R M M₂) = LinearMap.id :=
  by 
    ext <;> simp only [Prod.mk_add_mk, add_zeroₓ, id_apply, coprod_apply, inl_apply, inr_apply, zero_addₓ]

theorem comp_coprod (f : M₃ →ₗ[R] M₄) (g₁ : M →ₗ[R] M₃) (g₂ : M₂ →ₗ[R] M₃) :
  f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
  ext$ fun x => f.map_add (g₁ x.1) (g₂ x.2)

theorem fst_eq_coprod : fst R M M₂ = coprod LinearMap.id 0 :=
  by 
    ext <;> simp 

theorem snd_eq_coprod : snd R M M₂ = coprod 0 LinearMap.id :=
  by 
    ext <;> simp 

@[simp]
theorem coprod_comp_prod (f : M₂ →ₗ[R] M₄) (g : M₃ →ₗ[R] M₄) (f' : M →ₗ[R] M₂) (g' : M →ₗ[R] M₃) :
  (f.coprod g).comp (f'.prod g') = f.comp f'+g.comp g' :=
  rfl

@[simp]
theorem coprod_map_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (S : Submodule R M) (S' : Submodule R M₂) :
  (Submodule.prod S S').map (LinearMap.coprod f g) = S.map f⊔S'.map g :=
  SetLike.coe_injective$
    by 
      simp only [LinearMap.coprod_apply, Submodule.coe_sup, Submodule.map_coe]
      rw [←Set.image2_add, Set.image2_image_left, Set.image2_image_right]
      exact Set.image_prod fun m m₂ => f m+g m₂

/-- Taking the product of two maps with the same codomain is equivalent to taking the product of
their domains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def coprod_equiv [Module S M₃] [SmulCommClass R S M₃] : ((M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃)) ≃ₗ[S] M × M₂ →ₗ[R] M₃ :=
  { toFun := fun f => f.1.coprod f.2, invFun := fun f => (f.comp (inl _ _ _), f.comp (inr _ _ _)),
    left_inv :=
      fun f =>
        by 
          simp only [Prod.mk.eta, coprod_inl, coprod_inr],
    right_inv :=
      fun f =>
        by 
          simp only [←comp_coprod, comp_id, coprod_inl_inr],
    map_add' :=
      fun a b =>
        by 
          ext 
          simp only [Prod.snd_add, add_apply, coprod_apply, Prod.fst_add]
          acRfl,
    map_smul' :=
      fun r a =>
        by 
          dsimp 
          ext 
          simp only [smul_add, smul_apply, Prod.smul_snd, Prod.smul_fst, coprod_apply] }

theorem prod_ext_iff {f g : M × M₂ →ₗ[R] M₃} :
  f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
  (coprod_equiv ℕ).symm.Injective.eq_iff.symm.trans Prod.ext_iff

/--
Split equality of linear maps from a product into linear maps over each component, to allow `ext`
to apply lemmas specific to `M →ₗ M₃` and `M₂ →ₗ M₃`.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem prod_ext {f g : M × M₂ →ₗ[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

/-- `prod.map` of two linear maps. -/
def prod_mapₓ (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) : M × M₂ →ₗ[R] M₃ × M₄ :=
  (f.comp (fst R M M₂)).Prod (g.comp (snd R M M₂))

@[simp]
theorem prod_map_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) x : f.prod_map g x = (f x.1, g x.2) :=
  rfl

theorem prod_map_comap_prod (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) (S : Submodule R M₂) (S' : Submodule R M₄) :
  (Submodule.prod S S').comap (LinearMap.prodMap f g) = (S.comap f).Prod (S'.comap g) :=
  SetLike.coe_injective$ Set.preimage_prod_map_prod f g _ _

theorem ker_prod_map (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) : (LinearMap.prodMap f g).ker = Submodule.prod f.ker g.ker :=
  by 
    dsimp only [ker]
    rw [←prod_map_comap_prod, Submodule.prod_bot]

section MapMul

variable {A : Type _} [NonUnitalNonAssocSemiring A] [Module R A]

variable {B : Type _} [NonUnitalNonAssocSemiring B] [Module R B]

theorem inl_map_mul (a₁ a₂ : A) : LinearMap.inl R A B (a₁*a₂) = LinearMap.inl R A B a₁*LinearMap.inl R A B a₂ :=
  Prod.extₓ rfl
    (by 
      simp )

theorem inr_map_mul (b₁ b₂ : B) : LinearMap.inr R A B (b₁*b₂) = LinearMap.inr R A B b₁*LinearMap.inr R A B b₂ :=
  Prod.extₓ
    (by 
      simp )
    rfl

end MapMul

end LinearMap

end Prod

namespace LinearMap

open Submodule

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄] [Module R M]
  [Module R M₂] [Module R M₃] [Module R M₄]

theorem range_coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (f.coprod g).range = f.range⊔g.range :=
  Submodule.ext$
    fun x =>
      by 
        simp [mem_sup]

theorem is_compl_range_inl_inr : IsCompl (inl R M M₂).range (inr R M M₂).range :=
  by 
    split 
    ·
      rintro ⟨_, _⟩ ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      simp only [Prod.ext_iff, inl_apply, inr_apply, mem_bot] at hx hy⊢
      exact ⟨hy.1.symm, hx.2.symm⟩
    ·
      rintro ⟨x, y⟩ -
      simp only [mem_sup, mem_range, exists_prop]
      refine' ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, _⟩
      simp 

theorem sup_range_inl_inr : (inl R M M₂).range⊔(inr R M M₂).range = ⊤ :=
  is_compl_range_inl_inr.sup_eq_top

-- error in LinearAlgebra.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem disjoint_inl_inr : disjoint (inl R M M₂).range (inr R M M₂).range :=
by simp [] [] [] ["[", expr disjoint_def, ",", expr @eq_comm M 0, ",", expr @eq_comm M₂ 0, "]"] [] [] { contextual := tt }; intros []; refl

theorem map_coprod_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (p : Submodule R M) (q : Submodule R M₂) :
  map (coprod f g) (p.prod q) = map f p⊔map g q :=
  by 
    refine' le_antisymmₓ _ (sup_le (map_le_iff_le_comap.2 _) (map_le_iff_le_comap.2 _))
    ·
      rw [SetLike.le_def]
      rintro _ ⟨x, ⟨h₁, h₂⟩, rfl⟩
      exact mem_sup.2 ⟨_, ⟨_, h₁, rfl⟩, _, ⟨_, h₂, rfl⟩, rfl⟩
    ·
      exact
        fun x hx =>
          ⟨(x, 0),
            by 
              simp [hx]⟩
    ·
      exact
        fun x hx =>
          ⟨(0, x),
            by 
              simp [hx]⟩

theorem comap_prod_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) (p : Submodule R M₂) (q : Submodule R M₃) :
  comap (Prod f g) (p.prod q) = comap f p⊓comap g q :=
  Submodule.ext$ fun x => Iff.rfl

theorem prod_eq_inf_comap (p : Submodule R M) (q : Submodule R M₂) :
  p.prod q = p.comap (LinearMap.fst R M M₂)⊓q.comap (LinearMap.snd R M M₂) :=
  Submodule.ext$ fun x => Iff.rfl

theorem prod_eq_sup_map (p : Submodule R M) (q : Submodule R M₂) :
  p.prod q = p.map (LinearMap.inl R M M₂)⊔q.map (LinearMap.inr R M M₂) :=
  by 
    rw [←map_coprod_prod, coprod_inl_inr, map_id]

theorem span_inl_union_inr {s : Set M} {t : Set M₂} :
  span R (inl R M M₂ '' s ∪ inr R M M₂ '' t) = (span R s).Prod (span R t) :=
  by 
    rw [span_union, prod_eq_sup_map, ←span_image, ←span_image]

@[simp]
theorem ker_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : ker (Prod f g) = ker f⊓ker g :=
  by 
    rw [ker, ←prod_bot, comap_prod_prod] <;> rfl

theorem range_prod_le (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : range (Prod f g) ≤ (range f).Prod (range g) :=
  by 
    simp only [SetLike.le_def, prod_apply, mem_range, SetLike.mem_coe, mem_prod, exists_imp_distrib]
    rintro _ x rfl 
    exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩

-- error in LinearAlgebra.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ker_prod_ker_le_ker_coprod
{M₂ : Type*}
[add_comm_group M₂]
[module R M₂]
{M₃ : Type*}
[add_comm_group M₃]
[module R M₃]
(f : «expr →ₗ[ ] »(M, R, M₃))
(g : «expr →ₗ[ ] »(M₂, R, M₃)) : «expr ≤ »((ker f).prod (ker g), ker (f.coprod g)) :=
by { rintros ["⟨", ident y, ",", ident z, "⟩"],
  simp [] [] [] [] [] [] { contextual := tt } }

-- error in LinearAlgebra.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ker_coprod_of_disjoint_range
{M₂ : Type*}
[add_comm_group M₂]
[module R M₂]
{M₃ : Type*}
[add_comm_group M₃]
[module R M₃]
(f : «expr →ₗ[ ] »(M, R, M₃))
(g : «expr →ₗ[ ] »(M₂, R, M₃))
(hd : disjoint f.range g.range) : «expr = »(ker (f.coprod g), (ker f).prod (ker g)) :=
begin
  apply [expr le_antisymm _ (ker_prod_ker_le_ker_coprod f g)],
  rintros ["⟨", ident y, ",", ident z, "⟩", ident h],
  simp [] [] ["only"] ["[", expr mem_ker, ",", expr mem_prod, ",", expr coprod_apply, "]"] [] ["at", ident h, "⊢"],
  have [] [":", expr «expr ∈ »(f y, «expr ⊓ »(f.range, g.range))] [],
  { simp [] [] ["only"] ["[", expr true_and, ",", expr mem_range, ",", expr mem_inf, ",", expr exists_apply_eq_apply, "]"] [] [],
    use [expr «expr- »(z)],
    rwa ["[", expr eq_comm, ",", expr map_neg, ",", "<-", expr sub_eq_zero, ",", expr sub_neg_eq_add, "]"] [] },
  rw ["[", expr hd.eq_bot, ",", expr mem_bot, "]"] ["at", ident this],
  rw ["[", expr this, "]"] ["at", ident h],
  simpa [] [] [] ["[", expr this, "]"] [] ["using", expr h]
end

end LinearMap

namespace Submodule

open LinearMap

variable [Semiringₓ R]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]

variable [Module R M] [Module R M₂]

theorem sup_eq_range (p q : Submodule R M) : p⊔q = (p.subtype.coprod q.subtype).range :=
  Submodule.ext$
    fun x =>
      by 
        simp [Submodule.mem_sup, SetLike.exists]

variable (p : Submodule R M) (q : Submodule R M₂)

@[simp]
theorem map_inl : p.map (inl R M M₂) = Prod p ⊥ :=
  by 
    ext ⟨x, y⟩
    simp only [And.left_comm, eq_comm, mem_map, Prod.mk.inj_iffₓ, inl_apply, mem_bot, exists_eq_left', mem_prod]

@[simp]
theorem map_inr : q.map (inr R M M₂) = Prod ⊥ q :=
  by 
    ext ⟨x, y⟩ <;> simp [And.left_comm, eq_comm]

@[simp]
theorem comap_fst : p.comap (fst R M M₂) = Prod p ⊤ :=
  by 
    ext ⟨x, y⟩ <;> simp 

@[simp]
theorem comap_snd : q.comap (snd R M M₂) = Prod ⊤ q :=
  by 
    ext ⟨x, y⟩ <;> simp 

@[simp]
theorem prod_comap_inl : (Prod p q).comap (inl R M M₂) = p :=
  by 
    ext <;> simp 

@[simp]
theorem prod_comap_inr : (Prod p q).comap (inr R M M₂) = q :=
  by 
    ext <;> simp 

@[simp]
theorem prod_map_fst : (Prod p q).map (fst R M M₂) = p :=
  by 
    ext x <;> simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ q)]

@[simp]
theorem prod_map_snd : (Prod p q).map (snd R M M₂) = q :=
  by 
    ext x <;> simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ p)]

@[simp]
theorem ker_inl : (inl R M M₂).ker = ⊥ :=
  by 
    rw [ker, ←prod_bot, prod_comap_inl]

@[simp]
theorem ker_inr : (inr R M M₂).ker = ⊥ :=
  by 
    rw [ker, ←prod_bot, prod_comap_inr]

@[simp]
theorem range_fst : (fst R M M₂).range = ⊤ :=
  by 
    rw [range_eq_map, ←prod_top, prod_map_fst]

@[simp]
theorem range_snd : (snd R M M₂).range = ⊤ :=
  by 
    rw [range_eq_map, ←prod_top, prod_map_snd]

variable (R M M₂)

/-- `M` as a submodule of `M × N`. -/
def fst : Submodule R (M × M₂) :=
  (⊥ : Submodule R M₂).comap (LinearMap.snd R M M₂)

/-- `M` as a submodule of `M × N` is isomorphic to `M`. -/
@[simps]
def fst_equiv : Submodule.fst R M M₂ ≃ₗ[R] M :=
  { toFun := fun x => x.1.1,
    invFun :=
      fun m =>
        ⟨⟨m, 0⟩,
          by 
            tidy⟩,
    map_add' :=
      by 
        simp ,
    map_smul' :=
      by 
        simp ,
    left_inv :=
      by 
        tidy,
    right_inv :=
      by 
        tidy }

theorem fst_map_fst : (Submodule.fst R M M₂).map (LinearMap.fst R M M₂) = ⊤ :=
  by 
    tidy

theorem fst_map_snd : (Submodule.fst R M M₂).map (LinearMap.snd R M M₂) = ⊥ :=
  by 
    tidy 
    exact 0

/-- `N` as a submodule of `M × N`. -/
def snd : Submodule R (M × M₂) :=
  (⊥ : Submodule R M).comap (LinearMap.fst R M M₂)

/-- `N` as a submodule of `M × N` is isomorphic to `N`. -/
@[simps]
def snd_equiv : Submodule.snd R M M₂ ≃ₗ[R] M₂ :=
  { toFun := fun x => x.1.2,
    invFun :=
      fun n =>
        ⟨⟨0, n⟩,
          by 
            tidy⟩,
    map_add' :=
      by 
        simp ,
    map_smul' :=
      by 
        simp ,
    left_inv :=
      by 
        tidy,
    right_inv :=
      by 
        tidy }

theorem snd_map_fst : (Submodule.snd R M M₂).map (LinearMap.fst R M M₂) = ⊥ :=
  by 
    tidy 
    exact 0

theorem snd_map_snd : (Submodule.snd R M M₂).map (LinearMap.snd R M M₂) = ⊤ :=
  by 
    tidy

theorem fst_sup_snd : Submodule.fst R M M₂⊔Submodule.snd R M M₂ = ⊤ :=
  by 
    rw [eq_top_iff]
    rintro ⟨m, n⟩ -
    rw
      [show (m, n) = (m, 0)+(0, n)by 
        simp ]
    apply Submodule.add_mem (Submodule.fst R M M₂⊔Submodule.snd R M M₂)
    ·
      exact
        Submodule.mem_sup_left
          (submodule.mem_comap.mpr
            (by 
              simp ))
    ·
      exact
        Submodule.mem_sup_right
          (submodule.mem_comap.mpr
            (by 
              simp ))

theorem fst_inf_snd : Submodule.fst R M M₂⊓Submodule.snd R M M₂ = ⊥ :=
  by 
    tidy

end Submodule

namespace LinearEquiv

section 

variable [Semiringₓ R]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄]

variable {module_M : Module R M} {module_M₂ : Module R M₂}

variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}

variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Product of linear equivalences; the maps come from `equiv.prod_congr`. -/
protected def Prod : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { Equiv.prodCongr e₁.to_equiv e₂.to_equiv with map_add' := fun x y => Prod.extₓ (e₁.map_add _ _) (e₂.map_add _ _),
    map_smul' := fun c x => Prod.extₓ (e₁.map_smulₛₗ c _) (e₂.map_smulₛₗ c _) }

theorem prod_symm : (e₁.prod e₂).symm = e₁.symm.prod e₂.symm :=
  rfl

@[simp]
theorem prod_apply p : e₁.prod e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[simp, normCast]
theorem coe_prod : (e₁.prod e₂ : M × M₃ →ₗ[R] M₂ × M₄) = (e₁ : M →ₗ[R] M₂).prod_map (e₂ : M₃ →ₗ[R] M₄) :=
  rfl

end 

section 

variable [Semiringₓ R]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommGroupₓ M₄]

variable {module_M : Module R M} {module_M₂ : Module R M₂}

variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}

variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Equivalence given by a block lower diagonal matrix. `e₁` and `e₂` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
protected def skew_prod (f : M →ₗ[R] M₄) : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { ((e₁ : M →ₗ[R] M₂).comp (LinearMap.fst R M M₃)).Prod
      ((e₂ : M₃ →ₗ[R] M₄).comp (LinearMap.snd R M M₃)+f.comp (LinearMap.fst R M M₃)) with
    invFun := fun p : M₂ × M₄ => (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1))),
    left_inv :=
      fun p =>
        by 
          simp ,
    right_inv :=
      fun p =>
        by 
          simp  }

@[simp]
theorem skew_prod_apply (f : M →ₗ[R] M₄) x : e₁.skew_prod e₂ f x = (e₁ x.1, e₂ x.2+f x.1) :=
  rfl

@[simp]
theorem skew_prod_symm_apply (f : M →ₗ[R] M₄) x :
  (e₁.skew_prod e₂ f).symm x = (e₁.symm x.1, e₂.symm (x.2 - f (e₁.symm x.1))) :=
  rfl

end 

end LinearEquiv

namespace LinearMap

open Submodule

variable [Ringₓ R]

variable [AddCommGroupₓ M] [AddCommGroupₓ M₂] [AddCommGroupₓ M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

-- error in LinearAlgebra.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the union of the kernels `ker f` and `ker g` spans the domain, then the range of
`prod f g` is equal to the product of `range f` and `range g`. -/
theorem range_prod_eq
{f : «expr →ₗ[ ] »(M, R, M₂)}
{g : «expr →ₗ[ ] »(M, R, M₃)}
(h : «expr = »(«expr ⊔ »(ker f, ker g), «expr⊤»())) : «expr = »(range (prod f g), (range f).prod (range g)) :=
begin
  refine [expr le_antisymm (f.range_prod_le g) _],
  simp [] [] ["only"] ["[", expr set_like.le_def, ",", expr prod_apply, ",", expr mem_range, ",", expr set_like.mem_coe, ",", expr mem_prod, ",", expr exists_imp_distrib, ",", expr and_imp, ",", expr prod.forall, "]"] [] [],
  rintros ["_", "_", ident x, ident rfl, ident y, ident rfl],
  simp [] [] ["only"] ["[", expr prod.mk.inj_iff, ",", "<-", expr sub_mem_ker_iff, "]"] [] [],
  have [] [":", expr «expr ∈ »(«expr - »(y, x), «expr ⊔ »(ker f, ker g))] [],
  { simp [] [] ["only"] ["[", expr h, ",", expr mem_top, "]"] [] [] },
  rcases [expr mem_sup.1 this, "with", "⟨", ident x', ",", ident hx', ",", ident y', ",", ident hy', ",", ident H, "⟩"],
  refine [expr ⟨«expr + »(x', x), _, _⟩],
  { rwa [expr add_sub_cancel] [] },
  { rwa ["[", "<-", expr eq_sub_iff_add_eq.1 H, ",", expr add_sub_add_right_eq_sub, ",", "<-", expr neg_mem_iff, ",", expr neg_sub, ",", expr add_sub_cancel', "]"] [] }
end

end LinearMap

namespace LinearMap

/-!
## Tunnels and tailings

Some preliminary work for establishing the strong rank condition for noetherian rings.

Given a morphism `f : M × N →ₗ[R] M` which is `i : injective f`,
we can find an infinite decreasing `tunnel f i n` of copies of `M` inside `M`,
and sitting beside these, an infinite sequence of copies of `N`.

We picturesquely name these as `tailing f i n` for each individual copy of `N`,
and `tailings f i n` for the supremum of the first `n+1` copies:
they are the pieces left behind, sitting inside the tunnel.

By construction, each `tailing f i (n+1)` is disjoint from `tailings f i n`;
later, when we assume `M` is noetherian, this implies that `N` must be trivial,
and establishes the strong rank condition for any left-noetherian ring.
-/


section Tunnel

variable [Ringₓ R]

variable {N : Type _} [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ N] [Module R N]

open Function

/-- An auxiliary construction for `tunnel`.
The composition of `f`, followed by the isomorphism back to `K`,
followed by the inclusion of this submodule back into `M`. -/
def tunnel_aux (f : M × N →ₗ[R] M) (Kφ : ΣK : Submodule R M, K ≃ₗ[R] M) : M × N →ₗ[R] M :=
  (Kφ.1.Subtype.comp Kφ.2.symm.toLinearMap).comp f

theorem tunnel_aux_injective (f : M × N →ₗ[R] M) (i : injective f) (Kφ : ΣK : Submodule R M, K ≃ₗ[R] M) :
  injective (tunnel_aux f Kφ) :=
  (Subtype.val_injective.comp Kφ.2.symm.Injective).comp i

noncomputable theory

/-- Auxiliary definition for `tunnel`. -/
noncomputable def tunnel' (f : M × N →ₗ[R] M) (i : injective f) : ℕ → ΣK : Submodule R M, K ≃ₗ[R] M
| 0 => ⟨⊤, LinearEquiv.ofTop ⊤ rfl⟩
| n+1 =>
  ⟨(Submodule.fst R M N).map (tunnel_aux f (tunnel' n)),
    ((Submodule.fst R M N).equivMapOfInjective _ (tunnel_aux_injective f i (tunnel' n))).symm.trans
      (Submodule.fstEquiv R M N)⟩

/--
Give an injective map `f : M × N →ₗ[R] M` we can find a nested sequence of submodules
all isomorphic to `M`.
-/
def tunnel (f : M × N →ₗ[R] M) (i : injective f) : ℕ →ₘ OrderDual (Submodule R M) :=
  ⟨fun n => (tunnel' f i n).1,
    monotone_nat_of_le_succ
      fun n =>
        by 
          dsimp [tunnel', tunnel_aux]
          rw [Submodule.map_comp, Submodule.map_comp]
          apply Submodule.map_subtype_le⟩

/--
Give an injective map `f : M × N →ₗ[R] M` we can find a sequence of submodules
all isomorphic to `N`.
-/
def tailing (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) : Submodule R M :=
  (Submodule.snd R M N).map (tunnel_aux f (tunnel' f i n))

/-- Each `tailing f i n` is a copy of `N`. -/
def tailing_linear_equiv (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) : tailing f i n ≃ₗ[R] N :=
  ((Submodule.snd R M N).equivMapOfInjective _ (tunnel_aux_injective f i (tunnel' f i n))).symm.trans
    (Submodule.sndEquiv R M N)

theorem tailing_le_tunnel (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) : tailing f i n ≤ tunnel f i n :=
  by 
    dsimp [tailing, tunnel_aux]
    rw [Submodule.map_comp, Submodule.map_comp]
    apply Submodule.map_subtype_le

theorem tailing_disjoint_tunnel_succ (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  Disjoint (tailing f i n) (tunnel f i (n+1)) :=
  by 
    rw [disjoint_iff]
    dsimp [tailing, tunnel, tunnel']
    rw [Submodule.map_inf_eq_map_inf_comap, Submodule.comap_map_eq_of_injective (tunnel_aux_injective _ i _), inf_comm,
      Submodule.fst_inf_snd, Submodule.map_bot]

theorem tailing_sup_tunnel_succ_le_tunnel (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  tailing f i n⊔tunnel f i (n+1) ≤ tunnel f i n :=
  by 
    dsimp [tailing, tunnel, tunnel', tunnel_aux]
    rw [←Submodule.map_sup, sup_comm, Submodule.fst_sup_snd, Submodule.map_comp, Submodule.map_comp]
    apply Submodule.map_subtype_le

/-- The supremum of all the copies of `N` found inside the tunnel. -/
def tailings (f : M × N →ₗ[R] M) (i : injective f) : ℕ → Submodule R M :=
  partialSups (tailing f i)

@[simp]
theorem tailings_zero (f : M × N →ₗ[R] M) (i : injective f) : tailings f i 0 = tailing f i 0 :=
  by 
    simp [tailings]

@[simp]
theorem tailings_succ (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  tailings f i (n+1) = tailings f i n⊔tailing f i (n+1) :=
  by 
    simp [tailings]

theorem tailings_disjoint_tunnel (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  Disjoint (tailings f i n) (tunnel f i (n+1)) :=
  by 
    induction' n with n ih
    ·
      simp only [tailings_zero]
      apply tailing_disjoint_tunnel_succ
    ·
      simp only [tailings_succ]
      refine' Disjoint.disjoint_sup_left_of_disjoint_sup_right _ _ 
      apply tailing_disjoint_tunnel_succ 
      apply Disjoint.mono_right _ ih 
      apply tailing_sup_tunnel_succ_le_tunnel

theorem tailings_disjoint_tailing (f : M × N →ₗ[R] M) (i : injective f) (n : ℕ) :
  Disjoint (tailings f i n) (tailing f i (n+1)) :=
  Disjoint.mono_right (tailing_le_tunnel f i _) (tailings_disjoint_tunnel f i _)

end Tunnel

end LinearMap

