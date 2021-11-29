import Mathbin.Algebra.Lie.Basic 
import Mathbin.RingTheory.Noetherian

/-!
# Lie subalgebras

This file defines Lie subalgebras of a Lie algebra and provides basic related definitions and
results.

## Main definitions

  * `lie_subalgebra`
  * `lie_subalgebra.incl`
  * `lie_subalgebra.map`
  * `lie_hom.range`
  * `lie_equiv.of_injective`
  * `lie_equiv.of_eq`
  * `lie_equiv.of_subalgebra`
  * `lie_equiv.of_subalgebras`

## Tags

lie algebra, lie subalgebra
-/


universe u v w w₁ w₂

section LieSubalgebra

variable (R : Type u) (L : Type v) [CommRingₓ R] [LieRing L] [LieAlgebra R L]

/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
structure LieSubalgebra extends Submodule R L where 
  lie_mem' : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x,y⁆ ∈ carrier

attribute [nolint doc_blame] LieSubalgebra.toSubmodule

/-- The zero algebra is a subalgebra of any Lie algebra. -/
instance : HasZero (LieSubalgebra R L) :=
  ⟨{ (0 : Submodule R L) with
      lie_mem' :=
        fun x y hx hy =>
          by 
            rw [(Submodule.mem_bot R).1 hx, zero_lie]
            exact Submodule.zero_mem (0 : Submodule R L) }⟩

instance : Inhabited (LieSubalgebra R L) :=
  ⟨0⟩

instance : Coe (LieSubalgebra R L) (Submodule R L) :=
  ⟨LieSubalgebra.toSubmodule⟩

instance : HasMem L (LieSubalgebra R L) :=
  ⟨fun x L' => x ∈ (L' : Set L)⟩

/-- A Lie subalgebra forms a new Lie ring. -/
instance lieSubalgebraLieRing (L' : LieSubalgebra R L) : LieRing L' :=
  { bracket := fun x y => ⟨⁅x.val,y.val⁆, L'.lie_mem' x.property y.property⟩,
    lie_add :=
      by 
        intros 
        apply SetCoe.ext 
        apply lie_add,
    add_lie :=
      by 
        intros 
        apply SetCoe.ext 
        apply add_lie,
    lie_self :=
      by 
        intros 
        apply SetCoe.ext 
        apply lie_self,
    leibniz_lie :=
      by 
        intros 
        apply SetCoe.ext 
        apply leibniz_lie }

/-- A Lie subalgebra forms a new Lie algebra. -/
instance lieSubalgebraLieAlgebra (L' : LieSubalgebra R L) : LieAlgebra R L' :=
  { lie_smul :=
      by 
        intros 
        apply SetCoe.ext 
        apply lie_smul }

namespace LieSubalgebra

variable {R L} (L' : LieSubalgebra R L)

@[simp]
theorem zero_mem : (0 : L) ∈ L' :=
  (L' : Submodule R L).zero_mem

theorem smul_mem (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' :=
  (L' : Submodule R L).smul_mem t h

theorem add_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (x+y : L) ∈ L' :=
  (L' : Submodule R L).add_mem hx hy

theorem sub_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (x - y : L) ∈ L' :=
  (L' : Submodule R L).sub_mem hx hy

theorem lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x,y⁆ : L) ∈ L' :=
  L'.lie_mem' hx hy

@[simp]
theorem mem_carrier {x : L} : x ∈ L'.carrier ↔ x ∈ (L' : Set L) :=
  Iff.rfl

@[simp]
theorem mem_mk_iff (S : Set L) h₁ h₂ h₃ h₄ {x : L} : x ∈ (⟨⟨S, h₁, h₂, h₃⟩, h₄⟩ : LieSubalgebra R L) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_coe_submodule {x : L} : x ∈ (L' : Submodule R L) ↔ x ∈ L' :=
  Iff.rfl

theorem mem_coe {x : L} : x ∈ (L' : Set L) ↔ x ∈ L' :=
  Iff.rfl

@[simp, normCast]
theorem coe_bracket (x y : L') : («expr↑ » ⁅x,y⁆ : L) = ⁅(«expr↑ » x : L),«expr↑ » y⁆ :=
  rfl

theorem ext_iff (x y : L') : x = y ↔ (x : L) = y :=
  Subtype.ext_iff

theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 :=
  (ext_iff L' x 0).symm

@[ext]
theorem ext (L₁' L₂' : LieSubalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' :=
  by 
    cases L₁' 
    cases L₂' 
    simp only 
    ext x 
    exact h x

theorem ext_iff' (L₁' L₂' : LieSubalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
  ⟨fun h x =>
      by 
        rw [h],
    ext L₁' L₂'⟩

@[simp]
theorem mk_coe (S : Set L) h₁ h₂ h₃ h₄ : ((⟨⟨S, h₁, h₂, h₃⟩, h₄⟩ : LieSubalgebra R L) : Set L) = S :=
  rfl

@[simp]
theorem coe_to_submodule_mk (p : Submodule R L) h :
  (({ p with lie_mem' := h } : LieSubalgebra R L) : Submodule R L) = p :=
  by 
    cases p 
    rfl

theorem coe_injective : Function.Injective (coeₓ : LieSubalgebra R L → Set L) :=
  by 
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h 
    congr

@[normCast]
theorem coe_set_eq (L₁' L₂' : LieSubalgebra R L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' :=
  coe_injective.eq_iff

theorem to_submodule_injective : Function.Injective (coeₓ : LieSubalgebra R L → Submodule R L) :=
  fun L₁' L₂' h =>
    by 
      rw [SetLike.ext'_iff] at h 
      rw [←coe_set_eq]
      exact h

@[simp]
theorem coe_to_submodule_eq_iff (L₁' L₂' : LieSubalgebra R L) :
  (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂' :=
  to_submodule_injective.eq_iff

@[normCast]
theorem coe_to_submodule : ((L' : Submodule R L) : Set L) = L' :=
  rfl

section LieModule

variable {M : Type w} [AddCommGroupₓ M] [LieRingModule L M]

variable {N : Type w₁} [AddCommGroupₓ N] [LieRingModule L N] [Module R N] [LieModule R L N]

/-- Given a Lie algebra `L` containing a Lie subalgebra `L' ⊆ L`, together with a Lie ring module
`M` of `L`, we may regard `M` as a Lie ring module of `L'` by restriction. -/
instance : LieRingModule L' M :=
  { bracket := fun x m => ⁅(x : L),m⁆, add_lie := fun x y m => add_lie x y m, lie_add := fun x y m => lie_add x y m,
    leibniz_lie := fun x y m => leibniz_lie x y m }

@[simp]
theorem coe_bracket_of_module (x : L') (m : M) : ⁅x,m⁆ = ⁅(x : L),m⁆ :=
  rfl

variable [Module R M] [LieModule R L M]

/-- Given a Lie algebra `L` containing a Lie subalgebra `L' ⊆ L`, together with a Lie module `M` of
`L`, we may regard `M` as a Lie module of `L'` by restriction. -/
instance : LieModule R L' M :=
  { smul_lie :=
      fun t x m =>
        by 
          simp only [coe_bracket_of_module, smul_lie, Submodule.coe_smul_of_tower],
    lie_smul :=
      fun t x m =>
        by 
          simp only [coe_bracket_of_module, lie_smul] }

/-- An `L`-equivariant map of Lie modules `M → N` is `L'`-equivariant for any Lie subalgebra
`L' ⊆ L`. -/
def _root_.lie_module_hom.restrict_lie (f : M →ₗ⁅R,L⁆ N) (L' : LieSubalgebra R L) : M →ₗ⁅R,L'⁆ N :=
  { (f : M →ₗ[R] N) with map_lie' := fun x m => f.map_lie («expr↑ » x) m }

@[simp]
theorem _root_.lie_module_hom.coe_restrict_lie (f : M →ₗ⁅R,L⁆ N) : «expr⇑ » (f.restrict_lie L') = f :=
  rfl

end LieModule

/-- The embedding of a Lie subalgebra into the ambient space as a morphism of Lie algebras. -/
def incl : L' →ₗ⁅R⁆ L :=
  { (L' : Submodule R L).Subtype with
    map_lie' :=
      fun x y =>
        by 
          simp only [LinearMap.to_fun_eq_coe, Submodule.subtype_apply]
          rfl }

@[simp]
theorem coe_incl : «expr⇑ » L'.incl = coeₓ :=
  rfl

/-- The embedding of a Lie subalgebra into the ambient space as a morphism of Lie modules. -/
def incl' : L' →ₗ⁅R,L'⁆ L :=
  { (L' : Submodule R L).Subtype with
    map_lie' :=
      fun x y =>
        by 
          simp only [coe_bracket_of_module, LinearMap.to_fun_eq_coe, Submodule.subtype_apply, coe_bracket] }

@[simp]
theorem coe_incl' : «expr⇑ » L'.incl' = coeₓ :=
  rfl

end LieSubalgebra

variable {R L} {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

namespace LieHom

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
def range : LieSubalgebra R L₂ :=
  { (f : L →ₗ[R] L₂).range with
    lie_mem' :=
      fun x y =>
        show x ∈ f.to_linear_map.range → y ∈ f.to_linear_map.range → ⁅x,y⁆ ∈ f.to_linear_map.range by 
          repeat' 
            rw [LinearMap.mem_range]
          rintro ⟨x', hx⟩ ⟨y', hy⟩
          refine' ⟨⁅x',y'⁆, _⟩
          rw [←hx, ←hy]
          change f ⁅x',y'⁆ = ⁅f x',f y'⁆
          rw [map_lie] }

@[simp]
theorem range_coe : (f.range : Set L₂) = Set.Range f :=
  LinearMap.range_coe («expr↑ » f)

@[simp]
theorem mem_range (x : L₂) : x ∈ f.range ↔ ∃ y : L, f y = x :=
  LinearMap.mem_range

theorem mem_range_self (x : L) : f x ∈ f.range :=
  LinearMap.mem_range_self f x

/-- We can restrict a morphism to a (surjective) map to its range. -/
def range_restrict : L →ₗ⁅R⁆ f.range :=
  { (f : L →ₗ[R] L₂).range_restrict with
    map_lie' :=
      fun x y =>
        by 
          apply Subtype.ext 
          exact f.map_lie x y }

@[simp]
theorem range_restrict_apply (x : L) : f.range_restrict x = ⟨f x, f.mem_range_self x⟩ :=
  rfl

theorem surjective_range_restrict : Function.Surjective f.range_restrict :=
  by 
    rintro ⟨y, hy⟩
    erw [mem_range] at hy 
    obtain ⟨x, rfl⟩ := hy 
    use x 
    simp only [Subtype.mk_eq_mk, range_restrict_apply]

end LieHom

theorem Submodule.exists_lie_subalgebra_coe_eq_iff (p : Submodule R L) :
  (∃ K : LieSubalgebra R L, «expr↑ » K = p) ↔ ∀ x y : L, x ∈ p → y ∈ p → ⁅x,y⁆ ∈ p :=
  by 
    split 
    ·
      rintro ⟨K, rfl⟩
      exact K.lie_mem'
    ·
      intro h 
      use { p with lie_mem' := h }
      exact LieSubalgebra.coe_to_submodule_mk p _

namespace LieSubalgebra

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

@[simp]
theorem incl_range : K.incl.range = K :=
  by 
    rw [←coe_to_submodule_eq_iff]
    exact (K : Submodule R L).range_subtype

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
def map : LieSubalgebra R L₂ :=
  { (K : Submodule R L).map (f : L →ₗ[R] L₂) with
    lie_mem' :=
      fun x y hx hy =>
        by 
          erw [Submodule.mem_map] at hx 
          rcases hx with ⟨x', hx', hx⟩
          rw [←hx]
          erw [Submodule.mem_map] at hy 
          rcases hy with ⟨y', hy', hy⟩
          rw [←hy]
          erw [Submodule.mem_map]
          exact ⟨⁅x',y'⁆, K.lie_mem hx' hy', f.map_lie x' y'⟩ }

@[simp]
theorem mem_map (x : L₂) : x ∈ K.map f ↔ ∃ y : L, y ∈ K ∧ f y = x :=
  Submodule.mem_map

@[simp]
theorem mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (x : L₂) :
  x ∈ K.map (e : L →ₗ⁅R⁆ L₂) ↔ x ∈ (K : Submodule R L).map (e : L →ₗ[R] L₂) :=
  Iff.rfl

/-- The preimage of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
domain. -/
def comap : LieSubalgebra R L :=
  { (K₂ : Submodule R L₂).comap (f : L →ₗ[R] L₂) with
    lie_mem' :=
      fun x y hx hy =>
        by 
          suffices  : ⁅f x,f y⁆ ∈ K₂
          ·
            ·
              simp [this]
          exact K₂.lie_mem hx hy }

section LatticeStructure

open Set

instance : PartialOrderₓ (LieSubalgebra R L) :=
  { PartialOrderₓ.lift (coeₓ : LieSubalgebra R L → Set L) coe_injective with le := fun N N' => ∀ ⦃x⦄, x ∈ N → x ∈ N' }

theorem le_def : K ≤ K' ↔ (K : Set L) ⊆ K' :=
  Iff.rfl

@[simp, normCast]
theorem coe_submodule_le_coe_submodule : (K : Submodule R L) ≤ K' ↔ K ≤ K' :=
  Iff.rfl

instance : HasBot (LieSubalgebra R L) :=
  ⟨0⟩

@[simp]
theorem bot_coe : ((⊥ : LieSubalgebra R L) : Set L) = {0} :=
  rfl

@[simp]
theorem bot_coe_submodule : ((⊥ : LieSubalgebra R L) : Submodule R L) = ⊥ :=
  rfl

@[simp]
theorem mem_bot (x : L) : x ∈ (⊥ : LieSubalgebra R L) ↔ x = 0 :=
  mem_singleton_iff

instance : HasTop (LieSubalgebra R L) :=
  ⟨{ (⊤ : Submodule R L) with lie_mem' := fun x y hx hy => mem_univ ⁅x,y⁆ }⟩

@[simp]
theorem top_coe : ((⊤ : LieSubalgebra R L) : Set L) = univ :=
  rfl

@[simp]
theorem top_coe_submodule : ((⊤ : LieSubalgebra R L) : Submodule R L) = ⊤ :=
  rfl

@[simp]
theorem mem_top (x : L) : x ∈ (⊤ : LieSubalgebra R L) :=
  mem_univ x

theorem _root_.lie_hom.range_eq_map : f.range = map f ⊤ :=
  by 
    ext 
    simp 

instance : HasInf (LieSubalgebra R L) :=
  ⟨fun K K' =>
      { (K⊓K' : Submodule R L) with
        lie_mem' := fun x y hx hy => mem_inter (K.lie_mem hx.1 hy.1) (K'.lie_mem hx.2 hy.2) }⟩

instance : HasInfₓ (LieSubalgebra R L) :=
  ⟨fun S =>
      { Inf {(s : Submodule R L) | (s)(_ : s ∈ S) } with
        lie_mem' :=
          fun x y hx hy =>
            by 
              simp only [Submodule.mem_carrier, mem_Inter, Submodule.Inf_coe, mem_set_of_eq, forall_apply_eq_imp_iff₂,
                exists_imp_distrib] at *
              intro K hK 
              exact K.lie_mem (hx K hK) (hy K hK) }⟩

@[simp]
theorem inf_coe : («expr↑ » (K⊓K') : Set L) = K ∩ K' :=
  rfl

@[simp]
theorem Inf_coe_to_submodule (S : Set (LieSubalgebra R L)) :
  («expr↑ » (Inf S) : Submodule R L) = Inf {(s : Submodule R L) | (s)(_ : s ∈ S) } :=
  rfl

@[simp]
theorem Inf_coe (S : Set (LieSubalgebra R L)) : («expr↑ » (Inf S) : Set L) = ⋂(s : _)(_ : s ∈ S), (s : Set L) :=
  by 
    rw [←coe_to_submodule, Inf_coe_to_submodule, Submodule.Inf_coe]
    ext x 
    simpa only [mem_Inter, mem_set_of_eq, forall_apply_eq_imp_iff₂, exists_imp_distrib]

-- error in Algebra.Lie.Subalgebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Inf_glb (S : set (lie_subalgebra R L)) : is_glb S (Inf S) :=
begin
  have [ident h] [":", expr ∀ K K' : lie_subalgebra R L, «expr ↔ »(«expr ≤ »((K : set L), K'), «expr ≤ »(K, K'))] [],
  { intros [],
    exact [expr iff.rfl] },
  apply [expr is_glb.of_image h],
  simp [] [] ["only"] ["[", expr Inf_coe, "]"] [] [],
  exact [expr is_glb_binfi]
end

/-- The set of Lie subalgebras of a Lie algebra form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `complete_lattice_of_Inf`. -/
instance : CompleteLattice (LieSubalgebra R L) :=
  { completeLatticeOfInf _ Inf_glb with bot := ⊥,
    bot_le :=
      fun N _ h =>
        by 
          rw [mem_bot] at h 
          rw [h]
          exact N.zero_mem',
    top := ⊤, le_top := fun _ _ _ => trivialₓ, inf := ·⊓·, le_inf := fun N₁ N₂ N₃ h₁₂ h₁₃ m hm => ⟨h₁₂ hm, h₁₃ hm⟩,
    inf_le_left := fun _ _ _ => And.left, inf_le_right := fun _ _ _ => And.right }

instance : AddCommMonoidₓ (LieSubalgebra R L) :=
  { add := ·⊔·, add_assoc := fun _ _ _ => sup_assoc, zero := ⊥, zero_add := fun _ => bot_sup_eq,
    add_zero := fun _ => sup_bot_eq, add_comm := fun _ _ => sup_comm }

@[simp]
theorem add_eq_sup : (K+K') = K⊔K' :=
  rfl

@[normCast, simp]
theorem inf_coe_to_submodule : («expr↑ » (K⊓K') : Submodule R L) = (K : Submodule R L)⊓(K' : Submodule R L) :=
  rfl

@[simp]
theorem mem_inf (x : L) : x ∈ K⊓K' ↔ x ∈ K ∧ x ∈ K' :=
  by 
    rw [←mem_coe_submodule, ←mem_coe_submodule, ←mem_coe_submodule, inf_coe_to_submodule, Submodule.mem_inf]

theorem eq_bot_iff : K = ⊥ ↔ ∀ x : L, x ∈ K → x = 0 :=
  by 
    rw [eq_bot_iff]
    exact Iff.rfl

theorem subsingleton_of_bot : Subsingleton (LieSubalgebra R («expr↥ » (⊥ : LieSubalgebra R L))) :=
  by 
    apply subsingleton_of_bot_eq_top 
    ext ⟨x, hx⟩
    change x ∈ ⊥ at hx 
    rw [Submodule.mem_bot] at hx 
    subst hx 
    simp only [true_iffₓ, eq_self_iff_true, Submodule.mk_eq_zero, mem_bot]

variable (R L)

theorem well_founded_of_noetherian [IsNoetherian R L] :
  WellFounded (· > · : LieSubalgebra R L → LieSubalgebra R L → Prop) :=
  by 
    let f : (· > · : LieSubalgebra R L → LieSubalgebra R L → Prop) →r (· > · : Submodule R L → Submodule R L → Prop) :=
      { toFun := coeₓ, map_rel' := fun N N' h => h }
    apply f.well_founded 
    rw [←is_noetherian_iff_well_founded]
    infer_instance

variable {R L K K' f}

section NestedSubalgebras

variable (h : K ≤ K')

/-- Given two nested Lie subalgebras `K ⊆ K'`, the inclusion `K ↪ K'` is a morphism of Lie
algebras. -/
def hom_of_le : K →ₗ⁅R⁆ K' :=
  { Submodule.ofLe h with map_lie' := fun x y => rfl }

@[simp]
theorem coe_hom_of_le (x : K) : (hom_of_le h x : L) = x :=
  rfl

theorem hom_of_le_apply (x : K) : hom_of_le h x = ⟨x.1, h x.2⟩ :=
  rfl

theorem hom_of_le_injective : Function.Injective (hom_of_le h) :=
  fun x y =>
    by 
      simp only [hom_of_le_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe, Subtype.val_eq_coe]

/-- Given two nested Lie subalgebras `K ⊆ K'`, we can view `K` as a Lie subalgebra of `K'`,
regarded as Lie algebra in its own right. -/
def of_le : LieSubalgebra R K' :=
  (hom_of_le h).range

@[simp]
theorem mem_of_le (x : K') : x ∈ of_le h ↔ (x : L) ∈ K :=
  by 
    simp only [of_le, hom_of_le_apply, LieHom.mem_range]
    split 
    ·
      rintro ⟨y, rfl⟩
      exact y.property
    ·
      intro h 
      use ⟨(x : L), h⟩
      simp 

theorem of_le_eq_comap_incl : of_le h = K.comap K'.incl :=
  by 
    ext 
    rw [mem_of_le]
    rfl

end NestedSubalgebras

theorem map_le_iff_le_comap {K : LieSubalgebra R L} {K' : LieSubalgebra R L₂} : map f K ≤ K' ↔ K ≤ comap f K' :=
  Set.image_subset_iff

theorem gc_map_comap : GaloisConnection (map f) (comap f) :=
  fun K K' => map_le_iff_le_comap

end LatticeStructure

section LieSpan

variable (R L) (s : Set L)

/-- The Lie subalgebra of a Lie algebra `L` generated by a subset `s ⊆ L`. -/
def lie_span : LieSubalgebra R L :=
  Inf { N | s ⊆ N }

variable {R L s}

theorem mem_lie_span {x : L} : x ∈ lie_span R L s ↔ ∀ K : LieSubalgebra R L, s ⊆ K → x ∈ K :=
  by 
    change x ∈ (lie_span R L s : Set L) ↔ _ 
    erw [Inf_coe]
    exact Set.mem_bInter_iff

theorem subset_lie_span : s ⊆ lie_span R L s :=
  by 
    intro m hm 
    erw [mem_lie_span]
    intro K hK 
    exact hK hm

theorem submodule_span_le_lie_span : Submodule.span R s ≤ lie_span R L s :=
  by 
    rw [Submodule.span_le]
    apply subset_lie_span

theorem lie_span_le {K} : lie_span R L s ≤ K ↔ s ⊆ K :=
  by 
    split 
    ·
      exact Set.Subset.trans subset_lie_span
    ·
      intro hs m hm 
      rw [mem_lie_span] at hm 
      exact hm _ hs

theorem lie_span_mono {t : Set L} (h : s ⊆ t) : lie_span R L s ≤ lie_span R L t :=
  by 
    rw [lie_span_le]
    exact Set.Subset.trans h subset_lie_span

theorem lie_span_eq : lie_span R L (K : Set L) = K :=
  le_antisymmₓ (lie_span_le.mpr rfl.Subset) subset_lie_span

theorem coe_lie_span_submodule_eq_iff {p : Submodule R L} :
  (lie_span R L (p : Set L) : Submodule R L) = p ↔ ∃ K : LieSubalgebra R L, «expr↑ » K = p :=
  by 
    rw [p.exists_lie_subalgebra_coe_eq_iff]
    split  <;> intro h
    ·
      intro x m hm 
      rw [←h, mem_coe_submodule]
      exact lie_mem _ (subset_lie_span hm)
    ·
      rw [←coe_to_submodule_mk p h, coe_to_submodule, coe_to_submodule_eq_iff, lie_span_eq]

variable (R L)

/-- `lie_span` forms a Galois insertion with the coercion from `lie_subalgebra` to `set`. -/
protected def gi : GaloisInsertion (lie_span R L : Set L → LieSubalgebra R L) coeₓ :=
  { choice := fun s _ => lie_span R L s, gc := fun s t => lie_span_le, le_l_u := fun s => subset_lie_span,
    choice_eq := fun s h => rfl }

@[simp]
theorem span_empty : lie_span R L (∅ : Set L) = ⊥ :=
  (LieSubalgebra.gi R L).gc.l_bot

@[simp]
theorem span_univ : lie_span R L (Set.Univ : Set L) = ⊤ :=
  eq_top_iff.2$ SetLike.le_def.2$ subset_lie_span

variable {L}

theorem span_union (s t : Set L) : lie_span R L (s ∪ t) = lie_span R L s⊔lie_span R L t :=
  (LieSubalgebra.gi R L).gc.l_sup

theorem span_Union {ι} (s : ι → Set L) : lie_span R L (⋃i, s i) = ⨆i, lie_span R L (s i) :=
  (LieSubalgebra.gi R L).gc.l_supr

end LieSpan

end LieSubalgebra

end LieSubalgebra

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w}

variable [CommRingₓ R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂]

/-- An injective Lie algebra morphism is an equivalence onto its range. -/
noncomputable def of_injective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) : L₁ ≃ₗ⁅R⁆ f.range :=
  { LinearEquiv.ofInjective («expr↑ » f)$
      by 
        rwa [LieHom.coe_to_linear_map] with
    map_lie' :=
      fun x y =>
        by 
          apply SetCoe.ext 
          simpa }

@[simp]
theorem of_injective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) (x : L₁) :
  «expr↑ » (of_injective f h x) = f x :=
  rfl

variable (L₁' L₁'' : LieSubalgebra R L₁) (L₂' : LieSubalgebra R L₂)

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
def of_eq (h : (L₁' : Set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
  { LinearEquiv.ofEq («expr↑ » L₁') («expr↑ » L₁'')
      (by 
        ext x 
        change x ∈ (L₁' : Set L₁) ↔ x ∈ (L₁'' : Set L₁)
        rw [h]) with
    map_lie' :=
      fun x y =>
        by 
          apply SetCoe.ext 
          simp  }

@[simp]
theorem of_eq_apply (L L' : LieSubalgebra R L₁) (h : (L : Set L₁) = L') (x : L) :
  («expr↑ » (of_eq L L' h x) : L₁) = x :=
  rfl

variable (e : L₁ ≃ₗ⁅R⁆ L₂)

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebra : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : LieSubalgebra R L₂) :=
  { LinearEquiv.ofSubmodule (e : L₁ ≃ₗ[R] L₂) («expr↑ » L₁'') with
    map_lie' :=
      fun x y =>
        by 
          apply SetCoe.ext 
          exact LieHom.map_lie («expr↑ » e : L₁ →ₗ⁅R⁆ L₂) («expr↑ » x) («expr↑ » y) }

@[simp]
theorem of_subalgebra_apply (x : L₁'') : «expr↑ » (e.of_subalgebra _ x) = e x :=
  rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebras (h : L₁'.map («expr↑ » e) = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
  { LinearEquiv.ofSubmodules (e : L₁ ≃ₗ[R] L₂) («expr↑ » L₁') («expr↑ » L₂')
      (by 
        rw [←h]
        rfl) with
    map_lie' :=
      fun x y =>
        by 
          apply SetCoe.ext 
          exact LieHom.map_lie («expr↑ » e : L₁ →ₗ⁅R⁆ L₂) («expr↑ » x) («expr↑ » y) }

@[simp]
theorem of_subalgebras_apply (h : L₁'.map («expr↑ » e) = L₂') (x : L₁') : «expr↑ » (e.of_subalgebras _ _ h x) = e x :=
  rfl

@[simp]
theorem of_subalgebras_symm_apply (h : L₁'.map («expr↑ » e) = L₂') (x : L₂') :
  «expr↑ » ((e.of_subalgebras _ _ h).symm x) = e.symm x :=
  rfl

end LieEquiv

