import Mathbin.Algebra.Lie.Subalgebra 
import Mathbin.RingTheory.Noetherian

/-!
# Lie submodules of a Lie algebra

In this file we define Lie submodules and Lie ideals, we construct the lattice structure on Lie
submodules and we use it to define various important operations, notably the Lie span of a subset
of a Lie module.

## Main definitions

  * `lie_submodule`
  * `lie_submodule.well_founded_of_noetherian`
  * `lie_submodule.lie_span`
  * `lie_submodule.map`
  * `lie_submodule.comap`
  * `lie_ideal`
  * `lie_ideal.map`
  * `lie_ideal.comap`

## Tags

lie algebra, lie submodule, lie ideal, lattice structure
-/


universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [AddCommGroupₓ M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure LieSubmodule extends Submodule R M where 
  lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x,m⁆ ∈ carrier

attribute [nolint doc_blame] LieSubmodule.toSubmodule

namespace LieSubmodule

variable {R L M} (N N' : LieSubmodule R L M)

instance : SetLike (LieSubmodule R L M) M :=
  { coe := carrier,
    coe_injective' :=
      fun N O h =>
        by 
          cases N <;> cases O <;> congr }

/-- The zero module is a Lie submodule of any Lie module. -/
instance : HasZero (LieSubmodule R L M) :=
  ⟨{ (0 : Submodule R M) with
      lie_mem :=
        fun x m h =>
          by 
            rw [(Submodule.mem_bot R).1 h]
            apply lie_zero }⟩

instance : Inhabited (LieSubmodule R L M) :=
  ⟨0⟩

instance coe_submodule : Coe (LieSubmodule R L M) (Submodule R M) :=
  ⟨to_submodule⟩

@[normCast]
theorem coe_to_submodule : ((N : Submodule R M) : Set M) = N :=
  rfl

@[simp]
theorem mem_carrier {x : M} : x ∈ N.carrier ↔ x ∈ (N : Set M) :=
  Iff.rfl

@[simp]
theorem mem_mk_iff (S : Set M) h₁ h₂ h₃ h₄ {x : M} : x ∈ (⟨S, h₁, h₂, h₃, h₄⟩ : LieSubmodule R L M) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_coe_submodule {x : M} : x ∈ (N : Submodule R M) ↔ x ∈ N :=
  Iff.rfl

theorem mem_coe {x : M} : x ∈ (N : Set M) ↔ x ∈ N :=
  Iff.rfl

@[simp]
theorem zero_mem : (0 : M) ∈ N :=
  (N : Submodule R M).zero_mem

@[simp]
theorem coe_to_set_mk (S : Set M) h₁ h₂ h₃ h₄ : ((⟨S, h₁, h₂, h₃, h₄⟩ : LieSubmodule R L M) : Set M) = S :=
  rfl

@[simp]
theorem coe_to_submodule_mk (p : Submodule R M) h :
  (({ p with lie_mem := h } : LieSubmodule R L M) : Submodule R M) = p :=
  by 
    cases p 
    rfl

theorem coe_submodule_injective : Function.Injective (to_submodule : LieSubmodule R L M → Submodule R M) :=
  fun x y h =>
    by 
      cases x 
      cases y 
      congr 
      injection h

@[ext]
theorem ext (h : ∀ m, m ∈ N ↔ m ∈ N') : N = N' :=
  SetLike.ext h

@[simp]
theorem coe_to_submodule_eq_iff : (N : Submodule R M) = (N' : Submodule R M) ↔ N = N' :=
  coe_submodule_injective.eq_iff

/-- Copy of a lie_submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (s : Set M) (hs : s = «expr↑ » N) : LieSubmodule R L M :=
  { Carrier := s, zero_mem' := hs.symm ▸ N.zero_mem', add_mem' := hs.symm ▸ N.add_mem',
    smul_mem' := hs.symm ▸ N.smul_mem', lie_mem := hs.symm ▸ N.lie_mem }

@[simp]
theorem coe_copy (S : LieSubmodule R L M) (s : Set M) (hs : s = «expr↑ » S) : (S.copy s hs : Set M) = s :=
  rfl

theorem copy_eq (S : LieSubmodule R L M) (s : Set M) (hs : s = «expr↑ » S) : S.copy s hs = S :=
  coe_submodule_injective (SetLike.coe_injective hs)

instance : LieRingModule L N :=
  { bracket := fun x : L m : N => ⟨⁅x,m.val⁆, N.lie_mem m.property⟩,
    add_lie :=
      by 
        intro x y m 
        apply SetCoe.ext 
        apply add_lie,
    lie_add :=
      by 
        intro x m n 
        apply SetCoe.ext 
        apply lie_add,
    leibniz_lie :=
      by 
        intro x y m 
        apply SetCoe.ext 
        apply leibniz_lie }

instance : LieModule R L N :=
  { lie_smul :=
      by 
        intro t x y 
        apply SetCoe.ext 
        apply lie_smul,
    smul_lie :=
      by 
        intro t x y 
        apply SetCoe.ext 
        apply smul_lie }

@[simp, normCast]
theorem coe_zero : ((0 : N) : M) = (0 : M) :=
  rfl

@[simp, normCast]
theorem coe_add (m m' : N) : («expr↑ » (m+m') : M) = (m : M)+(m' : M) :=
  rfl

@[simp, normCast]
theorem coe_neg (m : N) : («expr↑ » (-m) : M) = -(m : M) :=
  rfl

@[simp, normCast]
theorem coe_sub (m m' : N) : («expr↑ » (m - m') : M) = (m : M) - (m' : M) :=
  rfl

@[simp, normCast]
theorem coe_smul (t : R) (m : N) : («expr↑ » (t • m) : M) = t • (m : M) :=
  rfl

@[simp, normCast]
theorem coe_bracket (x : L) (m : N) : («expr↑ » ⁅x,m⁆ : M) = ⁅x,«expr↑ » m⁆ :=
  rfl

end LieSubmodule

section LieIdeal

variable (L)

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
abbrev LieIdeal :=
  LieSubmodule R L L

theorem lie_mem_right (I : LieIdeal R L) (x y : L) (h : y ∈ I) : ⁅x,y⁆ ∈ I :=
  I.lie_mem h

theorem lie_mem_left (I : LieIdeal R L) (x y : L) (h : x ∈ I) : ⁅x,y⁆ ∈ I :=
  by 
    rw [←lie_skew, ←neg_lie]
    apply lie_mem_right 
    assumption

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
def lieIdealSubalgebra (I : LieIdeal R L) : LieSubalgebra R L :=
  { I.to_submodule with
    lie_mem' :=
      by 
        intro x y hx hy 
        apply lie_mem_right 
        exact hy }

instance : Coe (LieIdeal R L) (LieSubalgebra R L) :=
  ⟨fun I => lieIdealSubalgebra R L I⟩

@[normCast]
theorem LieIdeal.coe_to_subalgebra (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Set L) = I :=
  rfl

@[normCast]
theorem LieIdeal.coe_to_lie_subalgebra_to_submodule (I : LieIdeal R L) :
  ((I : LieSubalgebra R L) : Submodule R L) = I :=
  rfl

end LieIdeal

variable {R M}

theorem Submodule.exists_lie_submodule_coe_eq_iff (p : Submodule R M) :
  (∃ N : LieSubmodule R L M, «expr↑ » N = p) ↔ ∀ x : L m : M, m ∈ p → ⁅x,m⁆ ∈ p :=
  by 
    split 
    ·
      rintro ⟨N, rfl⟩
      exact N.lie_mem
    ·
      intro h 
      use { p with lie_mem := h }
      exact LieSubmodule.coe_to_submodule_mk p _

namespace LieSubalgebra

variable {L}

/-- Given a Lie subalgebra `K ⊆ L`, if we view `L` as a `K`-module by restriction, it contains
a distinguished Lie submodule for the action of `K`, namely `K` itself. -/
def to_lie_submodule (K : LieSubalgebra R L) : LieSubmodule R K L :=
  { (K : Submodule R L) with lie_mem := fun x y hy => K.lie_mem x.property hy }

@[simp]
theorem coe_to_lie_submodule (K : LieSubalgebra R L) : (K.to_lie_submodule : Submodule R L) = K :=
  by 
    rcases K with ⟨⟨⟩⟩
    rfl

@[simp]
theorem mem_to_lie_submodule {K : LieSubalgebra R L} (x : L) : x ∈ K.to_lie_submodule ↔ x ∈ K :=
  Iff.rfl

theorem exists_lie_ideal_coe_eq_iff (K : LieSubalgebra R L) :
  (∃ I : LieIdeal R L, «expr↑ » I = K) ↔ ∀ x y : L, y ∈ K → ⁅x,y⁆ ∈ K :=
  by 
    simp only [←coe_to_submodule_eq_iff, LieIdeal.coe_to_lie_subalgebra_to_submodule,
      Submodule.exists_lie_submodule_coe_eq_iff L]
    exact Iff.rfl

theorem exists_nested_lie_ideal_coe_eq_iff {K K' : LieSubalgebra R L} (h : K ≤ K') :
  (∃ I : LieIdeal R K', «expr↑ » I = of_le h) ↔ ∀ x y : L, x ∈ K' → y ∈ K → ⁅x,y⁆ ∈ K :=
  by 
    simp only [exists_lie_ideal_coe_eq_iff, coe_bracket, mem_of_le]
    split 
    ·
      intro h' x y hx hy 
      exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
    ·
      rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy' 
      exact h' x y hx hy'

end LieSubalgebra

end LieSubmodule

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [AddCommGroupₓ M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

section LatticeStructure

open Set

theorem coe_injective : Function.Injective (coeₓ : LieSubmodule R L M → Set M) :=
  SetLike.coe_injective

@[simp, normCast]
theorem coe_submodule_le_coe_submodule : (N : Submodule R M) ≤ N' ↔ N ≤ N' :=
  Iff.rfl

instance : HasBot (LieSubmodule R L M) :=
  ⟨0⟩

@[simp]
theorem bot_coe : ((⊥ : LieSubmodule R L M) : Set M) = {0} :=
  rfl

@[simp]
theorem bot_coe_submodule : ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥ :=
  rfl

@[simp]
theorem mem_bot (x : M) : x ∈ (⊥ : LieSubmodule R L M) ↔ x = 0 :=
  mem_singleton_iff

instance : HasTop (LieSubmodule R L M) :=
  ⟨{ (⊤ : Submodule R M) with lie_mem := fun x m h => mem_univ ⁅x,m⁆ }⟩

@[simp]
theorem top_coe : ((⊤ : LieSubmodule R L M) : Set M) = univ :=
  rfl

@[simp]
theorem top_coe_submodule : ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤ :=
  rfl

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : LieSubmodule R L M) :=
  mem_univ x

instance : HasInf (LieSubmodule R L M) :=
  ⟨fun N N' => { (N⊓N' : Submodule R M) with lie_mem := fun x m h => mem_inter (N.lie_mem h.1) (N'.lie_mem h.2) }⟩

instance : HasInfₓ (LieSubmodule R L M) :=
  ⟨fun S =>
      { Inf {(s : Submodule R M) | (s)(_ : s ∈ S) } with
        lie_mem :=
          fun x m h =>
            by 
              simp only [Submodule.mem_carrier, mem_Inter, Submodule.Inf_coe, mem_set_of_eq, forall_apply_eq_imp_iff₂,
                exists_imp_distrib] at *
              intro N hN 
              apply N.lie_mem (h N hN) }⟩

@[simp]
theorem inf_coe : («expr↑ » (N⊓N') : Set M) = N ∩ N' :=
  rfl

@[simp]
theorem Inf_coe_to_submodule (S : Set (LieSubmodule R L M)) :
  («expr↑ » (Inf S) : Submodule R M) = Inf {(s : Submodule R M) | (s)(_ : s ∈ S) } :=
  rfl

@[simp]
theorem Inf_coe (S : Set (LieSubmodule R L M)) : («expr↑ » (Inf S) : Set M) = ⋂(s : _)(_ : s ∈ S), (s : Set M) :=
  by 
    rw [←LieSubmodule.coe_to_submodule, Inf_coe_to_submodule, Submodule.Inf_coe]
    ext m 
    simpa only [mem_Inter, mem_set_of_eq, forall_apply_eq_imp_iff₂, exists_imp_distrib]

-- error in Algebra.Lie.Submodule: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Inf_glb (S : set (lie_submodule R L M)) : is_glb S (Inf S) :=
begin
  have [ident h] [":", expr ∀ N N' : lie_submodule R L M, «expr ↔ »(«expr ≤ »((N : set M), N'), «expr ≤ »(N, N'))] [],
  { intros [],
    refl },
  apply [expr is_glb.of_image h],
  simp [] [] ["only"] ["[", expr Inf_coe, "]"] [] [],
  exact [expr is_glb_binfi]
end

/-- The set of Lie submodules of a Lie module form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `complete_lattice_of_Inf`.  -/
instance : CompleteLattice (LieSubmodule R L M) :=
  { SetLike.partialOrder, completeLatticeOfInf _ Inf_glb with le := · ≤ ·, lt := · < ·, bot := ⊥,
    bot_le :=
      fun N _ h =>
        by 
          rw [mem_bot] at h 
          rw [h]
          exact N.zero_mem',
    top := ⊤, le_top := fun _ _ _ => trivialₓ, inf := ·⊓·, le_inf := fun N₁ N₂ N₃ h₁₂ h₁₃ m hm => ⟨h₁₂ hm, h₁₃ hm⟩,
    inf_le_left := fun _ _ _ => And.left, inf_le_right := fun _ _ _ => And.right }

instance : AddCommMonoidₓ (LieSubmodule R L M) :=
  { add := ·⊔·, add_assoc := fun _ _ _ => sup_assoc, zero := ⊥, zero_add := fun _ => bot_sup_eq,
    add_zero := fun _ => sup_bot_eq, add_comm := fun _ _ => sup_comm }

@[simp]
theorem add_eq_sup : (N+N') = N⊔N' :=
  rfl

-- error in Algebra.Lie.Submodule: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[norm_cast #[], simp]
theorem sup_coe_to_submodule : «expr = »((«expr↑ »(«expr ⊔ »(N, N')) : submodule R M), «expr ⊔ »((N : submodule R M), (N' : submodule R M))) :=
begin
  have [ident aux] [":", expr ∀
   (x : L)
   (m), «expr ∈ »(m, («expr ⊔ »(N, N') : submodule R M)) → «expr ∈ »(«expr⁅ , ⁆»(x, m), («expr ⊔ »(N, N') : submodule R M))] [],
  { simp [] [] ["only"] ["[", expr submodule.mem_sup, "]"] [] [],
    rintro [ident x, ident m, "⟨", ident y, ",", ident hy, ",", ident z, ",", ident hz, ",", ident rfl, "⟩"],
    refine [expr ⟨«expr⁅ , ⁆»(x, y), N.lie_mem hy, «expr⁅ , ⁆»(x, z), N'.lie_mem hz, (lie_add _ _ _).symm⟩] },
  refine [expr le_antisymm (Inf_le ⟨{ lie_mem := aux, ..(«expr ⊔ »(N, N') : submodule R M) }, _⟩) _],
  { simp [] [] ["only"] ["[", expr exists_prop, ",", expr and_true, ",", expr mem_set_of_eq, ",", expr eq_self_iff_true, ",", expr coe_to_submodule_mk, ",", "<-", expr coe_submodule_le_coe_submodule, ",", expr and_self, ",", expr le_sup_left, ",", expr le_sup_right, "]"] [] [] },
  { simp [] [] [] [] [] [] }
end

@[normCast, simp]
theorem inf_coe_to_submodule : («expr↑ » (N⊓N') : Submodule R M) = (N : Submodule R M)⊓(N' : Submodule R M) :=
  rfl

@[simp]
theorem mem_inf (x : M) : x ∈ N⊓N' ↔ x ∈ N ∧ x ∈ N' :=
  by 
    rw [←mem_coe_submodule, ←mem_coe_submodule, ←mem_coe_submodule, inf_coe_to_submodule, Submodule.mem_inf]

theorem mem_sup (x : M) : x ∈ N⊔N' ↔ ∃ (y : _)(_ : y ∈ N)(z : _)(_ : z ∈ N'), (y+z) = x :=
  by 
    rw [←mem_coe_submodule, sup_coe_to_submodule, Submodule.mem_sup]
    exact Iff.rfl

theorem eq_bot_iff : N = ⊥ ↔ ∀ m : M, m ∈ N → m = 0 :=
  by 
    rw [eq_bot_iff]
    exact Iff.rfl

theorem subsingleton_of_bot : Subsingleton (LieSubmodule R L («expr↥ » (⊥ : LieSubmodule R L M))) :=
  by 
    apply subsingleton_of_bot_eq_top 
    ext ⟨x, hx⟩
    change x ∈ ⊥ at hx 
    rw [Submodule.mem_bot] at hx 
    subst hx 
    simp only [true_iffₓ, eq_self_iff_true, Submodule.mk_eq_zero, LieSubmodule.mem_bot]

instance : IsModularLattice (LieSubmodule R L M) :=
  { sup_inf_le_assoc_of_le :=
      fun N₁ N₂ N₃ =>
        by 
          simp only [←coe_submodule_le_coe_submodule, sup_coe_to_submodule, inf_coe_to_submodule]
          exact IsModularLattice.sup_inf_le_assoc_of_le («expr↑ » N₂) }

variable (R L M)

theorem well_founded_of_noetherian [IsNoetherian R M] :
  WellFounded (· > · : LieSubmodule R L M → LieSubmodule R L M → Prop) :=
  by 
    let f :
      (· > · : LieSubmodule R L M → LieSubmodule R L M → Prop) →r (· > · : Submodule R M → Submodule R M → Prop) :=
      { toFun := coeₓ, map_rel' := fun N N' h => h }
    apply f.well_founded 
    rw [←is_noetherian_iff_well_founded]
    infer_instance

@[simp]
theorem subsingleton_iff : Subsingleton (LieSubmodule R L M) ↔ Subsingleton M :=
  have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) :=
    by 
      rw [←subsingleton_iff_bot_eq_top, ←subsingleton_iff_bot_eq_top, ←coe_to_submodule_eq_iff, top_coe_submodule,
        bot_coe_submodule]
  h.trans$ Submodule.subsingleton_iff R

@[simp]
theorem nontrivial_iff : Nontrivial (LieSubmodule R L M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans$ subsingleton_iff R L M).trans not_nontrivial_iff_subsingleton.symm)

instance [Nontrivial M] : Nontrivial (LieSubmodule R L M) :=
  (nontrivial_iff R L M).mpr ‹_›

variable {R L M}

section InclusionMaps

/-- The inclusion of a Lie submodule into its ambient space is a morphism of Lie modules. -/
def incl : N →ₗ⁅R,L⁆ M :=
  { Submodule.subtype (N : Submodule R M) with map_lie' := fun x m => rfl }

@[simp]
theorem incl_apply (m : N) : N.incl m = m :=
  rfl

theorem incl_eq_val : (N.incl : N → M) = Subtype.val :=
  rfl

variable {N N'} (h : N ≤ N')

/-- Given two nested Lie submodules `N ⊆ N'`, the inclusion `N ↪ N'` is a morphism of Lie modules.-/
def hom_of_le : N →ₗ⁅R,L⁆ N' :=
  { Submodule.ofLe (show N.to_submodule ≤ N'.to_submodule from h) with map_lie' := fun x m => rfl }

@[simp]
theorem coe_hom_of_le (m : N) : (hom_of_le h m : M) = m :=
  rfl

theorem hom_of_le_apply (m : N) : hom_of_le h m = ⟨m.1, h m.2⟩ :=
  rfl

theorem hom_of_le_injective : Function.Injective (hom_of_le h) :=
  fun x y =>
    by 
      simp only [hom_of_le_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe, Subtype.val_eq_coe]

end InclusionMaps

section LieSpan

variable (R L) (s : Set M)

/-- The `lie_span` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contains `s`. -/
def lie_span : LieSubmodule R L M :=
  Inf { N | s ⊆ N }

variable {R L s}

theorem mem_lie_span {x : M} : x ∈ lie_span R L s ↔ ∀ N : LieSubmodule R L M, s ⊆ N → x ∈ N :=
  by 
    change x ∈ (lie_span R L s : Set M) ↔ _ 
    erw [Inf_coe]
    exact mem_bInter_iff

theorem subset_lie_span : s ⊆ lie_span R L s :=
  by 
    intro m hm 
    erw [mem_lie_span]
    intro N hN 
    exact hN hm

theorem submodule_span_le_lie_span : Submodule.span R s ≤ lie_span R L s :=
  by 
    rw [Submodule.span_le]
    apply subset_lie_span

theorem lie_span_le {N} : lie_span R L s ≤ N ↔ s ⊆ N :=
  by 
    split 
    ·
      exact subset.trans subset_lie_span
    ·
      intro hs m hm 
      rw [mem_lie_span] at hm 
      exact hm _ hs

theorem lie_span_mono {t : Set M} (h : s ⊆ t) : lie_span R L s ≤ lie_span R L t :=
  by 
    rw [lie_span_le]
    exact subset.trans h subset_lie_span

theorem lie_span_eq : lie_span R L (N : Set M) = N :=
  le_antisymmₓ (lie_span_le.mpr rfl.Subset) subset_lie_span

theorem coe_lie_span_submodule_eq_iff {p : Submodule R M} :
  (lie_span R L (p : Set M) : Submodule R M) = p ↔ ∃ N : LieSubmodule R L M, «expr↑ » N = p :=
  by 
    rw [p.exists_lie_submodule_coe_eq_iff L]
    split  <;> intro h
    ·
      intro x m hm 
      rw [←h, mem_coe_submodule]
      exact lie_mem _ (subset_lie_span hm)
    ·
      rw [←coe_to_submodule_mk p h, coe_to_submodule, coe_to_submodule_eq_iff, lie_span_eq]

variable (R L M)

/-- `lie_span` forms a Galois insertion with the coercion from `lie_submodule` to `set`. -/
protected def gi : GaloisInsertion (lie_span R L : Set M → LieSubmodule R L M) coeₓ :=
  { choice := fun s _ => lie_span R L s, gc := fun s t => lie_span_le, le_l_u := fun s => subset_lie_span,
    choice_eq := fun s h => rfl }

@[simp]
theorem span_empty : lie_span R L (∅ : Set M) = ⊥ :=
  (LieSubmodule.gi R L M).gc.l_bot

@[simp]
theorem span_univ : lie_span R L (Set.Univ : Set M) = ⊤ :=
  eq_top_iff.2$ SetLike.le_def.2$ subset_lie_span

variable {M}

theorem span_union (s t : Set M) : lie_span R L (s ∪ t) = lie_span R L s⊔lie_span R L t :=
  (LieSubmodule.gi R L M).gc.l_sup

theorem span_Union {ι} (s : ι → Set M) : lie_span R L (⋃i, s i) = ⨆i, lie_span R L (s i) :=
  (LieSubmodule.gi R L M).gc.l_supr

end LieSpan

end LatticeStructure

end LieSubmodule

section LieSubmoduleMapAndComap

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroupₓ M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

/-- A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to Lie submodules
of `M'`. -/
def map : LieSubmodule R L M' :=
  { (N : Submodule R M).map (f : M →ₗ[R] M') with
    lie_mem :=
      fun x m' h =>
        by 
          rcases h with ⟨m, hm, hfm⟩
          use ⁅x,m⁆
          split 
          ·
            apply N.lie_mem hm
          ·
            normCast  at hfm 
            simp [hfm] }

/-- A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie submodules of
`M`. -/
def comap : LieSubmodule R L M :=
  { (N' : Submodule R M').comap (f : M →ₗ[R] M') with
    lie_mem :=
      fun x m h =>
        by 
          suffices  : ⁅x,f m⁆ ∈ N'
          ·
            simp [this]
          apply N'.lie_mem h }

variable {f N N₂ N'}

theorem map_le_iff_le_comap : map f N ≤ N' ↔ N ≤ comap f N' :=
  Set.image_subset_iff

variable (f)

theorem gc_map_comap : GaloisConnection (map f) (comap f) :=
  fun N N' => map_le_iff_le_comap

variable {f}

@[simp]
theorem map_sup : (N⊔N₂).map f = N.map f⊔N₂.map f :=
  (gc_map_comap f).l_sup

theorem mem_map (m' : M') : m' ∈ N.map f ↔ ∃ m, m ∈ N ∧ f m = m' :=
  Submodule.mem_map

@[simp]
theorem mem_comap {m : M} : m ∈ comap f N' ↔ f m ∈ N' :=
  Iff.rfl

end LieSubmodule

namespace LieIdeal

variable (f : L →ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

@[simp]
theorem top_coe_lie_subalgebra : ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤ :=
  rfl

/-- A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie ideals of `L'`.

Note that unlike `lie_submodule.map`, we must take the `lie_span` of the image. Mathematically
this is because although `f` makes `L'` into a Lie module over `L`, in general the `L` submodules of
`L'` are not the same as the ideals of `L'`. -/
def map : LieIdeal R L' :=
  LieSubmodule.lieSpan R L'$ (I : Submodule R L).map (f : L →ₗ[R] L')

/-- A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ideals of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism of Lie modules)
and so this is a special case of `lie_submodule.comap` but we do not exploit this fact. -/
def comap : LieIdeal R L :=
  { (J : Submodule R L').comap (f : L →ₗ[R] L') with
    lie_mem :=
      fun x y h =>
        by 
          suffices  : ⁅f x,f y⁆ ∈ J
          ·
            simp [this]
          apply J.lie_mem h }

@[simp]
theorem map_coe_submodule (h : «expr↑ » (map f I) = f '' I) :
  (map f I : Submodule R L') = (I : Submodule R L).map (f : L →ₗ[R] L') :=
  by 
    rw [SetLike.ext'_iff, LieSubmodule.coe_to_submodule, h, Submodule.map_coe]
    rfl

@[simp]
theorem comap_coe_submodule : (comap f J : Submodule R L) = (J : Submodule R L').comap (f : L →ₗ[R] L') :=
  rfl

theorem map_le : map f I ≤ J ↔ f '' I ⊆ J :=
  LieSubmodule.lie_span_le

variable {f I I₂ J}

theorem mem_map {x : L} (hx : x ∈ I) : f x ∈ map f I :=
  by 
    apply LieSubmodule.subset_lie_span 
    use x 
    exact ⟨hx, rfl⟩

@[simp]
theorem mem_comap {x : L} : x ∈ comap f J ↔ f x ∈ J :=
  Iff.rfl

theorem map_le_iff_le_comap : map f I ≤ J ↔ I ≤ comap f J :=
  by 
    rw [map_le]
    exact Set.image_subset_iff

variable (f)

theorem gc_map_comap : GaloisConnection (map f) (comap f) :=
  fun I I' => map_le_iff_le_comap

variable {f}

@[simp]
theorem map_sup : (I⊔I₂).map f = I.map f⊔I₂.map f :=
  (gc_map_comap f).l_sup

theorem map_comap_le : map f (comap f J) ≤ J :=
  by 
    rw [map_le_iff_le_comap]
    apply le_reflₓ _

/-- See also `lie_ideal.map_comap_eq`. -/
theorem comap_map_le : I ≤ comap f (map f I) :=
  by 
    rw [←map_le_iff_le_comap]
    apply le_reflₓ _

@[mono]
theorem map_mono : Monotone (map f) :=
  fun I₁ I₂ h =>
    by 
      rw [SetLike.le_def] at h 
      apply LieSubmodule.lie_span_mono (Set.image_subset («expr⇑ » f) h)

@[mono]
theorem comap_mono : Monotone (comap f) :=
  fun J₁ J₂ h =>
    by 
      rw [←SetLike.coe_subset_coe] at h⊢
      exact Set.preimage_mono h

theorem map_of_image (h : f '' I = J) : I.map f = J :=
  by 
    apply le_antisymmₓ
    ·
      erw [LieSubmodule.lie_span_le, Submodule.map_coe, h]
    ·
      rw [←SetLike.coe_subset_coe, ←h]
      exact LieSubmodule.subset_lie_span

/-- Note that this is not a special case of `lie_submodule.subsingleton_of_bot`. Indeed, given
`I : lie_ideal R L`, in general the two lattices `lie_ideal R I` and `lie_submodule R L I` are
different (though the latter does naturally inject into the former).

In other words, in general, ideals of `I`, regarded as a Lie algebra in its own right, are not the
same as ideals of `L` contained in `I`. -/
theorem subsingleton_of_bot : Subsingleton (LieIdeal R («expr↥ » (⊥ : LieIdeal R L))) :=
  by 
    apply subsingleton_of_bot_eq_top 
    ext ⟨x, hx⟩
    change x ∈ ⊥ at hx 
    rw [Submodule.mem_bot] at hx 
    subst hx 
    simp only [true_iffₓ, eq_self_iff_true, Submodule.mk_eq_zero, LieSubmodule.mem_bot]

end LieIdeal

namespace LieHom

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : LieIdeal R L :=
  LieIdeal.comap f ⊥

/-- The range of a morphism of Lie algebras as an ideal in the codomain. -/
def ideal_range : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' f.range

theorem ideal_range_eq_lie_span_range : f.ideal_range = LieSubmodule.lieSpan R L' f.range :=
  rfl

theorem ideal_range_eq_map : f.ideal_range = LieIdeal.map f ⊤ :=
  by 
    ext 
    simp only [ideal_range, range_eq_map]
    rfl

/-- The condition that the image of a morphism of Lie algebras is an ideal. -/
def is_ideal_morphism : Prop :=
  (f.ideal_range : LieSubalgebra R L') = f.range

@[simp]
theorem is_ideal_morphism_def : f.is_ideal_morphism ↔ (f.ideal_range : LieSubalgebra R L') = f.range :=
  Iff.rfl

theorem is_ideal_morphism_iff : f.is_ideal_morphism ↔ ∀ x : L' y : L, ∃ z : L, ⁅x,f y⁆ = f z :=
  by 
    simp only [is_ideal_morphism_def, ideal_range_eq_lie_span_range, ←LieSubalgebra.coe_to_submodule_eq_iff,
      ←f.range.coe_to_submodule, LieIdeal.coe_to_lie_subalgebra_to_submodule,
      LieSubmodule.coe_lie_span_submodule_eq_iff, LieSubalgebra.mem_coe_submodule, mem_range, exists_imp_distrib,
      Submodule.exists_lie_submodule_coe_eq_iff]
    split 
    ·
      intro h x y 
      obtain ⟨z, hz⟩ := h x (f y) y rfl 
      use z 
      exact hz.symm
    ·
      intro h x y z hz 
      obtain ⟨w, hw⟩ := h x z 
      use w 
      rw [←hw, hz]

theorem range_subset_ideal_range : (f.range : Set L') ⊆ f.ideal_range :=
  LieSubmodule.subset_lie_span

theorem map_le_ideal_range : I.map f ≤ f.ideal_range :=
  by 
    rw [f.ideal_range_eq_map]
    exact LieIdeal.map_mono le_top

theorem ker_le_comap : f.ker ≤ J.comap f :=
  LieIdeal.comap_mono bot_le

@[simp]
theorem ker_coe_submodule : (ker f : Submodule R L) = (f : L →ₗ[R] L').ker :=
  rfl

@[simp]
theorem mem_ker {x : L} : x ∈ ker f ↔ f x = 0 :=
  show x ∈ (f.ker : Submodule R L) ↔ _ by 
    simp only [ker_coe_submodule, LinearMap.mem_ker, coe_to_linear_map]

theorem mem_ideal_range {x : L} : f x ∈ ideal_range f :=
  by 
    rw [ideal_range_eq_map]
    exact LieIdeal.mem_map (LieSubmodule.mem_top x)

@[simp]
theorem mem_ideal_range_iff (h : is_ideal_morphism f) {y : L'} : y ∈ ideal_range f ↔ ∃ x : L, f x = y :=
  by 
    rw [f.is_ideal_morphism_def] at h 
    rw [←LieSubmodule.mem_coe, ←LieIdeal.coe_to_subalgebra, h, f.range_coe, Set.mem_range]

theorem le_ker_iff : I ≤ f.ker ↔ ∀ x, x ∈ I → f x = 0 :=
  by 
    split  <;> intro h x hx
    ·
      specialize h hx 
      rw [mem_ker] at h 
      exact h
    ·
      rw [mem_ker]
      apply h x hx

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f :=
  by 
    rw [←LieSubmodule.coe_to_submodule_eq_iff, ker_coe_submodule, LieSubmodule.bot_coe_submodule, LinearMap.ker_eq_bot,
      coe_to_linear_map]

@[simp]
theorem range_coe_submodule : (f.range : Submodule R L') = (f : L →ₗ[R] L').range :=
  rfl

theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f :=
  by 
    rw [←LieSubalgebra.coe_to_submodule_eq_iff, range_coe_submodule, LieSubalgebra.top_coe_submodule]
    exact LinearMap.range_eq_top

@[simp]
theorem ideal_range_eq_top_of_surjective (h : Function.Surjective f) : f.ideal_range = ⊤ :=
  by 
    rw [←f.range_eq_top] at h 
    rw [ideal_range_eq_lie_span_range, h, ←LieSubalgebra.coe_to_submodule, ←LieSubmodule.coe_to_submodule_eq_iff,
      LieSubmodule.top_coe_submodule, LieSubalgebra.top_coe_submodule, LieSubmodule.coe_lie_span_submodule_eq_iff]
    use ⊤
    exact LieSubmodule.top_coe_submodule

theorem is_ideal_morphism_of_surjective (h : Function.Surjective f) : f.is_ideal_morphism :=
  by 
    rw [is_ideal_morphism_def, f.ideal_range_eq_top_of_surjective h, f.range_eq_top.mpr h,
      LieIdeal.top_coe_lie_subalgebra]

end LieHom

namespace LieIdeal

variable {f : L →ₗ⁅R⁆ L'} {I : LieIdeal R L} {J : LieIdeal R L'}

@[simp]
theorem map_eq_bot_iff : I.map f = ⊥ ↔ I ≤ f.ker :=
  by 
    rw [←le_bot_iff]
    exact LieIdeal.map_le_iff_le_comap

-- error in Algebra.Lie.Submodule: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coe_map_of_surjective
(h : function.surjective f) : «expr = »((I.map f : submodule R L'), (I : submodule R L).map (f : «expr →ₗ[ ] »(L, R, L'))) :=
begin
  let [ident J] [":", expr lie_ideal R L'] [":=", expr { lie_mem := λ x y hy, begin
       have [ident hy'] [":", expr «expr∃ , »((x : L), «expr ∧ »(«expr ∈ »(x, I), «expr = »(f x, y)))] [],
       { simpa [] [] [] ["[", expr hy, "]"] [] [] },
       obtain ["⟨", ident z₂, ",", ident hz₂, ",", ident rfl, "⟩", ":=", expr hy'],
       obtain ["⟨", ident z₁, ",", ident rfl, "⟩", ":=", expr h x],
       simp [] [] ["only"] ["[", expr lie_hom.coe_to_linear_map, ",", expr set_like.mem_coe, ",", expr set.mem_image, ",", expr lie_submodule.mem_coe_submodule, ",", expr submodule.mem_carrier, ",", expr submodule.map_coe, "]"] [] [],
       use [expr «expr⁅ , ⁆»(z₁, z₂)],
       exact [expr ⟨I.lie_mem hz₂, f.map_lie z₁ z₂⟩]
     end,
     ..(I : submodule R L).map (f : «expr →ₗ[ ] »(L, R, L')) }],
  erw [expr lie_submodule.coe_lie_span_submodule_eq_iff] [],
  use [expr J],
  apply [expr lie_submodule.coe_to_submodule_mk]
end

theorem mem_map_of_surjective {y : L'} (h₁ : Function.Surjective f) (h₂ : y ∈ I.map f) : ∃ x : I, f x = y :=
  by 
    rw [←LieSubmodule.mem_coe_submodule, coe_map_of_surjective h₁, Submodule.mem_map] at h₂ 
    obtain ⟨x, hx, rfl⟩ := h₂ 
    use ⟨x, hx⟩
    rfl

theorem bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥) : I = ⊥ :=
  by 
    rw [←f.ker_eq_bot] at h₁ 
    change comap f ⊥ = ⊥ at h₁ 
    rw [eq_bot_iff, map_le_iff_le_comap, h₁] at h₂ 
    rw [eq_bot_iff]
    exact h₂

/-- Given two nested Lie ideals `I₁ ⊆ I₂`, the inclusion `I₁ ↪ I₂` is a morphism of Lie algebras. -/
def hom_of_le {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) : I₁ →ₗ⁅R⁆ I₂ :=
  { Submodule.ofLe (show I₁.to_submodule ≤ I₂.to_submodule from h) with map_lie' := fun x y => rfl }

@[simp]
theorem coe_hom_of_le {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) : (hom_of_le h x : L) = x :=
  rfl

theorem hom_of_le_apply {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) : hom_of_le h x = ⟨x.1, h x.2⟩ :=
  rfl

theorem hom_of_le_injective {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) : Function.Injective (hom_of_le h) :=
  fun x y =>
    by 
      simp only [hom_of_le_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe, Subtype.val_eq_coe]

@[simp]
theorem map_sup_ker_eq_map : LieIdeal.map f (I⊔f.ker) = LieIdeal.map f I :=
  by 
    suffices  : LieIdeal.map f (I⊔f.ker) ≤ LieIdeal.map f I
    ·
      exact le_antisymmₓ this (LieIdeal.map_mono le_sup_left)
    apply LieSubmodule.lie_span_mono 
    rintro x ⟨y, hy₁, hy₂⟩
    rw [←hy₂]
    erw [LieSubmodule.mem_sup] at hy₁ 
    obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁ 
    rw [←hy]
    rw [f.coe_to_linear_map, f.map_add, f.mem_ker.mp hz₂, add_zeroₓ]
    exact ⟨z₁, hz₁, rfl⟩

@[simp]
theorem map_comap_eq (h : f.is_ideal_morphism) : map f (comap f J) = f.ideal_range⊓J :=
  by 
    apply le_antisymmₓ
    ·
      rw [le_inf_iff]
      exact ⟨f.map_le_ideal_range _, map_comap_le⟩
    ·
      rw [f.is_ideal_morphism_def] at h 
      rw [←SetLike.coe_subset_coe, LieSubmodule.inf_coe, ←coe_to_subalgebra, h]
      rintro y ⟨⟨x, h₁⟩, h₂⟩
      rw [←h₁] at h₂⊢
      exact mem_map h₂

@[simp]
theorem comap_map_eq (h : «expr↑ » (map f I) = f '' I) : comap f (map f I) = I⊔f.ker :=
  by 
    rw [←LieSubmodule.coe_to_submodule_eq_iff, comap_coe_submodule, I.map_coe_submodule f h,
      LieSubmodule.sup_coe_to_submodule, f.ker_coe_submodule, Submodule.comap_map_eq]

variable (f I J)

/-- Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space is a morphism
of Lie algebras. -/
def incl : I →ₗ⁅R⁆ L :=
  (I : LieSubalgebra R L).incl

@[simp]
theorem incl_range : I.incl.range = I :=
  (I : LieSubalgebra R L).incl_range

@[simp]
theorem incl_apply (x : I) : I.incl x = x :=
  rfl

@[simp]
theorem incl_coe : (I.incl : I →ₗ[R] L) = (I : Submodule R L).Subtype :=
  rfl

@[simp]
theorem comap_incl_self : comap I.incl I = ⊤ :=
  by 
    rw [←LieSubmodule.coe_to_submodule_eq_iff]
    exact Submodule.comap_subtype_self _

@[simp]
theorem ker_incl : I.incl.ker = ⊥ :=
  by 
    rw [←LieSubmodule.coe_to_submodule_eq_iff, I.incl.ker_coe_submodule, LieSubmodule.bot_coe_submodule, incl_coe,
      Submodule.ker_subtype]

@[simp]
theorem incl_ideal_range : I.incl.ideal_range = I :=
  by 
    rw [LieHom.ideal_range_eq_lie_span_range, ←LieSubalgebra.coe_to_submodule, ←LieSubmodule.coe_to_submodule_eq_iff,
      incl_range, coe_to_lie_subalgebra_to_submodule, LieSubmodule.coe_lie_span_submodule_eq_iff]
    use I

theorem incl_is_ideal_morphism : I.incl.is_ideal_morphism :=
  by 
    rw [I.incl.is_ideal_morphism_def, incl_ideal_range]
    exact (I : LieSubalgebra R L).incl_range.symm

end LieIdeal

end LieSubmoduleMapAndComap

namespace LieModuleHom

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroupₓ N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (f : M →ₗ⁅R,L⁆ N)

/-- The range of a morphism of Lie modules `f : M → N` is a Lie submodule of `N`.
See Note [range copy pattern]. -/
def range : LieSubmodule R L N :=
  (LieSubmodule.map f ⊤).copy (Set.Range f) Set.image_univ.symm

@[simp]
theorem coe_range : (f.range : Set N) = Set.Range f :=
  rfl

@[simp]
theorem coe_submodule_range : (f.range : Submodule R N) = (f : M →ₗ[R] N).range :=
  rfl

@[simp]
theorem mem_range (n : N) : n ∈ f.range ↔ ∃ m, f m = n :=
  Iff.rfl

theorem map_top : LieSubmodule.map f ⊤ = f.range :=
  by 
    ext 
    simp [LieSubmodule.mem_map]

end LieModuleHom

section TopEquivSelf

variable {R : Type u} {L : Type v}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L]

/-- The natural equivalence between the 'top' Lie subalgebra and the enclosing Lie algebra. -/
def LieSubalgebra.topEquivSelf : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L :=
  { (⊤ : LieSubalgebra R L).incl with invFun := fun x => ⟨x, Set.mem_univ x⟩,
    left_inv :=
      fun x =>
        by 
          ext 
          rfl,
    right_inv := fun x => rfl }

@[simp]
theorem LieSubalgebra.top_equiv_self_apply (x : (⊤ : LieSubalgebra R L)) : LieSubalgebra.topEquivSelf x = x :=
  rfl

/-- The natural equivalence between the 'top' Lie ideal and the enclosing Lie algebra. -/
def LieIdeal.topEquivSelf : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L :=
  LieSubalgebra.topEquivSelf

@[simp]
theorem LieIdeal.top_equiv_self_apply (x : (⊤ : LieIdeal R L)) : LieIdeal.topEquivSelf x = x :=
  rfl

end TopEquivSelf

