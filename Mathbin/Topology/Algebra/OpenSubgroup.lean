import Mathbin.Topology.Opens 
import Mathbin.Topology.Algebra.Ring

/-!
# Open subgroups of a topological groups

This files builds the lattice `open_subgroup G` of open subgroups in a topological group `G`,
and its additive version `open_add_subgroup`.  This lattice has a top element, the subgroup of all
elements, but no bottom element in general. The trivial subgroup which is the natural candidate
bottom has no reason to be open (this happens only in discrete groups).

Note that this notion is especially relevant in a non-archimedean context, for instance for
`p`-adic groups.

## Main declarations

* `open_subgroup.is_closed`: An open subgroup is automatically closed.
* `subgroup.is_open_mono`: A subgroup containing an open subgroup is open.
                           There are also versions for additive groups, submodules and ideals.
* `open_subgroup.comap`: Open subgroups can be pulled back by a continuous group morphism.

## TODO
* Prove that the identity component of a locally path connected group is an open subgroup.
  Up to now this file is really geared towards non-archimedean algebra, not Lie groups.
-/


open TopologicalSpace

open_locale TopologicalSpace

/-- The type of open subgroups of a topological additive group. -/
@[ancestor AddSubgroup]
structure OpenAddSubgroup(G : Type _)[AddGroupₓ G][TopologicalSpace G] extends AddSubgroup G where 
  is_open' : IsOpen carrier

/-- The type of open subgroups of a topological group. -/
@[ancestor Subgroup, toAdditive]
structure OpenSubgroup(G : Type _)[Groupₓ G][TopologicalSpace G] extends Subgroup G where 
  is_open' : IsOpen carrier

/-- Reinterpret an `open_subgroup` as a `subgroup`. -/
add_decl_doc OpenSubgroup.toSubgroup

/-- Reinterpret an `open_add_subgroup` as an `add_subgroup`. -/
add_decl_doc OpenAddSubgroup.toAddSubgroup

namespace OpenAddSubgroup

end OpenAddSubgroup

namespace OpenSubgroup

open Function TopologicalSpace

variable{G : Type _}[Groupₓ G][TopologicalSpace G]

variable{U V : OpenSubgroup G}{g : G}

@[toAdditive]
instance has_coe_set : CoeTₓ (OpenSubgroup G) (Set G) :=
  ⟨fun U => U.1⟩

@[toAdditive]
instance  : HasMem G (OpenSubgroup G) :=
  ⟨fun g U => g ∈ (U : Set G)⟩

@[toAdditive]
instance has_coe_subgroup : CoeTₓ (OpenSubgroup G) (Subgroup G) :=
  ⟨to_subgroup⟩

@[toAdditive]
instance has_coe_opens : CoeTₓ (OpenSubgroup G) (opens G) :=
  ⟨fun U => ⟨U, U.is_open'⟩⟩

@[simp, normCast, toAdditive]
theorem mem_coe : g ∈ (U : Set G) ↔ g ∈ U :=
  Iff.rfl

@[simp, normCast, toAdditive]
theorem mem_coe_opens : g ∈ (U : opens G) ↔ g ∈ U :=
  Iff.rfl

@[simp, normCast, toAdditive]
theorem mem_coe_subgroup : g ∈ (U : Subgroup G) ↔ g ∈ U :=
  Iff.rfl

@[toAdditive]
theorem coe_injective : injective (coeₓ : OpenSubgroup G → Set G) :=
  by 
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨h⟩
    congr

@[ext, toAdditive]
theorem ext (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  coe_injective$ Set.ext h

@[toAdditive]
theorem ext_iff : U = V ↔ ∀ x, x ∈ U ↔ x ∈ V :=
  ⟨fun h x => h ▸ Iff.rfl, ext⟩

variable(U)

@[toAdditive]
protected theorem IsOpen : IsOpen (U : Set G) :=
  U.is_open'

@[toAdditive]
protected theorem one_mem : (1 : G) ∈ U :=
  U.one_mem'

@[toAdditive]
protected theorem inv_mem {g : G} (h : g ∈ U) : g⁻¹ ∈ U :=
  U.inv_mem' h

@[toAdditive]
protected theorem mul_mem {g₁ g₂ : G} (h₁ : g₁ ∈ U) (h₂ : g₂ ∈ U) : (g₁*g₂) ∈ U :=
  U.mul_mem' h₁ h₂

@[toAdditive]
theorem mem_nhds_one : (U : Set G) ∈ 𝓝 (1 : G) :=
  IsOpen.mem_nhds U.is_open U.one_mem

variable{U}

@[toAdditive]
instance  : HasTop (OpenSubgroup G) :=
  ⟨{ (⊤ : Subgroup G) with is_open' := is_open_univ }⟩

@[toAdditive]
instance  : Inhabited (OpenSubgroup G) :=
  ⟨⊤⟩

@[toAdditive]
theorem IsClosed [HasContinuousMul G] (U : OpenSubgroup G) : IsClosed (U : Set G) :=
  by 
    apply is_open_compl_iff.1
    refine' is_open_iff_forall_mem_open.2 fun x hx => ⟨(fun y => y*x⁻¹) ⁻¹' U, _, _, _⟩
    ·
      intro u hux 
      simp only [Set.mem_preimage, Set.mem_compl_iff, mem_coe] at hux hx⊢
      refine' mt (fun hu => _) hx 
      convert U.mul_mem (U.inv_mem hux) hu 
      simp 
    ·
      exact U.is_open.preimage (continuous_mul_right _)
    ·
      simp [U.one_mem]

section 

variable{H : Type _}[Groupₓ H][TopologicalSpace H]

/-- The product of two open subgroups as an open subgroup of the product group. -/
@[toAdditive "The product of two open subgroups as an open subgroup of the product group."]
def Prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  { (U : Subgroup G).Prod (V : Subgroup H) with Carrier := (U : Set G).Prod (V : Set H),
    is_open' := U.is_open.prod V.is_open }

end 

@[toAdditive]
instance  : PartialOrderₓ (OpenSubgroup G) :=
  { PartialOrderₓ.lift (coeₓ : OpenSubgroup G → Set G) coe_injective with le := fun U V => ∀ ⦃x⦄, x ∈ U → x ∈ V }

@[toAdditive]
instance  : SemilatticeInf (OpenSubgroup G) :=
  { OpenSubgroup.partialOrder with
    inf := fun U V => { (U : Subgroup G)⊓V with is_open' := IsOpen.inter U.is_open V.is_open },
    inf_le_left := fun U V => Set.inter_subset_left _ _, inf_le_right := fun U V => Set.inter_subset_right _ _,
    le_inf := fun U V W hV hW => Set.subset_inter hV hW }

@[toAdditive]
instance  : OrderTop (OpenSubgroup G) :=
  { top := ⊤, le_top := fun U => Set.subset_univ _ }

@[simp, normCast, toAdditive]
theorem coe_inf : («expr↑ » (U⊓V) : Set G) = (U : Set G) ∩ V :=
  rfl

@[simp, normCast, toAdditive]
theorem coe_subset : (U : Set G) ⊆ V ↔ U ≤ V :=
  Iff.rfl

@[simp, normCast, toAdditive]
theorem coe_subgroup_le : (U : Subgroup G) ≤ (V : Subgroup G) ↔ U ≤ V :=
  Iff.rfl

variable{N : Type _}[Groupₓ N][TopologicalSpace N]

/-- The preimage of an `open_subgroup` along a continuous `monoid` homomorphism
  is an `open_subgroup`. -/
@[toAdditive
      "The preimage of an `open_add_subgroup` along a continuous `add_monoid` homomorphism\nis an `open_add_subgroup`."]
def comap (f : G →* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgroup G :=
  { (H : Subgroup N).comap f with is_open' := H.is_open.preimage hf }

@[simp, toAdditive]
theorem coe_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) : (H.comap f hf : Set G) = f ⁻¹' H :=
  rfl

@[simp, toAdditive]
theorem mem_comap {H : OpenSubgroup N} {f : G →* N} {hf : Continuous f} {x : G} : x ∈ H.comap f hf ↔ f x ∈ H :=
  Iff.rfl

@[toAdditive]
theorem comap_comap {P : Type _} [Groupₓ P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N →* P)
  (hf₂ : Continuous f₂) (f₁ : G →* N) (hf₁ : Continuous f₁) :
  (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
  rfl

end OpenSubgroup

namespace Subgroup

variable{G : Type _}[Groupₓ G][TopologicalSpace G][HasContinuousMul G](H : Subgroup G)

-- error in Topology.Algebra.OpenSubgroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]] theorem is_open_of_mem_nhds {g : G} (hg : «expr ∈ »((H : set G), expr𝓝() g)) : is_open (H : set G) :=
begin
  simp [] [] ["only"] ["[", expr is_open_iff_mem_nhds, ",", expr set_like.mem_coe, "]"] [] ["at", ident hg, "⊢"],
  intros [ident x, ident hx],
  have [] [":", expr filter.tendsto (λ
    y, «expr * »(y, «expr * »(«expr ⁻¹»(x), g))) (expr𝓝() x) «expr $ »(expr𝓝(), «expr * »(x, «expr * »(«expr ⁻¹»(x), g)))] [":=", expr (continuous_id.mul continuous_const).tendsto _],
  rw ["[", expr mul_inv_cancel_left, "]"] ["at", ident this],
  have [] [] [":=", expr filter.mem_map'.1 (this hg)],
  replace [ident hg] [":", expr «expr ∈ »(g, H)] [":=", expr set_like.mem_coe.1 (mem_of_mem_nhds hg)],
  simp [] [] ["only"] ["[", expr set_like.mem_coe, ",", expr H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg), "]"] [] ["at", ident this],
  exact [expr this]
end

@[toAdditive]
theorem is_open_of_open_subgroup {U : OpenSubgroup G} (h : U.1 ≤ H) : IsOpen (H : Set G) :=
  H.is_open_of_mem_nhds (Filter.mem_of_superset U.mem_nhds_one h)

@[toAdditive]
theorem is_open_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (h₁ : IsOpen (H₁ : Set G)) : IsOpen (H₂ : Set G) :=
  @is_open_of_open_subgroup _ _ _ _ H₂ { H₁ with is_open' := h₁ } h

end Subgroup

namespace OpenSubgroup

variable{G : Type _}[Groupₓ G][TopologicalSpace G][HasContinuousMul G]

@[toAdditive]
instance  : SemilatticeSup (OpenSubgroup G) :=
  { OpenSubgroup.semilatticeInf with
    sup :=
      fun U V =>
        { (U : Subgroup G)⊔V with
          is_open' :=
            show IsOpen (((U : Subgroup G)⊔V : Subgroup G) : Set G) from Subgroup.is_open_mono le_sup_left U.is_open },
    le_sup_left := fun U V => coe_subgroup_le.1 le_sup_left, le_sup_right := fun U V => coe_subgroup_le.1 le_sup_right,
    sup_le := fun U V W hU hV => coe_subgroup_le.1 (sup_le hU hV) }

@[toAdditive]
instance  : Lattice (OpenSubgroup G) :=
  { OpenSubgroup.semilatticeSup, OpenSubgroup.semilatticeInf with  }

end OpenSubgroup

namespace Submodule

open OpenAddSubgroup

variable{R : Type _}{M : Type _}[CommRingₓ R]

variable[AddCommGroupₓ M][TopologicalSpace M][TopologicalAddGroup M][Module R M]

theorem is_open_mono {U P : Submodule R M} (h : U ≤ P) (hU : IsOpen (U : Set M)) : IsOpen (P : Set M) :=
  @AddSubgroup.is_open_mono M _ _ _ U.to_add_subgroup P.to_add_subgroup h hU

end Submodule

namespace Ideal

variable{R : Type _}[CommRingₓ R]

variable[TopologicalSpace R][TopologicalRing R]

theorem is_open_of_open_subideal {U I : Ideal R} (h : U ≤ I) (hU : IsOpen (U : Set R)) : IsOpen (I : Set R) :=
  Submodule.is_open_mono h hU

end Ideal

