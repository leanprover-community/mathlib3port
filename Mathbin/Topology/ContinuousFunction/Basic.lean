import Mathbin.Data.Set.UnionLift 
import Mathbin.Topology.SubsetProperties 
import Mathbin.Topology.Tactic 
import Mathbin.Topology.Algebra.Ordered.ProjIcc

/-!
# Continuous bundled map

In this file we define the type `continuous_map` of continuous bundled maps.
-/


/-- Bundled continuous maps. -/
@[protectProj]
structure ContinuousMap(α : Type _)(β : Type _)[TopologicalSpace α][TopologicalSpace β] where 
  toFun : α → β 
  continuous_to_fun : Continuous to_fun :=  by 
  runTac 
    tactic.interactive.continuity'

notation "C(" α ", " β ")" => ContinuousMap α β

namespace ContinuousMap

attribute [continuity] ContinuousMap.continuous_to_fun

variable{α : Type _}{β : Type _}{γ : Type _}

variable[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ]

instance  : CoeFun C(α, β) fun _ => α → β :=
  ⟨ContinuousMap.toFun⟩

@[simp]
theorem to_fun_eq_coe {f : C(α, β)} : f.to_fun = (f : α → β) :=
  rfl

variable{α β}{f g : ContinuousMap α β}

@[continuity]
protected theorem Continuous (f : C(α, β)) : Continuous f :=
  f.continuous_to_fun

@[continuity]
theorem continuous_set_coe (s : Set C(α, β)) (f : s) : Continuous f :=
  by 
    cases f 
    rw [@coe_fn_coe_base']
    continuity

protected theorem ContinuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  f.continuous.continuous_at

protected theorem ContinuousWithinAt (f : C(α, β)) (s : Set α) (x : α) : ContinuousWithinAt f s x :=
  f.continuous.continuous_within_at

protected theorem congr_funₓ {f g : C(α, β)} (H : f = g) (x : α) : f x = g x :=
  H ▸ rfl

protected theorem congr_argₓ (f : C(α, β)) {x y : α} (h : x = y) : f x = f y :=
  h ▸ rfl

@[ext]
theorem ext (H : ∀ x, f x = g x) : f = g :=
  by 
    cases f <;> cases g <;> congr <;> exact funext H

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  ⟨ContinuousMap.congr_fun, ext⟩

instance  [Inhabited β] : Inhabited C(α, β) :=
  ⟨{ toFun := fun _ => default _ }⟩

theorem coe_inj ⦃f g : C(α, β)⦄ (h : (f : α → β) = g) : f = g :=
  by 
    cases f <;> cases g <;> cases h <;> rfl

@[simp]
theorem coe_mk (f : α → β) (h : Continuous f) : «expr⇑ » (⟨f, h⟩ : ContinuousMap α β) = f :=
  rfl

section 

variable(α β)

/--
The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
def equiv_fn_of_discrete [DiscreteTopology α] : C(α, β) ≃ (α → β) :=
  ⟨fun f => f, fun f => ⟨f, continuous_of_discrete_topology⟩,
    fun f =>
      by 
        ext 
        rfl,
    fun f =>
      by 
        ext 
        rfl⟩

end 

/-- The identity as a continuous map. -/
def id : C(α, α) :=
  ⟨id⟩

@[simp]
theorem id_coe : (id : α → α) = _root_.id :=
  rfl

theorem id_apply (a : α) : id a = a :=
  rfl

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) :=
  ⟨f ∘ g⟩

@[simp]
theorem comp_coe (f : C(β, γ)) (g : C(α, β)) : (comp f g : α → γ) = (f ∘ g) :=
  rfl

theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl

/-- Constant map as a continuous map -/
def const (b : β) : C(α, β) :=
  ⟨fun x => b⟩

@[simp]
theorem const_coe (b : β) : (const b : α → β) = fun x => b :=
  rfl

theorem const_apply (b : β) (a : α) : const b a = b :=
  rfl

instance  [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  { exists_pair_ne :=
      by 
        obtain ⟨b₁, b₂, hb⟩ := exists_pair_ne β 
        refine' ⟨const b₁, const b₂, _⟩
        contrapose! hb 
        inhabit α 
        change const b₁ (default α) = const b₂ (default α)
        simp [hb] }

section 

variable[LinearOrderedAddCommGroup β][OrderTopology β]

/-- The pointwise absolute value of a continuous function as a continuous function. -/
def abs (f : C(α, β)) : C(α, β) :=
  { toFun := fun x => |f x| }

instance (priority := 100) : HasAbs C(α, β) :=
  ⟨fun f => abs f⟩

@[simp]
theorem abs_apply (f : C(α, β)) (x : α) : |f| x = |f x| :=
  rfl

end 

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/


section Lattice

instance PartialOrderₓ [PartialOrderₓ β] : PartialOrderₓ C(α, β) :=
  PartialOrderₓ.lift (fun f => f.to_fun)
    (by 
      tidy)

theorem le_def [PartialOrderₓ β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def

theorem lt_def [PartialOrderₓ β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def

instance HasSup [LinearOrderₓ β] [OrderClosedTopology β] : HasSup C(α, β) :=
  { sup := fun f g => { toFun := fun a => max (f a) (g a) } }

@[simp, normCast]
theorem sup_coe [LinearOrderₓ β] [OrderClosedTopology β] (f g : C(α, β)) : ((f⊔g : C(α, β)) : α → β) = (f⊔g : α → β) :=
  rfl

@[simp]
theorem sup_apply [LinearOrderₓ β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) : (f⊔g) a = max (f a) (g a) :=
  rfl

instance  [LinearOrderₓ β] [OrderClosedTopology β] : SemilatticeSup C(α, β) :=
  { ContinuousMap.partialOrder, ContinuousMap.hasSup with
    le_sup_left :=
      fun f g =>
        le_def.mpr
          (by 
            simp [le_reflₓ]),
    le_sup_right :=
      fun f g =>
        le_def.mpr
          (by 
            simp [le_reflₓ]),
    sup_le :=
      fun f₁ f₂ g w₁ w₂ =>
        le_def.mpr
          fun a =>
            by 
              simp [le_def.mp w₁ a, le_def.mp w₂ a] }

instance HasInf [LinearOrderₓ β] [OrderClosedTopology β] : HasInf C(α, β) :=
  { inf := fun f g => { toFun := fun a => min (f a) (g a) } }

@[simp, normCast]
theorem inf_coe [LinearOrderₓ β] [OrderClosedTopology β] (f g : C(α, β)) : ((f⊓g : C(α, β)) : α → β) = (f⊓g : α → β) :=
  rfl

@[simp]
theorem inf_apply [LinearOrderₓ β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) : (f⊓g) a = min (f a) (g a) :=
  rfl

instance  [LinearOrderₓ β] [OrderClosedTopology β] : SemilatticeInf C(α, β) :=
  { ContinuousMap.partialOrder, ContinuousMap.hasInf with
    inf_le_left :=
      fun f g =>
        le_def.mpr
          (by 
            simp [le_reflₓ]),
    inf_le_right :=
      fun f g =>
        le_def.mpr
          (by 
            simp [le_reflₓ]),
    le_inf :=
      fun f₁ f₂ g w₁ w₂ =>
        le_def.mpr
          fun a =>
            by 
              simp [le_def.mp w₁ a, le_def.mp w₂ a] }

instance  [LinearOrderₓ β] [OrderClosedTopology β] : Lattice C(α, β) :=
  { ContinuousMap.semilatticeInf, ContinuousMap.semilatticeSup with  }

section Sup'

variable[LinearOrderₓ γ][OrderClosedTopology γ]

-- error in Topology.ContinuousFunction.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem sup'_apply
{ι : Type*}
{s : finset ι}
(H : s.nonempty)
(f : ι → «exprC( , )»(β, γ))
(b : β) : «expr = »(s.sup' H f b, s.sup' H (λ a, f a b)) :=
finset.comp_sup'_eq_sup'_comp H (λ f : «exprC( , )»(β, γ), f b) (λ i j, rfl)

@[simp, normCast]
theorem sup'_coe {ι : Type _} {s : Finset ι} (H : s.nonempty) (f : ι → C(β, γ)) :
  ((s.sup' H f : C(β, γ)) : ι → β) = s.sup' H fun a => (f a : β → γ) :=
  by 
    ext 
    simp [sup'_apply]

end Sup'

section Inf'

variable[LinearOrderₓ γ][OrderClosedTopology γ]

theorem inf'_apply {ι : Type _} {s : Finset ι} (H : s.nonempty) (f : ι → C(β, γ)) (b : β) :
  s.inf' H f b = s.inf' H fun a => f a b :=
  @sup'_apply _ (OrderDual γ) _ _ _ _ _ _ H f b

@[simp, normCast]
theorem inf'_coe {ι : Type _} {s : Finset ι} (H : s.nonempty) (f : ι → C(β, γ)) :
  ((s.inf' H f : C(β, γ)) : ι → β) = s.inf' H fun a => (f a : β → γ) :=
  @sup'_coe _ (OrderDual γ) _ _ _ _ _ _ H f

end Inf'

end Lattice

section Restrict

variable(s : Set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) :=
  ⟨f ∘ coeₓ⟩

@[simp]
theorem coe_restrict (f : C(α, β)) : «expr⇑ » (f.restrict s) = (f ∘ coeₓ) :=
  rfl

end Restrict

section Extend

variable[LinearOrderₓ α][OrderTopology α]{a b : α}(h : a ≤ b)

/--
Extend a continuous function `f : C(set.Icc a b, β)` to a function `f : C(α, β)`.
-/
def Icc_extend (f : C(Set.Icc a b, β)) : C(α, β) :=
  ⟨Set.iccExtend h f⟩

@[simp]
theorem coe_Icc_extend (f : C(Set.Icc a b, β)) : ((Icc_extend h f : C(α, β)) : α → β) = Set.iccExtend h f :=
  rfl

end Extend

section Gluing

variable{ι :
    Type
      _}(S :
    ι →
      Set
        α)(φ :
    ∀ (i : ι),
      C(S i,
        β))(hφ :
    ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)(hS : ∀ (x : α), ∃ i, S i ∈ nhds x)

include hφ hS

-- error in Topology.ContinuousFunction.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/ noncomputable def lift_cover : «exprC( , )»(α, β) :=
begin
  have [ident H] [":", expr «expr = »(«expr⋃ , »((i), S i), set.univ)] [],
  { rw [expr set.eq_univ_iff_forall] [],
    intros [ident x],
    rw [expr set.mem_Union] [],
    obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr hS x],
    exact [expr ⟨i, mem_of_mem_nhds hi⟩] },
  refine [expr ⟨set.lift_cover S (λ i, φ i) hφ H, continuous_subtype_nhds_cover hS _⟩],
  intros [ident i],
  convert [] [expr (φ i).continuous] [],
  ext [] [ident x] [],
  exact [expr set.lift_cover_coe x]
end

variable{S φ hφ hS}

@[simp]
theorem lift_cover_coe {i : ι} (x : S i) : lift_cover S φ hφ hS x = φ i x :=
  Set.lift_cover_coe _

@[simp]
theorem lift_cover_restrict {i : ι} : (lift_cover S φ hφ hS).restrict (S i) = φ i :=
  ext$ lift_cover_coe

omit hφ hS

variable(A :
    Set
      (Set
        α))(F :
    ∀ (s : Set α) (hi : s ∈ A),
      C(s,
        β))(hF :
    ∀ s (hs : s ∈ A) t (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
      F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)(hA : ∀ (x : α), ∃ (i : _)(_ : i ∈ A), i ∈ nhds x)

include hF hA

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def lift_cover' : C(α, β) :=
  by 
    let S : A → Set α := coeₓ 
    let F : ∀ (i : A), C(i, β) := fun i => F i i.prop 
    refine' lift_cover S F (fun i j => hF i i.prop j j.prop) _ 
    intro x 
    obtain ⟨s, hs, hsx⟩ := hA x 
    exact ⟨⟨s, hs⟩, hsx⟩

variable{A F hF hA}

@[simp]
theorem lift_cover_coe' {s : Set α} {hs : s ∈ A} (x : s) : lift_cover' A F hF hA x = F s hs x :=
  let x' : (coeₓ : A → Set α) ⟨s, hs⟩ := x 
  lift_cover_coe x'

@[simp]
theorem lift_cover_restrict' {s : Set α} {hs : s ∈ A} : (lift_cover' A F hF hA).restrict s = F s hs :=
  ext$ lift_cover_coe'

end Gluing

end ContinuousMap

/--
The forward direction of a homeomorphism, as a bundled continuous map.
-/
@[simps]
def Homeomorph.toContinuousMap {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) : C(α, β) :=
  ⟨e⟩

