import Mathbin.Tactic.Tidy 
import Mathbin.Topology.ContinuousFunction.Basic 
import Mathbin.Topology.Homeomorph 
import Mathbin.Topology.SubsetProperties

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `compact_open` is the compact-open topology on `C(α, β)`. It is declared as an instance.
* `ev` is the evaluation map `C(α, β) × α → β`. It is continuous as long as `α` is locally compact.
* `coev` is the coevaluation map `β → C(α, β × α)`. It is always continuous.
* `continuous_map.curry` is the currying map `C(α × β, γ) → C(α, C(β, γ))`. This map always exists
  and it is continuous as long as `α × β` is locally compact.
* `continuous_map.uncurry` is the uncurrying map `C(α, C(β, γ)) → C(α × β, γ)`. For this map to
  exist, we need `β` to be locally compact. If `α` is also locally compact, then this map is
  continuous.
* `homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(α × β, γ) ≃ₜ C(α, C(β, γ))`. This homeomorphism exists if `α` and `β` are locally compact.


## Tags

compact-open, curry, function space
-/


open Set

open_locale TopologicalSpace

namespace ContinuousMap

section CompactOpen

variable{α : Type _}{β : Type _}{γ : Type _}

variable[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ]

/-- A generating set for the compact-open topology (when `s` is compact and `u` is open). -/
def compact_open.gen (s : Set α) (u : Set β) : Set C(α, β) :=
  { f | f '' s ⊆ u }

instance compact_open : TopologicalSpace C(α, β) :=
  TopologicalSpace.generateFrom
    { m | ∃ (s : Set α)(hs : IsCompact s)(u : Set β)(hu : IsOpen u), m = compact_open.gen s u }

private theorem is_open_gen {s : Set α} (hs : IsCompact s) {u : Set β} (hu : IsOpen u) :
  IsOpen (compact_open.gen s u) :=
  TopologicalSpace.GenerateOpen.basic _
    (by 
      dsimp [mem_set_of_eq] <;> tauto)

section Functorial

variable(g : C(β, γ))

private theorem preimage_gen {s : Set α} (hs : IsCompact s) {u : Set γ} (hu : IsOpen u) :
  ContinuousMap.comp g ⁻¹' compact_open.gen s u = compact_open.gen s (g ⁻¹' u) :=
  by 
    ext ⟨f, _⟩
    change (g ∘ f) '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u 
    rw [image_comp, image_subset_iff]

/-- C(α, -) is a functor. -/
theorem continuous_comp : Continuous (ContinuousMap.comp g : C(α, β) → C(α, γ)) :=
  continuous_generated_from$
    fun m ⟨s, hs, u, hu, hm⟩ =>
      by 
        rw [hm, preimage_gen g hs hu] <;> exact is_open_gen hs (hu.preimage g.2)

end Functorial

section Ev

variable(α β)

/-- The evaluation map `map C(α, β) × α → β` -/
def ev (p : C(α, β) × α) : β :=
  p.1 p.2

variable{α β}

/-- The evaluation map `C(α, β) × α → β` is continuous if `α` is locally compact. -/
theorem continuous_ev [LocallyCompactSpace α] : Continuous (ev α β) :=
  continuous_iff_continuous_at.mpr$
    fun ⟨f, x⟩ n hn =>
      let ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn 
      have  : v ∈ 𝓝 (f x) := IsOpen.mem_nhds vo fxv 
      let ⟨s, hs, sv, sc⟩ := LocallyCompactSpace.local_compact_nhds x (f ⁻¹' v) (f.continuous.tendsto x this)
      let ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs 
      show ev α β ⁻¹' n ∈ 𝓝 (f, x) from
        let w := Set.Prod (compact_open.gen s v) u 
        have  : w ⊆ ev α β ⁻¹' n :=
          fun ⟨f', x'⟩ ⟨hf', hx'⟩ =>
            calc f' x' ∈ f' '' s := mem_image_of_mem f' (us hx')
              _ ⊆ v := hf' 
              _ ⊆ n := vn 
              
        have  : IsOpen w := (is_open_gen sc vo).Prod uo 
        have  : (f, x) ∈ w := ⟨image_subset_iff.mpr sv, xu⟩
        mem_nhds_iff.mpr
          ⟨w,
            by 
              assumption,
            by 
              assumption,
            by 
              assumption⟩

theorem continuous_ev₁ [LocallyCompactSpace α] (a : α) : Continuous fun f : C(α, β) => f a :=
  continuous_ev.comp (continuous_id.prod_mk continuous_const)

instance  [T2Space β] [LocallyCompactSpace α] : T2Space C(α, β) :=
  ⟨by 
      intro f₁ f₂ h 
      obtain ⟨p, hp⟩ := not_forall.mp (mt ContinuousMap.ext h)
      exact separated_by_continuous (continuous_ev₁ p) hp⟩

end Ev

section InfInduced

theorem compact_open_le_induced (s : Set α) :
  (ContinuousMap.compactOpen : TopologicalSpace C(α, β)) ≤
    TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen :=
  by 
    simp only [induced_generate_from_eq, ContinuousMap.compactOpen]
    apply generate_from_mono 
    rintro b ⟨a, ⟨c, hc, u, hu, rfl⟩, rfl⟩
    refine' ⟨coeₓ '' c, hc.image continuous_subtype_coe, u, hu, _⟩
    ext f 
    simp only [compact_open.gen, mem_set_of_eq, mem_preimage, ContinuousMap.coe_restrict]
    rw [image_comp f (coeₓ : s → α)]

/-- The compact-open topology on `C(α, β)` is equal to the infimum of the compact-open topologies
on `C(s, β)` for `s` a compact subset of `α`.  The key point of the proof is that the union of the
compact subsets of `α` is equal to the union of compact subsets of the compact subsets of `α`. -/
theorem compact_open_eq_Inf_induced :
  (ContinuousMap.compactOpen : TopologicalSpace C(α, β)) =
    ⨅(s : Set α)(hs : IsCompact s), TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen :=
  by 
    refine' le_antisymmₓ _ _
    ·
      refine' le_binfi _ 
      exact fun s hs => compact_open_le_induced s 
    simp only [←generate_from_Union, induced_generate_from_eq, ContinuousMap.compactOpen]
    apply generate_from_mono 
    rintro _ ⟨s, hs, u, hu, rfl⟩
    rw [mem_bUnion_iff']
    refine' ⟨s, hs, _, ⟨univ, is_compact_iff_is_compact_univ.mp hs, u, hu, rfl⟩, _⟩
    ext f 
    simp only [compact_open.gen, mem_set_of_eq, mem_preimage, ContinuousMap.coe_restrict]
    rw [image_comp f (coeₓ : s → α)]
    simp 

/-- For any subset `s` of `α`, the restriction of continuous functions to `s` is continuous as a
function from `C(α, β)` to `C(s, β)` with their respective compact-open topologies. -/
theorem continuous_restrict (s : Set α) : Continuous fun F : C(α, β) => F.restrict s :=
  by 
    rw [continuous_iff_le_induced]
    exact compact_open_le_induced s

theorem nhds_compact_open_eq_Inf_nhds_induced (f : C(α, β)) :
  𝓝 f = ⨅(s : _)(hs : IsCompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s) :=
  by 
    rw [compact_open_eq_Inf_induced]
    simp [nhds_infi, nhds_induced]

theorem tendsto_compact_open_restrict {ι : Type _} {l : Filter ι} {F : ι → C(α, β)} {f : C(α, β)}
  (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set α) : Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  (continuous_restrict s).ContinuousAt.Tendsto.comp hFf

theorem tendsto_compact_open_iff_forall {ι : Type _} {l : Filter ι} (F : ι → C(α, β)) (f : C(α, β)) :
  Filter.Tendsto F l (𝓝 f) ↔ ∀ s hs : IsCompact s, Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  by 
    rw [compact_open_eq_Inf_induced]
    simp [nhds_infi, nhds_induced, Filter.tendsto_comap_iff]

-- error in Topology.CompactOpen: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A family `F` of functions in `C(α, β)` converges in the compact-open topology, if and only if
it converges in the compact-open topology on each compact subset of `α`. -/
theorem exists_tendsto_compact_open_iff_forall
[locally_compact_space α]
[t2_space α]
[t2_space β]
{ι : Type*}
{l : filter ι}
[filter.ne_bot l]
(F : ι → «exprC( , )»(α, β)) : «expr ↔ »(«expr∃ , »((f), filter.tendsto F l (expr𝓝() f)), ∀
 (s : set α)
 (hs : is_compact s), «expr∃ , »((f), filter.tendsto (λ i, (F i).restrict s) l (expr𝓝() f))) :=
begin
  split,
  { rintros ["⟨", ident f, ",", ident hf, "⟩", ident s, ident hs],
    exact [expr ⟨f.restrict s, tendsto_compact_open_restrict hf s⟩] },
  { intros [ident h],
    choose [] [ident f] [ident hf] ["using", expr h],
    have [ident h] [":", expr ∀
     (s₁)
     (hs₁ : is_compact s₁)
     (s₂)
     (hs₂ : is_compact s₂)
     (x : α)
     (hxs₁ : «expr ∈ »(x, s₁))
     (hxs₂ : «expr ∈ »(x, s₂)), «expr = »(f s₁ hs₁ ⟨x, hxs₁⟩, f s₂ hs₂ ⟨x, hxs₂⟩)] [],
    { rintros [ident s₁, ident hs₁, ident s₂, ident hs₂, ident x, ident hxs₁, ident hxs₂],
      haveI [] [] [":=", expr is_compact_iff_compact_space.mp hs₁],
      haveI [] [] [":=", expr is_compact_iff_compact_space.mp hs₂],
      have [ident h₁] [] [":=", expr (continuous_ev₁ (⟨x, hxs₁⟩ : s₁)).continuous_at.tendsto.comp (hf s₁ hs₁)],
      have [ident h₂] [] [":=", expr (continuous_ev₁ (⟨x, hxs₂⟩ : s₂)).continuous_at.tendsto.comp (hf s₂ hs₂)],
      exact [expr tendsto_nhds_unique h₁ h₂] },
    have [ident hs] [":", expr ∀ x : α, «expr∃ , »((s) (hs : is_compact s), «expr ∈ »(s, expr𝓝() x))] [],
    { intros [ident x],
      obtain ["⟨", ident s, ",", ident hs, ",", ident hs', "⟩", ":=", expr exists_compact_mem_nhds x],
      exact [expr ⟨s, hs, hs'⟩] },
    refine [expr ⟨lift_cover' _ _ h hs, _⟩],
    rw [expr tendsto_compact_open_iff_forall] [],
    intros [ident s, ident hs],
    rw [expr lift_cover_restrict'] [],
    exact [expr hf s hs] }
end

end InfInduced

section Coev

variable(α β)

/-- The coevaluation map `β → C(α, β × α)` sending a point `x : β` to the continuous function
on `α` sending `y` to `(x, y)`. -/
def coev (b : β) : C(α, β × α) :=
  ⟨fun a => (b, a), Continuous.prod_mk continuous_const continuous_id⟩

variable{α β}

theorem image_coev {y : β} (s : Set α) : coev α β y '' s = Set.Prod {y} s :=
  by 
    tidy

theorem continuous_coev : Continuous (coev α β) :=
  continuous_generated_from$
    by 
      rintro _ ⟨s, sc, u, uo, rfl⟩
      rw [is_open_iff_forall_mem_open]
      intro y hy 
      change coev α β y '' s ⊆ u at hy 
      rw [image_coev s] at hy 
      rcases generalized_tube_lemma is_compact_singleton sc uo hy with ⟨v, w, vo, wo, yv, sw, vwu⟩
      refine' ⟨v, _, vo, singleton_subset_iff.mp yv⟩
      intro y' hy' 
      change coev α β y' '' s ⊆ u 
      rw [image_coev s]
      exact subset.trans (prod_mono (singleton_subset_iff.mpr hy') sw) vwu

end Coev

section Curry

/-- Auxiliary definition, see `continuous_map.curry` and `homeomorph.curry`. -/
def curry' (f : C(α × β, γ)) (a : α) : C(β, γ) :=
  ⟨Function.curry f a⟩

/-- If a map `α × β → γ` is continuous, then its curried form `α → C(β, γ)` is continuous. -/
theorem continuous_curry' (f : C(α × β, γ)) : Continuous (curry' f) :=
  have hf : curry' f = (ContinuousMap.comp f ∘ coev _ _) :=
    by 
      ext 
      rfl 
  hf ▸ Continuous.comp (continuous_comp f) continuous_coev

/-- To show continuity of a map `α → C(β, γ)`, it suffices to show that its uncurried form
    `α × β → γ` is continuous. -/
theorem continuous_of_continuous_uncurry (f : α → C(β, γ)) (h : Continuous (Function.uncurry fun x y => f x y)) :
  Continuous f :=
  by 
    convert continuous_curry' ⟨_, h⟩
    ext 
    rfl

/-- The curried form of a continuous map `α × β → γ` as a continuous map `α → C(β, γ)`.
    If `a × β` is locally compact, this is continuous. If `α` and `β` are both locally
    compact, then this is a homeomorphism, see `homeomorph.curry`. -/
def curry (f : C(α × β, γ)) : C(α, C(β, γ)) :=
  ⟨_, continuous_curry' f⟩

/-- The currying process is a continuous map between function spaces. -/
theorem continuous_curry [LocallyCompactSpace (α × β)] : Continuous (curry : C(α × β, γ) → C(α, C(β, γ))) :=
  by 
    apply continuous_of_continuous_uncurry 
    apply continuous_of_continuous_uncurry 
    rw [←Homeomorph.comp_continuous_iff' (Homeomorph.prodAssoc _ _ _).symm]
    convert continuous_ev <;> tidy

@[simp]
theorem curry_apply (f : C(α × β, γ)) (a : α) (b : β) : f.curry a b = f (a, b) :=
  rfl

/-- The uncurried form of a continuous map `α → C(β, γ)` is a continuous map `α × β → γ`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace β] (f : C(α, C(β, γ))) :
  Continuous (Function.uncurry fun x y => f x y) :=
  have hf : (Function.uncurry fun x y => f x y) = (ev β γ ∘ Prod.mapₓ f id) :=
    by 
      ext 
      rfl 
  hf ▸ Continuous.comp continuous_ev$ Continuous.prod_map f.2 id.2

/-- The uncurried form of a continuous map `α → C(β, γ)` as a continuous map `α × β → γ` (if `β` is
    locally compact). If `α` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `homeomorph.curry`. -/
def uncurry [LocallyCompactSpace β] (f : C(α, C(β, γ))) : C(α × β, γ) :=
  ⟨_, continuous_uncurry_of_continuous f⟩

/-- The uncurrying process is a continuous map between function spaces. -/
theorem continuous_uncurry [LocallyCompactSpace α] [LocallyCompactSpace β] :
  Continuous (uncurry : C(α, C(β, γ)) → C(α × β, γ)) :=
  by 
    apply continuous_of_continuous_uncurry 
    rw [←Homeomorph.comp_continuous_iff' (Homeomorph.prodAssoc _ _ _)]
    apply Continuous.comp continuous_ev (Continuous.prod_map continuous_ev id.2) <;> infer_instance

/-- The family of constant maps: `β → C(α, β)` as a continuous map. -/
def const' : C(β, C(α, β)) :=
  curry ⟨Prod.fst, continuous_fst⟩

@[simp]
theorem coe_const' : (const' : β → C(α, β)) = const :=
  rfl

theorem continuous_const' : Continuous (const : β → C(α, β)) :=
  const'.Continuous

end Curry

end CompactOpen

end ContinuousMap

open ContinuousMap

namespace Homeomorph

variable{α : Type _}{β : Type _}{γ : Type _}

variable[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ]

/-- Currying as a homeomorphism between the function spaces `C(α × β, γ)` and `C(α, C(β, γ))`. -/
def curry [LocallyCompactSpace α] [LocallyCompactSpace β] : C(α × β, γ) ≃ₜ C(α, C(β, γ)) :=
  ⟨⟨curry, uncurry,
      by 
        tidy,
      by 
        tidy⟩,
    continuous_curry, continuous_uncurry⟩

/-- If `α` has a single element, then `β` is homeomorphic to `C(α, β)`. -/
def continuous_map_of_unique [Unique α] : β ≃ₜ C(α, β) :=
  { toFun := ContinuousMap.comp ⟨_, continuous_fst⟩ ∘ coev α β, invFun := ev α β ∘ fun f => (f, default α),
    left_inv := fun a => rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rw [Unique.eq_default x]
          rfl,
    continuous_to_fun := Continuous.comp (continuous_comp _) continuous_coev,
    continuous_inv_fun := Continuous.comp continuous_ev (Continuous.prod_mk continuous_id continuous_const) }

@[simp]
theorem continuous_map_of_unique_apply [Unique α] (b : β) (a : α) : continuous_map_of_unique b a = b :=
  rfl

@[simp]
theorem continuous_map_of_unique_symm_apply [Unique α] (f : C(α, β)) :
  continuous_map_of_unique.symm f = f (default α) :=
  rfl

end Homeomorph

