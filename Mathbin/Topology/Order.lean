import Mathbin.Topology.Tactic

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion.
That is, for topologies `t₁` and `t₂` on `α`, we write `t₁ ≤ t₂`
if every set open in `t₂` is also open in `t₁`.
(One also calls `t₁` finer than `t₂`, and `t₂` coarser than `t₁`.)

Any function `f : α → β` induces
       `induced f : topological_space β → topological_space α`
and  `coinduced f : topological_space α → topological_space β`.
Continuity, the ordering on topologies and (co)induced topologies are
related as follows:
* The identity map (α, t₁) → (α, t₂) is continuous iff t₁ ≤ t₂.
* A map f : (α, t) → (β, u) is continuous
    iff             t ≤ induced f u   (`continuous_iff_le_induced`)
    iff coinduced f t ≤ u             (`continuous_iff_coinduced_le`).

Topologies on α form a complete lattice, with ⊥ the discrete topology
and ⊤ the indiscrete topology.

For a function f : α → β, (coinduced f, induced f) is a Galois connection
between topologies on α and topologies on β.

## Implementation notes

There is a Galois insertion between topologies on α (with the inclusion ordering)
and all collections of sets in α. The complete lattice structure on topologies
on α is defined as the reverse of the one obtained via this Galois insertion.

## Tags

finer, coarser, induced topology, coinduced topology

-/


open Set Filter Classical

open_locale Classical TopologicalSpace Filter

universe u v w

namespace TopologicalSpace

variable {α : Type u}

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » g)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » k)
/-- The open sets of the least topology containing a collection of basic sets. -/
inductive generate_open (g : Set (Set α)) : Set α → Prop
  | basic : ∀ s _ : s ∈ g, generate_open s
  | univ : generate_open univ
  | inter : ∀ s t, generate_open s → generate_open t → generate_open (s ∩ t)
  | sUnion : ∀ k, (∀ s _ : s ∈ k, generate_open s) → generate_open (⋃₀k)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from (g : Set (Set α)) : TopologicalSpace α :=
  { IsOpen := generate_open g, is_open_univ := generate_open.univ, is_open_inter := generate_open.inter,
    is_open_sUnion := generate_open.sUnion }

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » {s | «expr ∧ »(«expr ∈ »(a, s), «expr ∈ »(s, g))})
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  nhds_generate_from
  { g : Set Set α } { a : α } : @ nhds α generate_from g a = ⨅ ( s : _ ) ( _ : s ∈ { s | a ∈ s ∧ s ∈ g } ) , 𝓟 s
  :=
    by
      rw [ nhds_def ]
        <;>
        exact
          le_antisymmₓ
            infi_le_infi $ fun s => infi_le_infi_const $ fun ⟨ as , sg ⟩ => ⟨ as , generate_open.basic _ sg ⟩
              le_infi
                $
                fun
                  s
                    =>
                    le_infi
                      $
                      fun
                        ⟨ as , hs ⟩
                          =>
                          by
                            revert as
                              clear_
                              induction hs
                              case generate_open.basic s hs => exact fun as => infi_le_of_le s $ infi_le _ ⟨ as , hs ⟩
                              case generate_open.univ => rw [ principal_univ ] exact fun _ => le_top
                              case
                                generate_open.inter
                                s t hs' ht' hs ht
                                =>
                                exact
                                  fun ⟨ has , hat ⟩ => calc _ ≤ 𝓟 s ⊓ 𝓟 t := le_inf hs has ht hat _ = _ := inf_principal
                              case
                                generate_open.sUnion
                                k hk' hk
                                =>
                                exact
                                  fun
                                    ⟨ t , htk , hat ⟩
                                      =>
                                      calc
                                        _ ≤ 𝓟 t := hk t htk hat _ ≤ _ := le_principal_iff . 2 $ subset_sUnion_of_mem htk

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » g)
theorem tendsto_nhds_generate_from {β : Type _} {m : α → β} {f : Filter α} {g : Set (Set β)} {b : β}
  (h : ∀ s _ : s ∈ g, b ∈ s → m ⁻¹' s ∈ f) : tendsto m f (@nhds β (generate_from g) b) :=
  by 
    rw [nhds_generate_from] <;>
      exact tendsto_infi.2$ fun s => tendsto_infi.2$ fun ⟨hbs, hsg⟩ => tendsto_principal.2$ h s hsg hbs

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mk_of_nhds (n : α → Filter α) : TopologicalSpace α :=
  { IsOpen := fun s => ∀ a _ : a ∈ s, s ∈ n a, is_open_univ := fun x h => univ_mem,
    is_open_inter := fun s t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt),
    is_open_sUnion := fun s hs a ⟨x, hx, hxa⟩ => mem_of_superset (hs x hx _ hxa) (Set.subset_sUnion_of_mem hx) }

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » n a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a' «expr ∈ » t)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  nhds_mk_of_nhds
  ( n : α → Filter α )
      ( a : α )
      ( h₀ : pure ≤ n )
      ( h₁ : ∀ { a s } , s ∈ n a → ∃ ( t : _ ) ( _ : t ∈ n a ) , t ⊆ s ∧ ∀ a' _ : a' ∈ t , s ∈ n a' )
    : @ nhds α TopologicalSpace.mkOfNhds n a = n a
  :=
    by
      let this' := TopologicalSpace.mkOfNhds n
        refine' le_antisymmₓ fun s hs => _ fun s hs => _
        ·
          have h₀ : { b | s ∈ n b } ⊆ s := fun b hb => mem_pure . 1 $ h₀ b hb
            have h₁ : { b | s ∈ n b } ∈ 𝓝 a
            ·
              refine' IsOpen.mem_nhds fun b hb : s ∈ n b => _ hs
                rcases h₁ hb with ⟨ t , ht , hts , h ⟩
                exact mem_of_superset ht h
            exact mem_of_superset h₁ h₀
        ·
          rcases @ mem_nhds_iff α TopologicalSpace.mkOfNhds n _ _ . 1 hs with ⟨ t , hts , ht , hat ⟩
            exact n a . sets_of_superset ht _ hat hts

end TopologicalSpace

section Lattice

variable {α : Type u} {β : Type v}

/-- The inclusion ordering on topologies on α. We use it to get a complete
   lattice instance via the Galois insertion method, but the partial order
   that we will eventually impose on `topological_space α` is the reverse one. -/
def tmpOrder : PartialOrderₓ (TopologicalSpace α) :=
  { le := fun t s => t.is_open ≤ s.is_open, le_antisymm := fun t s h₁ h₂ => topological_space_eq$ le_antisymmₓ h₁ h₂,
    le_refl := fun t => le_reflₓ t.is_open,
    le_trans := fun a b c h₁ h₂ => @le_transₓ _ _ a.is_open b.is_open c.is_open h₁ h₂ }

attribute [local instance] tmpOrder

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
private
  theorem
    generate_from_le_iff_subset_is_open
    { g : Set Set α } { t : TopologicalSpace α } : TopologicalSpace.generateFrom g ≤ t ↔ g ⊆ { s | t.is_open s }
    :=
      Iff.intro
        fun ht s hs => ht _ $ TopologicalSpace.GenerateOpen.basic s hs
          fun
            hg s hs
              =>
              hs.rec_on
                fun v hv => hg hv t.is_open_univ fun u v _ _ => t.is_open_inter u v fun k _ => t.is_open_sUnion k

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
      If `s` equals the collection of open sets in the topology it generates,
        then `s` defines a topology. -/
    protected
  def
    mkOfClosure
    ( s : Set Set α ) ( hs : { u | TopologicalSpace.generateFrom s . IsOpen u } = s ) : TopologicalSpace α
    :=
      {
        IsOpen := fun u => u ∈ s ,
          is_open_univ := hs ▸ TopologicalSpace.GenerateOpen.univ ,
          is_open_inter := hs ▸ TopologicalSpace.GenerateOpen.inter ,
          is_open_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion
        }

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  mk_of_closure_sets
  { s : Set Set α } { hs : { u | TopologicalSpace.generateFrom s . IsOpen u } = s }
    : mkOfClosure s hs = TopologicalSpace.generateFrom s
  := topological_space_eq hs.symm

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
    The Galois insertion between `set (set α)` and `topological_space α` whose lower part
      sends a collection of subsets of α to the topology they generate, and whose upper part
      sends a topology to its collection of open subsets. -/
  def
    giGenerateFrom
    ( α : Type _ ) : GaloisInsertion TopologicalSpace.generateFrom fun t : TopologicalSpace α => { s | t.is_open s }
    :=
      {
        gc := fun g t => generate_from_le_iff_subset_is_open ,
          le_l_u := fun ts s hs => TopologicalSpace.GenerateOpen.basic s hs ,
          choice := fun g hg => mkOfClosure g subset.antisymm hg $ generate_from_le_iff_subset_is_open . 1 $ le_reflₓ _
            ,
          choice_eq := fun s hs => mk_of_closure_sets
        }

theorem generate_from_mono {α} {g₁ g₂ : Set (Set α)} (h : g₁ ⊆ g₂) :
  TopologicalSpace.generateFrom g₁ ≤ TopologicalSpace.generateFrom g₂ :=
  (giGenerateFrom _).gc.monotone_l h

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  generate_from_set_of_is_open
  ( t : TopologicalSpace α ) : TopologicalSpace.generateFrom { s | t.is_open s } = t
  := giGenerateFrom α . l_u_eq t

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  left_inverse_generate_from
  : Function.LeftInverse TopologicalSpace.generateFrom fun t : TopologicalSpace α => { s | t.is_open s }
  := giGenerateFrom α . left_inverse_l_u

theorem generate_from_surjective :
  Function.Surjective (TopologicalSpace.generateFrom : Set (Set α) → TopologicalSpace α) :=
  (giGenerateFrom α).l_surjective

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  set_of_is_open_injective
  : Function.Injective fun t : TopologicalSpace α => { s | t.is_open s }
  := giGenerateFrom α . u_injective

/-- The "temporary" order `tmp_order` on `topological_space α`, i.e. the inclusion order, is a
complete lattice.  (Note that later `topological_space α` will equipped with the dual order to
`tmp_order`). -/
def tmpCompleteLattice {α : Type u} : CompleteLattice (TopologicalSpace α) :=
  (giGenerateFrom α).liftCompleteLattice

instance : LE (TopologicalSpace α) :=
  { le := fun t s => s.is_open ≤ t.is_open }

protected theorem TopologicalSpace.le_def {α} {t s : TopologicalSpace α} : t ≤ s ↔ s.is_open ≤ t.is_open :=
  Iff.rfl

/-- The ordering on topologies on the type `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance : PartialOrderₓ (TopologicalSpace α) :=
  { TopologicalSpace.hasLe with le_antisymm := fun t s h₁ h₂ => topological_space_eq$ le_antisymmₓ h₂ h₁,
    le_refl := fun t => le_reflₓ t.is_open,
    le_trans := fun a b c h₁ h₂ => TopologicalSpace.le_def.mpr (le_transₓ h₂ h₁) }

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  le_generate_from_iff_subset_is_open
  { g : Set Set α } { t : TopologicalSpace α } : t ≤ TopologicalSpace.generateFrom g ↔ g ⊆ { s | t.is_open s }
  := generate_from_le_iff_subset_is_open

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : CompleteLattice (TopologicalSpace α) :=
  @OrderDual.completeLattice _ tmpCompleteLattice

theorem is_open_implies_is_open_iff {a b : TopologicalSpace α} : (∀ s, a.is_open s → b.is_open s) ↔ b ≤ a :=
  @GaloisInsertion.u_le_u_iff _ (OrderDual (TopologicalSpace α)) _ _ _ _ (giGenerateFrom α) a b

/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type _) [t : TopologicalSpace α] : Prop where 
  eq_bot{} : t = ⊥

instance (priority := 100) discrete_topology_bot (α : Type _) : @DiscreteTopology α ⊥ :=
  { eq_bot := rfl }

@[simp]
theorem is_open_discrete [TopologicalSpace α] [DiscreteTopology α] (s : Set α) : IsOpen s :=
  (DiscreteTopology.eq_bot α).symm ▸ trivialₓ

@[simp]
theorem is_closed_discrete [TopologicalSpace α] [DiscreteTopology α] (s : Set α) : IsClosed s :=
  is_open_compl_iff.1$ (DiscreteTopology.eq_bot α).symm ▸ trivialₓ

@[nontriviality]
theorem continuous_of_discrete_topology [TopologicalSpace α] [DiscreteTopology α] [TopologicalSpace β] {f : α → β} :
  Continuous f :=
  continuous_def.2$ fun s hs => is_open_discrete _

theorem nhds_bot (α : Type _) : @nhds α ⊥ = pure :=
  by 
    refine' le_antisymmₓ _ (@pure_le_nhds α ⊥)
    intro a s hs 
    exact @IsOpen.mem_nhds α ⊥ a s trivialₓ hs

theorem nhds_discrete (α : Type _) [TopologicalSpace α] [DiscreteTopology α] : @nhds α _ = pure :=
  (DiscreteTopology.eq_bot α).symm ▸ nhds_bot α

theorem le_of_nhds_le_nhds {t₁ t₂ : TopologicalSpace α} (h : ∀ x, @nhds α t₁ x ≤ @nhds α t₂ x) : t₁ ≤ t₂ :=
  fun s =>
    show @IsOpen α t₂ s → @IsOpen α t₁ s by 
      simp only [is_open_iff_nhds, le_principal_iff]
      exact fun hs a ha => h _$ hs _ ha

theorem eq_of_nhds_eq_nhds {t₁ t₂ : TopologicalSpace α} (h : ∀ x, @nhds α t₁ x = @nhds α t₂ x) : t₁ = t₂ :=
  le_antisymmₓ (le_of_nhds_le_nhds$ fun x => le_of_eqₓ$ h x) (le_of_nhds_le_nhds$ fun x => le_of_eqₓ$ (h x).symm)

theorem eq_bot_of_singletons_open {t : TopologicalSpace α} (h : ∀ x, t.is_open {x}) : t = ⊥ :=
  bot_unique$ fun s hs => bUnion_of_singleton s ▸ is_open_bUnion fun x _ => h x

theorem forall_open_iff_discrete {X : Type _} [TopologicalSpace X] : (∀ s : Set X, IsOpen s) ↔ DiscreteTopology X :=
  ⟨fun h =>
      ⟨by 
          ext U 
          show IsOpen U ↔ True 
          simp [h U]⟩,
    fun a => @is_open_discrete _ _ a⟩

theorem singletons_open_iff_discrete {X : Type _} [TopologicalSpace X] :
  (∀ a : X, IsOpen ({a} : Set X)) ↔ DiscreteTopology X :=
  ⟨fun h => ⟨eq_bot_of_singletons_open h⟩, fun a _ => @is_open_discrete _ _ a _⟩

end Lattice

section GaloisConnection

variable {α : Type _} {β : Type _} {γ : Type _}

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def TopologicalSpace.induced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace β) : TopologicalSpace α :=
  { IsOpen := fun s => ∃ s', t.is_open s' ∧ f ⁻¹' s' = s, is_open_univ := ⟨univ, t.is_open_univ, preimage_univ⟩,
    is_open_inter :=
      by 
        rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩ <;> exact ⟨s'₁ ∩ s'₂, t.is_open_inter _ _ hs₁ hs₂, preimage_inter⟩,
    is_open_sUnion :=
      fun s h =>
        by 
          simp only [Classical.skolem] at h 
          cases' h with f hf 
          apply Exists.introₓ (⋃ (x : Set α)(h : x ∈ s), f x h)
          simp only [sUnion_eq_bUnion, preimage_Union, fun x h => (hf x h).right]
          refine' ⟨_, rfl⟩
          exact
            @is_open_Union β _ t _$
              fun i => show IsOpen (⋃ h, f i h) from @is_open_Union β _ t _$ fun h => (hf i h).left }

theorem is_open_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
  @IsOpen α (t.induced f) s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl

theorem is_open_induced_iff' [t : TopologicalSpace β] {s : Set α} {f : α → β} :
  (t.induced f).IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl

theorem is_closed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
  @IsClosed α (t.induced f) s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s :=
  by 
    simp only [←is_open_compl_iff, is_open_induced_iff]
    exact
      ⟨fun ⟨t, ht, HEq⟩ =>
          ⟨tᶜ,
            by 
              rwa [compl_compl],
            by 
              simp [preimage_compl, HEq, compl_compl]⟩,
        fun ⟨t, ht, HEq⟩ =>
          ⟨tᶜ, ht,
            by 
              simp only [preimage_compl, HEq.symm]⟩⟩

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def TopologicalSpace.coinduced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace α) : TopologicalSpace β :=
  { IsOpen := fun s => t.is_open (f ⁻¹' s),
    is_open_univ :=
      by 
        rw [preimage_univ] <;> exact t.is_open_univ,
    is_open_inter :=
      fun s₁ s₂ h₁ h₂ =>
        by 
          rw [preimage_inter] <;> exact t.is_open_inter _ _ h₁ h₂,
    is_open_sUnion :=
      fun s h =>
        by 
          rw [preimage_sUnion] <;>
            exact
              @is_open_Union _ _ t _$
                fun i => show IsOpen (⋃ H : i ∈ s, f ⁻¹' i) from @is_open_Union _ _ t _$ fun hi => h i hi }

theorem is_open_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
  @IsOpen β (TopologicalSpace.coinduced f t) s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl

theorem preimage_nhds_coinduced [TopologicalSpace α] {π : α → β} {s : Set β} {a : α}
  (hs : s ∈ @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a :=
  by 
    let this' := TopologicalSpace.coinduced π ‹_›
    rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
    exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩

variable {t t₁ t₂ : TopologicalSpace α} {t' : TopologicalSpace β} {f : α → β} {g : β → α}

theorem Continuous.coinduced_le (h : @Continuous α β t t' f) : t.coinduced f ≤ t' :=
  fun s hs => (continuous_def.1 h s hs : _)

theorem coinduced_le_iff_le_induced {f : α → β} {tα : TopologicalSpace α} {tβ : TopologicalSpace β} :
  tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
  Iff.intro (fun h s ⟨t, ht, hst⟩ => hst ▸ h _ ht) fun h s hs => show tα.is_open (f ⁻¹' s) from h _ ⟨s, hs, rfl⟩

theorem Continuous.le_induced (h : @Continuous α β t t' f) : t ≤ t'.induced f :=
  coinduced_le_iff_le_induced.1 h.coinduced_le

theorem gc_coinduced_induced (f : α → β) :
  GaloisConnection (TopologicalSpace.coinduced f) (TopologicalSpace.induced f) :=
  fun f g => coinduced_le_iff_le_induced

theorem induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
  (gc_coinduced_induced g).monotone_u h

theorem coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
  (gc_coinduced_induced f).monotone_l h

@[simp]
theorem induced_top : (⊤ : TopologicalSpace α).induced g = ⊤ :=
  (gc_coinduced_induced g).u_top

@[simp]
theorem induced_inf : (t₁⊓t₂).induced g = t₁.induced g⊓t₂.induced g :=
  (gc_coinduced_induced g).u_inf

@[simp]
theorem induced_infi {ι : Sort w} {t : ι → TopologicalSpace α} : (⨅ i, t i).induced g = ⨅ i, (t i).induced g :=
  (gc_coinduced_induced g).u_infi

@[simp]
theorem coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥ :=
  (gc_coinduced_induced f).l_bot

@[simp]
theorem coinduced_sup : (t₁⊔t₂).coinduced f = t₁.coinduced f⊔t₂.coinduced f :=
  (gc_coinduced_induced f).l_sup

@[simp]
theorem coinduced_supr {ι : Sort w} {t : ι → TopologicalSpace α} : (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f :=
  (gc_coinduced_induced f).l_supr

theorem induced_id [t : TopologicalSpace α] : t.induced id = t :=
  topological_space_eq$ funext$ fun s => propext$ ⟨fun ⟨s', hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩

theorem induced_compose [tγ : TopologicalSpace γ] {f : α → β} {g : β → γ} :
  (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
  topological_space_eq$
    funext$
      fun s =>
        propext$
          ⟨fun ⟨s', ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩, fun ⟨s, hs, h⟩ => ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

theorem induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun y : β => x) = ⊤ :=
  le_antisymmₓ le_top (@continuous_const β α ⊤ t x).le_induced

theorem coinduced_id [t : TopologicalSpace α] : t.coinduced id = t :=
  topological_space_eq rfl

theorem coinduced_compose [tα : TopologicalSpace α] {f : α → β} {g : β → γ} :
  (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
  topological_space_eq rfl

end GaloisConnection

section Constructions

open TopologicalSpace

variable {α : Type u} {β : Type v}

instance inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α) :=
  ⟨⊤⟩

instance (priority := 100) Subsingleton.uniqueTopologicalSpace [Subsingleton α] : Unique (TopologicalSpace α) :=
  { default := ⊥,
    uniq :=
      fun t =>
        eq_bot_of_singletons_open$
          fun x => Subsingleton.set_cases (@is_open_empty _ t) (@is_open_univ _ t) ({x} : Set α) }

instance (priority := 100) Subsingleton.discrete_topology [t : TopologicalSpace α] [Subsingleton α] :
  DiscreteTopology α :=
  ⟨Unique.eq_default t⟩

instance : TopologicalSpace Empty :=
  ⊥

instance : DiscreteTopology Empty :=
  ⟨rfl⟩

instance : TopologicalSpace Pempty :=
  ⊥

instance : DiscreteTopology Pempty :=
  ⟨rfl⟩

instance : TopologicalSpace PUnit :=
  ⊥

instance : DiscreteTopology PUnit :=
  ⟨rfl⟩

instance : TopologicalSpace Bool :=
  ⊥

instance : DiscreteTopology Bool :=
  ⟨rfl⟩

instance : TopologicalSpace ℕ :=
  ⊥

instance : DiscreteTopology ℕ :=
  ⟨rfl⟩

instance : TopologicalSpace ℤ :=
  ⊥

instance : DiscreteTopology ℤ :=
  ⟨rfl⟩

instance sierpinskiSpace : TopologicalSpace Prop :=
  generate_from {{True}}

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » g)
theorem le_generate_from {t : TopologicalSpace α} {g : Set (Set α)} (h : ∀ s _ : s ∈ g, IsOpen s) :
  t ≤ generate_from g :=
  le_generate_from_iff_subset_is_open.2 h

theorem induced_generate_from_eq {α β} {b : Set (Set β)} {f : α → β} :
  (generate_from b).induced f = TopologicalSpace.generateFrom (preimage f '' b) :=
  le_antisymmₓ (le_generate_from$ ball_image_iff.2$ fun s hs => ⟨s, generate_open.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1$ le_generate_from$ fun s hs => generate_open.basic _$ mem_image_of_mem _ hs)

theorem le_induced_generate_from {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α → β}
  (h : ∀ a : Set β, a ∈ b → IsOpen (f ⁻¹' a)) : t ≤ induced f (generate_from b) :=
  by 
    rw [induced_generate_from_eq]
    apply le_generate_from 
    simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp_distrib]
    exact h

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
protected def TopologicalSpace.nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α :=
  { IsOpen := fun s => a ∈ s → s ∈ f, is_open_univ := fun s => univ_mem,
    is_open_inter := fun s t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat),
    is_open_sUnion := fun k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu) }

theorem gc_nhds (a : α) : GaloisConnection (TopologicalSpace.nhdsAdjoint a) fun t => @nhds α t a :=
  fun f t =>
    by 
      rw [le_nhds_iff]
      exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩

theorem nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ ≤ t₂) : @nhds α t₁ a ≤ @nhds α t₂ a :=
  (gc_nhds a).monotone_u h

theorem nhds_infi {ι : Sort _} {t : ι → TopologicalSpace α} {a : α} : @nhds α (infi t) a = ⨅ i, @nhds α (t i) a :=
  (gc_nhds a).u_infi

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » s)
theorem nhds_Inf {s : Set (TopologicalSpace α)} {a : α} : @nhds α (Inf s) a = ⨅ (t : _)(_ : t ∈ s), @nhds α t a :=
  (gc_nhds a).u_Inf

theorem nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} : @nhds α (t₁⊓t₂) a = @nhds α t₁ a⊓@nhds α t₂ a :=
  (gc_nhds a).u_inf

theorem nhds_top {a : α} : @nhds α ⊤ a = ⊤ :=
  (gc_nhds a).u_top

local notation "cont" => @Continuous _ _

local notation "tspace" => TopologicalSpace

open TopologicalSpace

variable {γ : Type _} {f : α → β} {ι : Sort _}

theorem continuous_iff_coinduced_le {t₁ : tspace α} {t₂ : tspace β} : cont t₁ t₂ f ↔ coinduced f t₁ ≤ t₂ :=
  continuous_def.trans Iff.rfl

theorem continuous_iff_le_induced {t₁ : tspace α} {t₂ : tspace β} : cont t₁ t₂ f ↔ t₁ ≤ induced f t₂ :=
  Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » b)
theorem continuous_generated_from {t : tspace α} {b : Set (Set β)} (h : ∀ s _ : s ∈ b, IsOpen (f ⁻¹' s)) :
  cont t (generate_from b) f :=
  continuous_iff_coinduced_le.2$ le_generate_from h

@[continuity]
theorem continuous_induced_dom {t : tspace β} : cont (induced f t) t f :=
  by 
    rw [continuous_def]
    intro s h 
    exact ⟨_, h, rfl⟩

theorem continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ} (h : cont t₁ t₂ (f ∘ g)) :
  cont t₁ (induced f t₂) g :=
  by 
    rw [continuous_def]
    rintro s ⟨t, ht, s_eq⟩
    simpa [←s_eq] using continuous_def.1 h t ht

theorem continuous_induced_rng' [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {g : γ → α} (f : α → β)
  (H : ‹TopologicalSpace α› = ‹TopologicalSpace β›.induced f) (h : Continuous (f ∘ g)) : Continuous g :=
  H.symm ▸ continuous_induced_rng h

theorem continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f :=
  by 
    rw [continuous_def]
    intro s h 
    exact h

theorem continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ} (h : cont t₁ t₂ (g ∘ f)) :
  cont (coinduced f t₁) t₂ g :=
  by 
    rw [continuous_def] at h⊢
    intro s hs 
    exact h _ hs

theorem continuous_le_dom {t₁ t₂ : tspace α} {t₃ : tspace β} (h₁ : t₂ ≤ t₁) (h₂ : cont t₁ t₃ f) : cont t₂ t₃ f :=
  by 
    rw [continuous_def] at h₂⊢
    intro s h 
    exact h₁ _ (h₂ s h)

theorem continuous_le_rng {t₁ : tspace α} {t₂ t₃ : tspace β} (h₁ : t₂ ≤ t₃) (h₂ : cont t₁ t₂ f) : cont t₁ t₃ f :=
  by 
    rw [continuous_def] at h₂⊢
    intro s h 
    exact h₂ s (h₁ s h)

theorem continuous_sup_dom {t₁ t₂ : tspace α} {t₃ : tspace β} (h₁ : cont t₁ t₃ f) (h₂ : cont t₂ t₃ f) :
  cont (t₁⊔t₂) t₃ f :=
  by 
    rw [continuous_def] at h₁ h₂⊢
    intro s h 
    exact ⟨h₁ s h, h₂ s h⟩

theorem continuous_sup_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β} : cont t₁ t₂ f → cont t₁ (t₂⊔t₃) f :=
  continuous_le_rng le_sup_left

theorem continuous_sup_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β} : cont t₁ t₃ f → cont t₁ (t₂⊔t₃) f :=
  continuous_le_rng le_sup_right

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » t₁)
theorem continuous_Sup_dom {t₁ : Set (tspace α)} {t₂ : tspace β} (h : ∀ t _ : t ∈ t₁, cont t t₂ f) :
  cont (Sup t₁) t₂ f :=
  continuous_iff_le_induced.2$ Sup_le$ fun t ht => continuous_iff_le_induced.1$ h t ht

theorem continuous_Sup_rng {t₁ : tspace α} {t₂ : Set (tspace β)} {t : tspace β} (h₁ : t ∈ t₂) (hf : cont t₁ t f) :
  cont t₁ (Sup t₂) f :=
  continuous_iff_coinduced_le.2$ le_Sup_of_le h₁$ continuous_iff_coinduced_le.1 hf

theorem continuous_supr_dom {t₁ : ι → tspace α} {t₂ : tspace β} (h : ∀ i, cont (t₁ i) t₂ f) : cont (supr t₁) t₂ f :=
  continuous_Sup_dom$ fun t ⟨i, (t_eq : t₁ i = t)⟩ => t_eq ▸ h i

theorem continuous_supr_rng {t₁ : tspace α} {t₂ : ι → tspace β} {i : ι} (h : cont t₁ (t₂ i) f) : cont t₁ (supr t₂) f :=
  continuous_Sup_rng ⟨i, rfl⟩ h

theorem continuous_inf_rng {t₁ : tspace α} {t₂ t₃ : tspace β} (h₁ : cont t₁ t₂ f) (h₂ : cont t₁ t₃ f) :
  cont t₁ (t₂⊓t₃) f :=
  continuous_iff_coinduced_le.2$ le_inf (continuous_iff_coinduced_le.1 h₁) (continuous_iff_coinduced_le.1 h₂)

theorem continuous_inf_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β} : cont t₁ t₃ f → cont (t₁⊓t₂) t₃ f :=
  continuous_le_dom inf_le_left

theorem continuous_inf_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β} : cont t₂ t₃ f → cont (t₁⊓t₂) t₃ f :=
  continuous_le_dom inf_le_right

theorem continuous_Inf_dom {t₁ : Set (tspace α)} {t₂ : tspace β} {t : tspace α} (h₁ : t ∈ t₁) :
  cont t t₂ f → cont (Inf t₁) t₂ f :=
  continuous_le_dom$ Inf_le h₁

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » t₂)
theorem continuous_Inf_rng {t₁ : tspace α} {t₂ : Set (tspace β)} (h : ∀ t _ : t ∈ t₂, cont t₁ t f) :
  cont t₁ (Inf t₂) f :=
  continuous_iff_coinduced_le.2$ le_Inf$ fun b hb => continuous_iff_coinduced_le.1$ h b hb

theorem continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β} {i : ι} : cont (t₁ i) t₂ f → cont (infi t₁) t₂ f :=
  continuous_le_dom$ infi_le _ _

theorem continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β} (h : ∀ i, cont t₁ (t₂ i) f) : cont t₁ (infi t₂) f :=
  continuous_iff_coinduced_le.2$ le_infi$ fun i => continuous_iff_coinduced_le.1$ h i

@[continuity]
theorem continuous_bot {t : tspace β} : cont ⊥ t f :=
  continuous_iff_le_induced.2$ bot_le

@[continuity]
theorem continuous_top {t : tspace α} : cont t ⊤ f :=
  continuous_iff_coinduced_le.2$ le_top

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (u «expr ∈ » expr𝓝() (f a))
theorem mem_nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) (s : Set β) :
  s ∈ @nhds β (TopologicalSpace.induced f T) a ↔ ∃ (u : _)(_ : u ∈ 𝓝 (f a)), f ⁻¹' u ⊆ s :=
  by 
    simp only [mem_nhds_iff, is_open_induced_iff, exists_prop, Set.mem_set_of_eq]
    constructor
    ·
      rintro ⟨u, usub, ⟨v, openv, ueq⟩, au⟩
      exact
        ⟨v,
          ⟨v, Set.Subset.refl v, openv,
            by 
              rwa [←ueq] at au⟩,
          by 
            rw [ueq] <;> exact usub⟩
    rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
    exact ⟨f ⁻¹' v, Set.Subset.trans (Set.preimage_mono vsubu) finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩

theorem nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) :
  @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a)) :=
  by 
    ext s 
    rw [mem_nhds_induced, mem_comap]

theorem induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β → α) :
  tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝$ f b) :=
  ⟨fun h a => h.symm ▸ nhds_induced f a,
    fun h =>
      eq_of_nhds_eq_nhds$
        fun x =>
          by 
            rw [h, nhds_induced]⟩

theorem map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β → α} (hf : Function.Surjective f) (a : β) :
  map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f a) :=
  by 
    rw [nhds_induced, map_comap_of_surjective hf]

end Constructions

section Induced

open TopologicalSpace

variable {α : Type _} {β : Type _}

variable [t : TopologicalSpace β] {f : α → β}

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem is_open_induced_eq { s : Set α } : @ IsOpen _ induced f t s ↔ s ∈ preimage f '' { s | IsOpen s } := Iff.rfl

theorem is_open_induced {s : Set β} (h : IsOpen s) : (induced f t).IsOpen (f ⁻¹' s) :=
  ⟨s, h, rfl⟩

theorem map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] f a :=
  by 
    rw [nhds_induced, Filter.map_comap, nhdsWithin]

theorem map_nhds_induced_of_mem {a : α} (h : range f ∈ 𝓝 (f a)) : map f (@nhds α (induced f t) a) = 𝓝 (f a) :=
  by 
    rw [nhds_induced, Filter.map_comap_of_mem h]

theorem closure_induced [t : TopologicalSpace β] {f : α → β} {a : α} {s : Set α} :
  a ∈ @Closure α (TopologicalSpace.induced f t) s ↔ f a ∈ Closure (f '' s) :=
  by 
    simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]

end Induced

section Sierpinski

variable {α : Type _} [TopologicalSpace α]

@[simp]
theorem is_open_singleton_true : IsOpen ({True} : Set Prop) :=
  TopologicalSpace.GenerateOpen.basic _
    (by 
      simp )

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  continuous_Prop
  { p : α → Prop } : Continuous p ↔ IsOpen { x | p x }
  :=
    ⟨
      fun
          h : Continuous p
            =>
            have
              : IsOpen p ⁻¹' { True } := is_open_singleton_true . Preimage h
              by simp [ preimage , eq_trueₓ ] at this <;> assumption
        ,
        fun
          h : IsOpen { x | p x }
            =>
            continuous_generated_from
              $
              fun s hs : s ∈ { { True } } => by simp at hs <;> simp [ hs , preimage , eq_trueₓ , h ]
      ⟩

theorem is_open_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous fun x => x ∈ s :=
  continuous_Prop.symm

end Sierpinski

section infi

variable {α : Type u} {ι : Sort v}

theorem generate_from_union (a₁ a₂ : Set (Set α)) :
  TopologicalSpace.generateFrom (a₁ ∪ a₂) = TopologicalSpace.generateFrom a₁⊓TopologicalSpace.generateFrom a₂ :=
  @GaloisConnection.l_sup _ (OrderDual (TopologicalSpace α)) a₁ a₂ _ _ _ _
    fun g t => generate_from_le_iff_subset_is_open

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  set_of_is_open_sup
  ( t₁ t₂ : TopologicalSpace α ) : { s | t₁ ⊔ t₂ . IsOpen s } = { s | t₁.is_open s } ∩ { s | t₂.is_open s }
  :=
    @ GaloisConnection.u_inf _ OrderDual TopologicalSpace α t₁ t₂ _ _ _ _ fun g t => generate_from_le_iff_subset_is_open

theorem generate_from_Union {f : ι → Set (Set α)} :
  TopologicalSpace.generateFrom (⋃ i, f i) = ⨅ i, TopologicalSpace.generateFrom (f i) :=
  @GaloisConnection.l_supr _ (OrderDual (TopologicalSpace α)) _ _ _ _ _ (fun g t => generate_from_le_iff_subset_is_open)
    f

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  set_of_is_open_supr
  { t : ι → TopologicalSpace α } : { s | ⨆ i , t i . IsOpen s } = ⋂ i , { s | t i . IsOpen s }
  := @ GaloisConnection.u_infi _ OrderDual TopologicalSpace α _ _ _ _ _ fun g t => generate_from_le_iff_subset_is_open t

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » S)
theorem generate_from_sUnion {S : Set (Set (Set α))} :
  TopologicalSpace.generateFrom (⋃₀S) = ⨅ (s : _)(_ : s ∈ S), TopologicalSpace.generateFrom s :=
  @GaloisConnection.l_Sup _ (OrderDual (TopologicalSpace α)) _ _ _ _ (fun g t => generate_from_le_iff_subset_is_open) S

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » T)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  set_of_is_open_Sup
  { T : Set TopologicalSpace α }
    : { s | Sup T . IsOpen s } = ⋂ ( t : _ ) ( _ : t ∈ T ) , { s | ( t : TopologicalSpace α ) . IsOpen s }
  := @ GaloisConnection.u_Inf _ OrderDual TopologicalSpace α _ _ _ _ fun g t => generate_from_le_iff_subset_is_open T

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  generate_from_union_is_open
  ( a b : TopologicalSpace α ) : TopologicalSpace.generateFrom { s | a.is_open s } ∪ { s | b.is_open s } = a ⊓ b
  := @ GaloisInsertion.l_sup_u _ OrderDual TopologicalSpace α _ _ _ _ giGenerateFrom α a b

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  generate_from_Union_is_open
  ( f : ι → TopologicalSpace α ) : TopologicalSpace.generateFrom ⋃ i , { s | f i . IsOpen s } = ⨅ i , f i
  := @ GaloisInsertion.l_supr_u _ OrderDual TopologicalSpace α _ _ _ _ giGenerateFrom α _ f

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  generate_from_inter
  ( a b : TopologicalSpace α ) : TopologicalSpace.generateFrom { s | a.is_open s } ∩ { s | b.is_open s } = a ⊔ b
  := @ GaloisInsertion.l_inf_u _ OrderDual TopologicalSpace α _ _ _ _ giGenerateFrom α a b

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  generate_from_Inter
  ( f : ι → TopologicalSpace α ) : TopologicalSpace.generateFrom ⋂ i , { s | f i . IsOpen s } = ⨆ i , f i
  := @ GaloisInsertion.l_infi_u _ OrderDual TopologicalSpace α _ _ _ _ giGenerateFrom α _ f

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  generate_from_Inter_of_generate_from_eq_self
  ( f : ι → Set Set α ) ( hf : ∀ i , { s | TopologicalSpace.generateFrom f i . IsOpen s } = f i )
    : TopologicalSpace.generateFrom ⋂ i , f i = ⨆ i , TopologicalSpace.generateFrom f i
  := @ GaloisInsertion.l_infi_of_ul_eq_self _ OrderDual TopologicalSpace α _ _ _ _ giGenerateFrom α _ f hf

variable {t : ι → TopologicalSpace α}

theorem is_open_supr_iff {s : Set α} : @IsOpen _ (⨆ i, t i) s ↔ ∀ i, @IsOpen _ (t i) s :=
  show s ∈ SetOf (supr t).IsOpen ↔ s ∈ { x : Set α | ∀ i : ι, (t i).IsOpen x }by 
    simp [set_of_is_open_supr]

theorem is_closed_infi_iff {s : Set α} : @IsClosed _ (⨆ i, t i) s ↔ ∀ i, @IsClosed _ (t i) s :=
  by 
    simp [←is_open_compl_iff, is_open_supr_iff]

end infi

