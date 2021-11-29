import Mathbin.Topology.Bases 
import Mathbin.Topology.DenseEmbedding

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

Parts of the formalization are based on "Ultrafilters and Topology"
by Marius Stekelenburg, particularly section 5.
-/


noncomputable theory

open Filter Set

open_locale TopologicalSpace

universe u v

section Ultrafilter

/-- Basis for the topology on `ultrafilter α`. -/
def UltrafilterBasis (α : Type u) : Set (Set (Ultrafilter α)) :=
  range$ fun s : Set α => { u | s ∈ u }

variable {α : Type u}

instance : TopologicalSpace (Ultrafilter α) :=
  TopologicalSpace.generateFrom (UltrafilterBasis α)

theorem ultrafilter_basis_is_basis : TopologicalSpace.IsTopologicalBasis (UltrafilterBasis α) :=
  ⟨by 
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
      refine' ⟨_, ⟨a ∩ b, rfl⟩, inter_mem ua ub, fun v hv => ⟨_, _⟩⟩ <;>
        apply mem_of_superset hv <;> simp [inter_subset_right a b],
    eq_univ_of_univ_subset$ subset_sUnion_of_mem$ ⟨univ, eq_univ_of_forall fun u => univ_mem⟩, rfl⟩

/-- The basic open sets for the topology on ultrafilters are open. -/
theorem ultrafilter_is_open_basic (s : Set α) : IsOpen { u:Ultrafilter α | s ∈ u } :=
  ultrafilter_basis_is_basis.IsOpen ⟨s, rfl⟩

/-- The basic open sets for the topology on ultrafilters are also closed. -/
theorem ultrafilter_is_closed_basic (s : Set α) : IsClosed { u:Ultrafilter α | s ∈ u } :=
  by 
    rw [←is_open_compl_iff]
    convert ultrafilter_is_open_basic («expr ᶜ» s)
    ext u 
    exact ultrafilter.compl_mem_iff_not_mem.symm

/-- Every ultrafilter `u` on `ultrafilter α` converges to a unique
  point of `ultrafilter α`, namely `mjoin u`. -/
theorem ultrafilter_converges_iff {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α} :
  «expr↑ » u ≤ 𝓝 x ↔ x = mjoin u :=
  by 
    rw [eq_comm, ←Ultrafilter.coe_le_coe]
    change «expr↑ » u ≤ 𝓝 x ↔ ∀ s _ : s ∈ x, { v:Ultrafilter α | s ∈ v } ∈ u 
    simp only [TopologicalSpace.nhds_generate_from, le_infi_iff, UltrafilterBasis, le_principal_iff, mem_set_of_eq]
    split 
    ·
      intro h a ha 
      exact h _ ⟨ha, a, rfl⟩
    ·
      rintro h a ⟨xi, a, rfl⟩
      exact h _ xi

instance ultrafilter_compact : CompactSpace (Ultrafilter α) :=
  ⟨is_compact_iff_ultrafilter_le_nhds.mpr$ fun f _ => ⟨mjoin f, trivialₓ, ultrafilter_converges_iff.mpr rfl⟩⟩

instance Ultrafilter.t2_space : T2Space (Ultrafilter α) :=
  t2_iff_ultrafilter.mpr$
    fun x y f fx fy =>
      have hx : x = mjoin f := ultrafilter_converges_iff.mp fx 
      have hy : y = mjoin f := ultrafilter_converges_iff.mp fy 
      hx.trans hy.symm

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : totally_disconnected_space (ultrafilter α) :=
begin
  rw [expr totally_disconnected_space_iff_connected_component_singleton] [],
  intro [ident A],
  simp [] [] ["only"] ["[", expr set.eq_singleton_iff_unique_mem, ",", expr mem_connected_component, ",", expr true_and, "]"] [] [],
  intros [ident B, ident hB],
  rw ["<-", expr ultrafilter.coe_le_coe] [],
  intros [ident s, ident hs],
  rw ["[", expr connected_component_eq_Inter_clopen, ",", expr set.mem_Inter, "]"] ["at", ident hB],
  let [ident Z] [] [":=", expr {F : ultrafilter α | «expr ∈ »(s, F)}],
  have [ident hZ] [":", expr is_clopen Z] [":=", expr ⟨ultrafilter_is_open_basic s, ultrafilter_is_closed_basic s⟩],
  exact [expr hB ⟨Z, hZ, hs⟩]
end

theorem ultrafilter_comap_pure_nhds (b : Ultrafilter α) : comap pure (𝓝 b) ≤ b :=
  by 
    rw [TopologicalSpace.nhds_generate_from]
    simp only [comap_infi, comap_principal]
    intro s hs 
    rw [←le_principal_iff]
    refine' infi_le_of_le { u | s ∈ u } _ 
    refine' infi_le_of_le ⟨hs, ⟨s, rfl⟩⟩ _ 
    exact principal_mono.2 fun a => id

section Embedding

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ultrafilter_pure_injective : function.injective (pure : α → ultrafilter α) :=
begin
  intros [ident x, ident y, ident h],
  have [] [":", expr «expr ∈ »({x}, (pure x : ultrafilter α))] [":=", expr singleton_mem_pure],
  rw [expr h] ["at", ident this],
  exact [expr (mem_singleton_iff.mp (mem_pure.mp this)).symm]
end

open TopologicalSpace

/-- The range of `pure : α → ultrafilter α` is dense in `ultrafilter α`. -/
theorem dense_range_pure : DenseRange (pure : α → Ultrafilter α) :=
  fun x =>
    mem_closure_iff_ultrafilter.mpr ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pureₓ x).symm⟩

/-- The map `pure : α → ultra_filter α` induces on `α` the discrete topology. -/
theorem induced_topology_pure : TopologicalSpace.induced (pure : α → Ultrafilter α) Ultrafilter.topologicalSpace = ⊥ :=
  by 
    apply eq_bot_of_singletons_open 
    intro x 
    use { u:Ultrafilter α | {x} ∈ u }, ultrafilter_is_open_basic _ 
    simp 

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `pure : α → ultrafilter α` defines a dense inducing of `α` in `ultrafilter α`. -/
theorem dense_inducing_pure : @dense_inducing _ _ «expr⊥»() _ (pure : α → ultrafilter α) :=
by letI [] [":", expr topological_space α] [":=", expr «expr⊥»()]; exact [expr ⟨⟨induced_topology_pure.symm⟩, dense_range_pure⟩]

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `pure : α → ultrafilter α` defines a dense embedding of `α` in `ultrafilter α`. -/
theorem dense_embedding_pure : @dense_embedding _ _ «expr⊥»() _ (pure : α → ultrafilter α) :=
by letI [] [":", expr topological_space α] [":=", expr «expr⊥»()]; exact [expr { inj := ultrafilter_pure_injective,
   ..dense_inducing_pure }]

end Embedding

section Extension

variable {γ : Type _} [TopologicalSpace γ]

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The extension of a function `α → γ` to a function `ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous. -/
def ultrafilter.extend (f : α → γ) : ultrafilter α → γ :=
by letI [] [":", expr topological_space α] [":=", expr «expr⊥»()]; exact [expr dense_inducing_pure.extend f]

variable [T2Space γ]

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ultrafilter_extend_extends (f : α → γ) : «expr = »(«expr ∘ »(ultrafilter.extend f, pure), f) :=
begin
  letI [] [":", expr topological_space α] [":=", expr «expr⊥»()],
  haveI [] [":", expr discrete_topology α] [":=", expr ⟨rfl⟩],
  exact [expr funext (dense_inducing_pure.extend_eq continuous_of_discrete_topology)]
end

variable [CompactSpace γ]

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_ultrafilter_extend (f : α → γ) : continuous (ultrafilter.extend f) :=
have ∀
b : ultrafilter α, «expr∃ , »((c), tendsto f (comap pure (expr𝓝() b)) (expr𝓝() c)) := assume
b, let ⟨c, _, h⟩ := compact_univ.ultrafilter_le_nhds (b.map f) (by rw ["[", expr le_principal_iff, "]"] []; exact [expr univ_mem]) in
⟨c, le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h⟩,
begin
  letI [] [":", expr topological_space α] [":=", expr «expr⊥»()],
  haveI [] [":", expr normal_space γ] [":=", expr normal_of_compact_t2],
  exact [expr dense_inducing_pure.continuous_extend this]
end

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The value of `ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`. -/
theorem ultrafilter_extend_eq_iff
{f : α → γ}
{b : ultrafilter α}
{c : γ} : «expr ↔ »(«expr = »(ultrafilter.extend f b, c), «expr ≤ »(«expr↑ »(b.map f), expr𝓝() c)) :=
⟨assume h, begin
   let [ident b'] [":", expr ultrafilter (ultrafilter α)] [":=", expr b.map pure],
   have [ident t] [":", expr «expr ≤ »(«expr↑ »(b'), expr𝓝() b)] [],
   from [expr ultrafilter_converges_iff.mpr (bind_pure _).symm],
   rw ["<-", expr h] [],
   have [] [] [":=", expr (continuous_ultrafilter_extend f).tendsto b],
   refine [expr le_trans _ (le_trans (map_mono t) this)],
   change [expr «expr ≤ »(_, map «expr ∘ »(ultrafilter.extend f, pure) «expr↑ »(b))] [] [],
   rw [expr ultrafilter_extend_extends] [],
   exact [expr le_refl _]
 end, assume
 h, by letI [] [":", expr topological_space α] [":=", expr «expr⊥»()]; exact [expr dense_inducing_pure.extend_eq_of_tendsto (le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h)]⟩

end Extension

end Ultrafilter

section StoneCech

variable (α : Type u) [TopologicalSpace α]

instance stoneCechSetoid : Setoidₓ (Ultrafilter α) :=
  { R :=
      fun x y =>
        ∀ γ : Type u [TopologicalSpace γ],
          by 
            exact
              ∀ [T2Space γ] [CompactSpace γ] f : α → γ hf : Continuous f,
                Ultrafilter.extend f x = Ultrafilter.extend f y,
    iseqv :=
      ⟨fun x γ tγ h₁ h₂ f hf => rfl,
        fun x y xy γ tγ h₁ h₂ f hf =>
          by 
            exact (xy γ f hf).symm,
        fun x y z xy yz γ tγ h₁ h₂ f hf =>
          by 
            exact (xy γ f hf).trans (yz γ f hf)⟩ }

/-- The Stone-Čech compactification of a topological space. -/
def StoneCech : Type u :=
  Quotientₓ (stoneCechSetoid α)

variable {α}

instance : TopologicalSpace (StoneCech α) :=
  by 
    unfold StoneCech <;> infer_instance

instance [Inhabited α] : Inhabited (StoneCech α) :=
  by 
    unfold StoneCech <;> infer_instance

/-- The natural map from α to its Stone-Čech compactification. -/
def stoneCechUnit (x : α) : StoneCech α :=
  «expr⟦ ⟧» (pure x)

/-- The image of stone_cech_unit is dense. (But stone_cech_unit need
  not be an embedding, for example if α is not Hausdorff.) -/
theorem dense_range_stone_cech_unit : DenseRange (stoneCechUnit : α → StoneCech α) :=
  dense_range_pure.Quotient

section Extension

variable {γ : Type u} [TopologicalSpace γ] [T2Space γ] [CompactSpace γ]

variable {f : α → γ} (hf : Continuous f)

attribute [local elab_with_expected_type] Quotientₓ.lift

/-- The extension of a continuous function from α to a compact
  Hausdorff space γ to the Stone-Čech compactification of α. -/
def stoneCechExtend : StoneCech α → γ :=
  Quotientₓ.lift (Ultrafilter.extend f) fun x y xy => xy γ f hf

theorem stone_cech_extend_extends : (stoneCechExtend hf ∘ stoneCechUnit) = f :=
  ultrafilter_extend_extends f

theorem continuous_stone_cech_extend : Continuous (stoneCechExtend hf) :=
  continuous_quot_lift _ (continuous_ultrafilter_extend f)

end Extension

theorem convergent_eqv_pure {u : Ultrafilter α} {x : α} (ux : «expr↑ » u ≤ 𝓝 x) : u ≈ pure x :=
  fun γ tγ h₁ h₂ f hf =>
    by 
      skip 
      trans f x 
      swap 
      symm 
      all_goals 
        refine' ultrafilter_extend_eq_iff.mpr (le_transₓ (map_mono _) (hf.tendsto _))
      ·
        apply pure_le_nhds
      ·
        exact ux

theorem continuous_stone_cech_unit : Continuous (stoneCechUnit : α → StoneCech α) :=
  continuous_iff_ultrafilter.mpr$
    fun x g gx =>
      have  : «expr↑ » (g.map pure) ≤ 𝓝 g :=
        by 
          rw [ultrafilter_converges_iff] <;> exact (bind_pureₓ _).symm 
      have  : (g.map stoneCechUnit : Filter (StoneCech α)) ≤ 𝓝 («expr⟦ ⟧» g) :=
        continuous_at_iff_ultrafilter.mp (continuous_quotient_mk.Tendsto g) _ this 
      by 
        rwa [show «expr⟦ ⟧» g = «expr⟦ ⟧» (pure x) from Quotientₓ.sound$ convergent_eqv_pure gx] at this

-- error in Topology.StoneCech: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance stone_cech.t2_space : t2_space (stone_cech α) :=
begin
  rw [expr t2_iff_ultrafilter] [],
  rintros ["⟨", ident x, "⟩", "⟨", ident y, "⟩", ident g, ident gx, ident gy],
  apply [expr quotient.sound],
  intros [ident γ, ident tγ, ident h₁, ident h₂, ident f, ident hf],
  resetI,
  let [ident ff] [] [":=", expr stone_cech_extend hf],
  change [expr «expr = »(ff «expr⟦ ⟧»(x), ff «expr⟦ ⟧»(y))] [] [],
  have [ident lim] [] [":=", expr λ
   (z : ultrafilter α)
   (gz : «expr ≤ »((g : filter (stone_cech α)), expr𝓝() «expr⟦ ⟧»(z))), ((continuous_stone_cech_extend hf).tendsto _).mono_left gz],
  exact [expr tendsto_nhds_unique (lim x gx) (lim y gy)]
end

instance StoneCech.compact_space : CompactSpace (StoneCech α) :=
  Quotientₓ.compact_space

end StoneCech

