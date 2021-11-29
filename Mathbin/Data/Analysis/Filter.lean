import Mathbin.Order.Filter.Cofinite

open Set Filter

/-- A `cfilter α σ` is a realization of a filter (base) on `α`,
  represented by a type `σ` together with operations for the top element and
  the binary inf operation. -/
structure Cfilter(α σ : Type _)[PartialOrderₓ α] where 
  f : σ → α 
  pt : σ 
  inf : σ → σ → σ 
  inf_le_left : ∀ (a b : σ), f (inf a b) ≤ f a 
  inf_le_right : ∀ (a b : σ), f (inf a b) ≤ f b

variable{α : Type _}{β : Type _}{σ : Type _}{τ : Type _}

namespace Cfilter

section 

variable[PartialOrderₓ α](F : Cfilter α σ)

instance  : CoeFun (Cfilter α σ) fun _ => σ → α :=
  ⟨Cfilter.f⟩

@[simp]
theorem coe_mk f pt inf h₁ h₂ a : (@Cfilter.mk α σ _ f pt inf h₁ h₂) a = f a :=
  rfl

/-- Map a cfilter to an equivalent representation type. -/
def of_equiv (E : σ ≃ τ) : Cfilter α σ → Cfilter α τ
| ⟨f, p, g, h₁, h₂⟩ =>
  { f := fun a => f (E.symm a), pt := E p, inf := fun a b => E (g (E.symm a) (E.symm b)),
    inf_le_left :=
      fun a b =>
        by 
          simpa using h₁ (E.symm a) (E.symm b),
    inf_le_right :=
      fun a b =>
        by 
          simpa using h₂ (E.symm a) (E.symm b) }

@[simp]
theorem of_equiv_val (E : σ ≃ τ) (F : Cfilter α σ) (a : τ) : F.of_equiv E a = F (E.symm a) :=
  by 
    cases F <;> rfl

end 

/-- The filter represented by a `cfilter` is the collection of supersets of
  elements of the filter base. -/
def to_filter (F : Cfilter (Set α) σ) : Filter α :=
  { Sets := { a | ∃ b, F b ⊆ a }, univ_sets := ⟨F.pt, subset_univ _⟩,
    sets_of_superset := fun x y ⟨b, h⟩ s => ⟨b, subset.trans h s⟩,
    inter_sets :=
      fun x y ⟨a, h₁⟩ ⟨b, h₂⟩ =>
        ⟨F.inf a b, subset_inter (subset.trans (F.inf_le_left _ _) h₁) (subset.trans (F.inf_le_right _ _) h₂)⟩ }

@[simp]
theorem mem_to_filter_sets (F : Cfilter (Set α) σ) {a : Set α} : a ∈ F.to_filter ↔ ∃ b, F b ⊆ a :=
  Iff.rfl

end Cfilter

/-- A realizer for filter `f` is a cfilter which generates `f`. -/
structure Filter.Realizer(f : Filter α) where 
  σ : Type _ 
  f : Cfilter (Set α) σ 
  Eq : F.to_filter = f

protected def Cfilter.toRealizer (F : Cfilter (Set α) σ) : F.to_filter.realizer :=
  ⟨σ, F, rfl⟩

namespace Filter.Realizer

theorem mem_sets {f : Filter α} (F : f.realizer) {a : Set α} : a ∈ f ↔ ∃ b, F.F b ⊆ a :=
  by 
    cases F <;> subst f <;> simp 

def of_eq {f g : Filter α} (e : f = g) (F : f.realizer) : g.realizer :=
  ⟨F.σ, F.F, F.eq.trans e⟩

/-- A filter realizes itself. -/
def of_filter (f : Filter α) : f.realizer :=
  ⟨f.sets,
    { f := Subtype.val, pt := ⟨univ, univ_mem⟩, inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => ⟨_, inter_mem h₁ h₂⟩,
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => inter_subset_left x y,
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => inter_subset_right x y },
    filter_eq$ Set.ext$ fun x => SetCoe.exists.trans exists_mem_subset_iff⟩

/-- Transfer a filter realizer to another realizer on a different base type. -/
def of_equiv {f : Filter α} (F : f.realizer) (E : F.σ ≃ τ) : f.realizer :=
  ⟨τ, F.F.of_equiv E,
    by 
      refine' Eq.trans _ F.eq <;>
        exact
          filter_eq
            (Set.ext$
              fun x =>
                ⟨fun ⟨s, h⟩ =>
                    ⟨E.symm s,
                      by 
                        simpa using h⟩,
                  fun ⟨t, h⟩ =>
                    ⟨E t,
                      by 
                        simp [h]⟩⟩)⟩

@[simp]
theorem of_equiv_σ {f : Filter α} (F : f.realizer) (E : F.σ ≃ τ) : (F.of_equiv E).σ = τ :=
  rfl

@[simp]
theorem of_equiv_F {f : Filter α} (F : f.realizer) (E : F.σ ≃ τ) (s : τ) : (F.of_equiv E).f s = F.F (E.symm s) :=
  by 
    delta' of_equiv <;> simp 

/-- `unit` is a realizer for the principal filter -/
protected def principal (s : Set α) : (principal s).Realizer :=
  ⟨Unit,
    { f := fun _ => s, pt := (), inf := fun _ _ => (), inf_le_left := fun _ _ => le_reflₓ _,
      inf_le_right := fun _ _ => le_reflₓ _ },
    filter_eq$ Set.ext$ fun x => ⟨fun ⟨_, s⟩ => s, fun h => ⟨(), h⟩⟩⟩

@[simp]
theorem principal_σ (s : Set α) : (realizer.principal s).σ = Unit :=
  rfl

@[simp]
theorem principal_F (s : Set α) (u : Unit) : (realizer.principal s).f u = s :=
  rfl

/-- `unit` is a realizer for the top filter -/
protected def top : (⊤ : Filter α).Realizer :=
  (realizer.principal _).of_eq principal_univ

@[simp]
theorem top_σ : (@realizer.top α).σ = Unit :=
  rfl

@[simp]
theorem top_F (u : Unit) : (@realizer.top α).f u = univ :=
  rfl

/-- `unit` is a realizer for the bottom filter -/
protected def bot : (⊥ : Filter α).Realizer :=
  (realizer.principal _).of_eq principal_empty

@[simp]
theorem bot_σ : (@realizer.bot α).σ = Unit :=
  rfl

@[simp]
theorem bot_F (u : Unit) : (@realizer.bot α).f u = ∅ :=
  rfl

/-- Construct a realizer for `map m f` given a realizer for `f` -/
protected def map (m : α → β) {f : Filter α} (F : f.realizer) : (map m f).Realizer :=
  ⟨F.σ,
    { f := fun s => image m (F.F s), pt := F.F.pt, inf := F.F.inf,
      inf_le_left := fun a b => image_subset _ (F.F.inf_le_left _ _),
      inf_le_right := fun a b => image_subset _ (F.F.inf_le_right _ _) },
    filter_eq$
      Set.ext$
        fun x =>
          by 
            simp [Cfilter.toFilter] <;> rw [F.mem_sets] <;> rfl⟩

@[simp]
theorem map_σ (m : α → β) {f : Filter α} (F : f.realizer) : (F.map m).σ = F.σ :=
  rfl

@[simp]
theorem map_F (m : α → β) {f : Filter α} (F : f.realizer) s : (F.map m).f s = image m (F.F s) :=
  rfl

/-- Construct a realizer for `comap m f` given a realizer for `f` -/
protected def comap (m : α → β) {f : Filter β} (F : f.realizer) : (comap m f).Realizer :=
  ⟨F.σ,
    { f := fun s => preimage m (F.F s), pt := F.F.pt, inf := F.F.inf,
      inf_le_left := fun a b => preimage_mono (F.F.inf_le_left _ _),
      inf_le_right := fun a b => preimage_mono (F.F.inf_le_right _ _) },
    filter_eq$
      Set.ext$
        fun x =>
          by 
            cases F <;>
              subst f <;>
                simp [Cfilter.toFilter, mem_comap] <;>
                  exact
                    ⟨fun ⟨s, h⟩ => ⟨_, ⟨s, subset.refl _⟩, h⟩,
                      fun ⟨y, ⟨s, h⟩, h₂⟩ => ⟨s, subset.trans (preimage_mono h) h₂⟩⟩⟩

/-- Construct a realizer for the sup of two filters -/
protected def sup {f g : Filter α} (F : f.realizer) (G : g.realizer) : (f⊔g).Realizer :=
  ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.F s ∪ G.F t, pt := (F.F.pt, G.F.pt),
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.F.inf a b, G.F.inf a' b'),
      inf_le_left := fun ⟨a, a'⟩ ⟨b, b'⟩ => union_subset_union (F.F.inf_le_left _ _) (G.F.inf_le_left _ _),
      inf_le_right := fun ⟨a, a'⟩ ⟨b, b'⟩ => union_subset_union (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
    filter_eq$
      Set.ext$
        fun x =>
          by 
            cases F <;>
              cases G <;>
                substs f g <;>
                  simp [Cfilter.toFilter] <;>
                    exact
                      ⟨fun ⟨s, t, h⟩ =>
                          ⟨⟨s, subset.trans (subset_union_left _ _) h⟩, ⟨t, subset.trans (subset_union_right _ _) h⟩⟩,
                        fun ⟨⟨s, h₁⟩, ⟨t, h₂⟩⟩ => ⟨s, t, union_subset h₁ h₂⟩⟩⟩

/-- Construct a realizer for the inf of two filters -/
protected def inf {f g : Filter α} (F : f.realizer) (G : g.realizer) : (f⊓g).Realizer :=
  ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.F s ∩ G.F t, pt := (F.F.pt, G.F.pt),
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.F.inf a b, G.F.inf a' b'),
      inf_le_left := fun ⟨a, a'⟩ ⟨b, b'⟩ => inter_subset_inter (F.F.inf_le_left _ _) (G.F.inf_le_left _ _),
      inf_le_right := fun ⟨a, a'⟩ ⟨b, b'⟩ => inter_subset_inter (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
    by 
      ext x 
      cases F <;> cases G <;> substs f g <;> simp [Cfilter.toFilter]
      split 
      ·
        rintro ⟨s : F_σ, t : G_σ, h⟩
        apply mem_inf_of_inter _ _ h 
        use s 
        use t
      ·
        rintro ⟨s, ⟨a, ha⟩, t, ⟨b, hb⟩, rfl⟩
        exact ⟨a, b, inter_subset_inter ha hb⟩⟩

-- error in Data.Analysis.Filter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Construct a realizer for the cofinite filter -/ protected def cofinite [decidable_eq α] : (@cofinite α).realizer :=
⟨finset α, { f := λ s, {a | «expr ∉ »(a, s)},
   pt := «expr∅»(),
   inf := («expr ∪ »),
   inf_le_left := λ s t a, mt (finset.mem_union_left _),
   inf_le_right := λ
   s
   t
   a, mt (finset.mem_union_right _) }, «expr $ »(filter_eq, «expr $ »(set.ext, λ
   x, ⟨λ
    ⟨s, h⟩, s.finite_to_set.subset (compl_subset_comm.1 h), λ
    ⟨fs⟩, by exactI [expr ⟨«expr ᶜ»(x).to_finset, λ
      (a)
      (h : «expr ∉ »(a, «expr ᶜ»(x).to_finset)), «expr $ »(classical.by_contradiction, λ
       h', h (mem_to_finset.2 h'))⟩]⟩))⟩

-- error in Data.Analysis.Filter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Construct a realizer for filter bind -/
protected
def bind {f : filter α} {m : α → filter β} (F : f.realizer) (G : ∀ i, (m i).realizer) : (f.bind m).realizer :=
⟨«exprΣ , »((s : F.σ), ∀
  i «expr ∈ » F.F s, (G i).σ), { f := λ ⟨s, f⟩, «expr⋃ , »((i «expr ∈ » F.F s), (G i).F (f i H)),
   pt := ⟨F.F.pt, λ i H, (G i).F.pt⟩,
   inf := λ
   ⟨a, f⟩
   ⟨b, f'⟩, ⟨F.F.inf a b, λ i h, (G i).F.inf (f i (F.F.inf_le_left _ _ h)) (f' i (F.F.inf_le_right _ _ h))⟩,
   inf_le_left := λ
   ⟨a, f⟩
   ⟨b, f'⟩
   (x), show «expr ∈ »(x, «expr⋃ , »((i : α)
     (H : «expr ∈ »(i, F.F (F.F.inf a b))), _)) → «expr ∈ »(x, «expr⋃ , »((i)
     (H : «expr ∈ »(i, F.F a)), (G i).F (f i H))), by simp [] [] [] [] [] []; exact [expr λ
    i h₁ h₂, ⟨i, F.F.inf_le_left _ _ h₁, (G i).F.inf_le_left _ _ h₂⟩],
   inf_le_right := λ
   ⟨a, f⟩
   ⟨b, f'⟩
   (x), show «expr ∈ »(x, «expr⋃ , »((i : α)
     (H : «expr ∈ »(i, F.F (F.F.inf a b))), _)) → «expr ∈ »(x, «expr⋃ , »((i)
     (H : «expr ∈ »(i, F.F b)), (G i).F (f' i H))), by simp [] [] [] [] [] []; exact [expr λ
    i
    h₁
    h₂, ⟨i, F.F.inf_le_right _ _ h₁, (G i).F.inf_le_right _ _ h₂⟩] }, «expr $ »(filter_eq, «expr $ »(set.ext, λ
   x, by cases [expr F] ["with", "_", ident F, "_"]; subst [expr f]; simp [] [] [] ["[", expr cfilter.to_filter, ",", expr mem_bind, "]"] [] []; exact [expr ⟨λ
     ⟨s, f, h⟩, ⟨F s, ⟨s, subset.refl _⟩, λ
      i
      H, (G i).mem_sets.2 ⟨f i H, λ
       a
       h', h ⟨_, ⟨i, rfl⟩, _, ⟨H, rfl⟩, h'⟩⟩⟩, λ
     ⟨y, ⟨s, h⟩, f⟩, let ⟨f', h'⟩ := classical.axiom_of_choice (λ i : F s, (G i).mem_sets.1 (f i (h i.2))) in
     ⟨s, λ i h, f' ⟨i, h⟩, λ (a) ⟨_, ⟨i, rfl⟩, _, ⟨H, rfl⟩, m⟩, h' ⟨_, H⟩ m⟩⟩]))⟩

/-- Construct a realizer for indexed supremum -/
protected def Sup {f : α → Filter β} (F : ∀ i, (f i).Realizer) : (⨆i, f i).Realizer :=
  let F' : (⨆i, f i).Realizer :=
    (realizer.bind realizer.top F).of_eq$
      filter_eq$
        Set.ext$
          by 
            simp [Filter.bind, eq_univ_iff_forall, supr_sets_eq]
  F'.of_equiv$
    show (Σu : Unit, ∀ (i : α), True → (F i).σ) ≃ ∀ i, (F i).σ from
      ⟨fun ⟨_, f⟩ i => f i ⟨⟩, fun f => ⟨(), fun i _ => f i⟩,
        fun ⟨⟨⟩, f⟩ =>
          by 
            dsimp <;> congr <;> simp ,
        fun f => rfl⟩

/-- Construct a realizer for the product of filters -/
protected def Prod {f g : Filter α} (F : f.realizer) (G : g.realizer) : (f.prod g).Realizer :=
  (F.comap _).inf (G.comap _)

theorem le_iff {f g : Filter α} (F : f.realizer) (G : g.realizer) : f ≤ g ↔ ∀ (b : G.σ), ∃ a : F.σ, F.F a ≤ G.F b :=
  ⟨fun H t => F.mem_sets.1 (H (G.mem_sets.2 ⟨t, subset.refl _⟩)),
    fun H x h =>
      F.mem_sets.2$
        let ⟨s, h₁⟩ := G.mem_sets.1 h 
        let ⟨t, h₂⟩ := H s
        ⟨t, subset.trans h₂ h₁⟩⟩

theorem tendsto_iff (f : α → β) {l₁ : Filter α} {l₂ : Filter β} (L₁ : l₁.realizer) (L₂ : l₂.realizer) :
  tendsto f l₁ l₂ ↔ ∀ b, ∃ a, ∀ x (_ : x ∈ L₁.F a), f x ∈ L₂.F b :=
  (le_iff (L₁.map f) L₂).trans$ forall_congrₓ$ fun b => exists_congr$ fun a => image_subset_iff

theorem ne_bot_iff {f : Filter α} (F : f.realizer) : f ≠ ⊥ ↔ ∀ (a : F.σ), (F.F a).Nonempty :=
  by 
    classical 
    rw [not_iff_comm, ←le_bot_iff, F.le_iff realizer.bot, not_forall]
    simp only [Set.not_nonempty_iff_eq_empty]
    exact
      ⟨fun ⟨x, e⟩ _ => ⟨x, le_of_eqₓ e⟩,
        fun h =>
          let ⟨x, h⟩ := h ()
          ⟨x, le_bot_iff.1 h⟩⟩

end Filter.Realizer

