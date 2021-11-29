import Mathbin.Topology.Constructions 
import Mathbin.Topology.Algebra.Monoid

/-!
# Topology on lists and vectors

-/


open TopologicalSpace Set Filter

open_locale TopologicalSpace Filter

variable{α : Type _}{β : Type _}[TopologicalSpace α][TopologicalSpace β]

instance  : TopologicalSpace (List α) :=
  TopologicalSpace.mkOfNhds (traverse nhds)

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nhds_list (as : list α) : «expr = »(expr𝓝() as, traverse expr𝓝() as) :=
begin
  refine [expr nhds_mk_of_nhds _ _ _ _],
  { assume [binders (l)],
    induction [expr l] [] [] [],
    case [ident list.nil] { exact [expr le_refl _] },
    case [ident list.cons, ":", ident a, ident l, ident ih] { suffices [] [":", expr «expr ≤ »(«expr <*> »(«expr <$> »(list.cons, pure a), pure l), «expr <*> »(«expr <$> »(list.cons, expr𝓝() a), traverse expr𝓝() l))],
      { simpa [] [] ["only"] ["[", "]"] ["with", ident functor_norm] ["using", expr this] },
      exact [expr filter.seq_mono «expr $ »(filter.map_mono, pure_le_nhds a) ih] } },
  { assume [binders (l s hs)],
    rcases [expr (mem_traverse_iff _ _).1 hs, "with", "⟨", ident u, ",", ident hu, ",", ident hus, "⟩"],
    clear [ident as, ident hs],
    have [] [":", expr «expr∃ , »((v : list (set α)), «expr ∧ »(l.forall₂ (λ
        a s, «expr ∧ »(is_open s, «expr ∈ »(a, s))) v, «expr ⊆ »(sequence v, s)))] [],
    { induction [expr hu] [] [] ["generalizing", ident s],
      case [ident list.forall₂.nil, ":", ident hs, ident this] { existsi ["[", "]"],
        simpa [] [] ["only"] ["[", expr list.forall₂_nil_left_iff, ",", expr exists_eq_left, "]"] [] [] },
      case [ident list.forall₂.cons, ":", ident a, ident s, ident as, ident ss, ident ht, ident h, ident ih, ident t, ident hts] { rcases [expr mem_nhds_iff.1 ht, "with", "⟨", ident u, ",", ident hut, ",", ident hu, "⟩"],
        rcases [expr ih (subset.refl _), "with", "⟨", ident v, ",", ident hv, ",", ident hvss, "⟩"],
        exact [expr ⟨[«expr :: »/«expr :: »/«expr :: »](u, v), list.forall₂.cons hu hv, subset.trans (set.seq_mono (set.image_subset _ hut) hvss) hts⟩] } },
    rcases [expr this, "with", "⟨", ident v, ",", ident hv, ",", ident hvs, "⟩"],
    refine [expr ⟨sequence v, mem_traverse _ _ _, hvs, _⟩],
    { exact [expr hv.imp (assume (a s) ⟨hs, ha⟩, is_open.mem_nhds hs ha)] },
    { assume [binders (u hu)],
      have [ident hu] [] [":=", expr (list.mem_traverse _ _).1 hu],
      have [] [":", expr list.forall₂ (λ a s, «expr ∧ »(is_open s, «expr ∈ »(a, s))) u v] [],
      { refine [expr list.forall₂.flip _],
        replace [ident hv] [] [":=", expr hv.flip],
        simp [] [] ["only"] ["[", expr list.forall₂_and_left, ",", expr flip, "]"] [] ["at", "⊢", ident hv],
        exact [expr ⟨hv.1, hu.flip⟩] },
      refine [expr mem_of_superset _ hvs],
      exact [expr mem_traverse _ _ «expr $ »(this.imp, assume (a s) ⟨hs, ha⟩, is_open.mem_nhds hs ha)] } }
end

@[simp]
theorem nhds_nil : 𝓝 ([] : List α) = pure [] :=
  by 
    rw [nhds_list, List.traverse_nil _] <;> infer_instance

theorem nhds_cons (a : α) (l : List α) : 𝓝 (a :: l) = (List.cons <$> 𝓝 a)<*>𝓝 l :=
  by 
    rw [nhds_list, List.traverse_cons _, ←nhds_list] <;> infer_instance

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem list.tendsto_cons
{a : α}
{l : list α} : tendsto (λ
 p : «expr × »(α, list α), list.cons p.1 p.2) «expr ×ᶠ »(expr𝓝() a, expr𝓝() l) (expr𝓝() [«expr :: »/«expr :: »/«expr :: »](a, l)) :=
by rw ["[", expr nhds_cons, ",", expr tendsto, ",", expr map_prod, "]"] []; exact [expr le_refl _]

theorem Filter.Tendsto.cons {α : Type _} {f : α → β} {g : α → List β} {a : _root_.filter α} {b : β} {l : List β}
  (hf : tendsto f a (𝓝 b)) (hg : tendsto g a (𝓝 l)) : tendsto (fun a => List.cons (f a) (g a)) a (𝓝 (b :: l)) :=
  List.tendsto_cons.comp (tendsto.prod_mk hf hg)

namespace List

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_cons_iff
{β : Type*}
{f : list α → β}
{b : _root_.filter β}
{a : α}
{l : list α} : «expr ↔ »(tendsto f (expr𝓝() [«expr :: »/«expr :: »/«expr :: »](a, l)) b, tendsto (λ
  p : «expr × »(α, list α), f [«expr :: »/«expr :: »/«expr :: »](p.1, p.2)) «expr ×ᶠ »(expr𝓝() a, expr𝓝() l) b) :=
have «expr = »(expr𝓝() [«expr :: »/«expr :: »/«expr :: »](a, l), «expr ×ᶠ »(expr𝓝() a, expr𝓝() l).map (λ
  p : «expr × »(α, list α), [«expr :: »/«expr :: »/«expr :: »](p.1, p.2))), begin
  simp [] [] ["only"] ["[", expr nhds_cons, ",", expr filter.prod_eq, ",", expr (filter.map_def _ _).symm, ",", expr (filter.seq_eq_filter_seq _ _).symm, "]"] [] [],
  simp [] [] [] ["[", "-", ident filter.seq_eq_filter_seq, ",", "-", ident filter.map_def, ",", expr («expr ∘ »), "]"] ["with", ident functor_norm] []
end,
by rw ["[", expr this, ",", expr filter.tendsto_map'_iff, "]"] []

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_cons : continuous (λ
 x : «expr × »(α, list α), ([«expr :: »/«expr :: »/«expr :: »](x.1, x.2) : list α)) :=
«expr $ »(continuous_iff_continuous_at.mpr, λ ⟨x, y⟩, continuous_at_fst.cons continuous_at_snd)

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_nhds
{β : Type*}
{f : list α → β}
{r : list α → _root_.filter β}
(h_nil : tendsto f (pure «expr[ , ]»([])) (r «expr[ , ]»([])))
(h_cons : ∀
 l
 a, tendsto f (expr𝓝() l) (r l) → tendsto (λ
  p : «expr × »(α, list α), f [«expr :: »/«expr :: »/«expr :: »](p.1, p.2)) «expr ×ᶠ »(expr𝓝() a, expr𝓝() l) (r [«expr :: »/«expr :: »/«expr :: »](a, l))) : ∀
l, tendsto f (expr𝓝() l) (r l)
| «expr[ , ]»([]) := by rwa ["[", expr nhds_nil, "]"] []
| [«expr :: »/«expr :: »/«expr :: »](a, l) := by rw ["[", expr tendsto_cons_iff, "]"] []; exact [expr h_cons l a (tendsto_nhds l)]

theorem continuous_at_length : ∀ (l : List α), ContinuousAt List.length l :=
  by 
    simp only [ContinuousAt, nhds_discrete]
    refine' tendsto_nhds _ _
    ·
      exact tendsto_pure_pure _ _
    ·
      intro l a ih 
      dsimp only [List.length]
      refine' tendsto.comp (tendsto_pure_pure (fun x => x+1) _) _ 
      refine' tendsto.comp ih tendsto_snd

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_insert_nth'
{a : α} : ∀
{n : exprℕ()}
{l : list α}, tendsto (λ
 p : «expr × »(α, list α), insert_nth n p.1 p.2) «expr ×ᶠ »(expr𝓝() a, expr𝓝() l) (expr𝓝() (insert_nth n a l))
| 0, l := tendsto_cons
| «expr + »(n, 1), «expr[ , ]»([]) := by simp [] [] [] [] [] []
| «expr + »(n, 1), [«expr :: »/«expr :: »/«expr :: »](a', l) := have «expr = »(«expr ×ᶠ »(expr𝓝() a, expr𝓝() [«expr :: »/«expr :: »/«expr :: »](a', l)), «expr ×ᶠ »(expr𝓝() a, «expr ×ᶠ »(expr𝓝() a', expr𝓝() l)).map (λ
  p : «expr × »(α, «expr × »(α, list α)), (p.1, [«expr :: »/«expr :: »/«expr :: »](p.2.1, p.2.2)))), begin
  simp [] [] ["only"] ["[", expr nhds_cons, ",", expr filter.prod_eq, ",", "<-", expr filter.map_def, ",", "<-", expr filter.seq_eq_filter_seq, "]"] [] [],
  simp [] [] [] ["[", "-", ident filter.seq_eq_filter_seq, ",", "-", ident filter.map_def, ",", expr («expr ∘ »), "]"] ["with", ident functor_norm] []
end,
begin
  rw ["[", expr this, ",", expr tendsto_map'_iff, "]"] [],
  exact [expr (tendsto_fst.comp tendsto_snd).cons «expr $ »((@tendsto_insert_nth' n l).comp, «expr $ »(tendsto_fst.prod_mk, tendsto_snd.comp tendsto_snd))]
end

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_insert_nth
{β}
{n : exprℕ()}
{a : α}
{l : list α}
{f : β → α}
{g : β → list α}
{b : _root_.filter β}
(hf : tendsto f b (expr𝓝() a))
(hg : tendsto g b (expr𝓝() l)) : tendsto (λ b : β, insert_nth n (f b) (g b)) b (expr𝓝() (insert_nth n a l)) :=
tendsto_insert_nth'.comp (tendsto.prod_mk hf hg)

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_insert_nth {n : exprℕ()} : continuous (λ p : «expr × »(α, list α), insert_nth n p.1 p.2) :=
«expr $ »(continuous_iff_continuous_at.mpr, assume
 ⟨a, l⟩, by rw ["[", expr continuous_at, ",", expr nhds_prod_eq, "]"] []; exact [expr tendsto_insert_nth'])

theorem tendsto_remove_nth : ∀ {n : ℕ} {l : List α}, tendsto (fun l => remove_nth l n) (𝓝 l) (𝓝 (remove_nth l n))
| _, [] =>
  by 
    rw [nhds_nil] <;> exact tendsto_pure_nhds _ _
| 0, a :: l =>
  by 
    rw [tendsto_cons_iff] <;> exact tendsto_snd
| n+1, a :: l =>
  by 
    rw [tendsto_cons_iff]
    dsimp [remove_nth]
    exact tendsto_fst.cons ((@tendsto_remove_nth n l).comp tendsto_snd)

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_remove_nth {n : exprℕ()} : continuous (λ l : list α, remove_nth l n) :=
«expr $ »(continuous_iff_continuous_at.mpr, assume a, tendsto_remove_nth)

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem tendsto_prod [monoid α] [has_continuous_mul α] {l : list α} : tendsto list.prod (expr𝓝() l) (expr𝓝() l.prod) :=
begin
  induction [expr l] [] ["with", ident x, ident l, ident ih] [],
  { simp [] [] [] ["[", expr nhds_nil, ",", expr mem_of_mem_nhds, ",", expr tendsto_pure_left, "]"] [] [] { contextual := tt } },
  simp_rw ["[", expr tendsto_cons_iff, ",", expr prod_cons, "]"] [],
  have [] [] [":=", expr continuous_iff_continuous_at.mp continuous_mul (x, l.prod)],
  rw ["[", expr continuous_at, ",", expr nhds_prod_eq, "]"] ["at", ident this],
  exact [expr this.comp (tendsto_id.prod_map ih)]
end

@[toAdditive]
theorem continuous_prod [Monoidₓ α] [HasContinuousMul α] : Continuous (Prod : List α → α) :=
  continuous_iff_continuous_at.mpr$ fun l => tendsto_prod

end List

namespace Vector

open List

instance  (n : ℕ) : TopologicalSpace (Vector α n) :=
  by 
    unfold Vector <;> infer_instance

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_cons
{n : exprℕ()}
{a : α}
{l : vector α n} : tendsto (λ
 p : «expr × »(α, vector α n), «expr ::ᵥ »(p.1, p.2)) «expr ×ᶠ »(expr𝓝() a, expr𝓝() l) (expr𝓝() «expr ::ᵥ »(a, l)) :=
by { simp [] [] [] ["[", expr tendsto_subtype_rng, ",", "<-", expr subtype.val_eq_coe, ",", expr cons_val, "]"] [] [],
  exact [expr tendsto_fst.cons (tendsto.comp continuous_at_subtype_coe tendsto_snd)] }

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_insert_nth
{n : exprℕ()}
{i : fin «expr + »(n, 1)}
{a : α} : ∀
{l : vector α n}, tendsto (λ
 p : «expr × »(α, vector α n), insert_nth p.1 i p.2) «expr ×ᶠ »(expr𝓝() a, expr𝓝() l) (expr𝓝() (insert_nth a i l))
| ⟨l, hl⟩ := begin
  rw ["[", expr insert_nth, ",", expr tendsto_subtype_rng, "]"] [],
  simp [] [] [] ["[", expr insert_nth_val, "]"] [] [],
  exact [expr list.tendsto_insert_nth tendsto_fst (tendsto.comp continuous_at_subtype_coe tendsto_snd : _)]
end

-- error in Topology.List: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_insert_nth'
{n : exprℕ()}
{i : fin «expr + »(n, 1)} : continuous (λ p : «expr × »(α, vector α n), insert_nth p.1 i p.2) :=
«expr $ »(continuous_iff_continuous_at.mpr, assume
 ⟨a, l⟩, by rw ["[", expr continuous_at, ",", expr nhds_prod_eq, "]"] []; exact [expr tendsto_insert_nth])

theorem continuous_insert_nth {n : ℕ} {i : Finₓ (n+1)} {f : β → α} {g : β → Vector α n} (hf : Continuous f)
  (hg : Continuous g) : Continuous fun b => insert_nth (f b) i (g b) :=
  continuous_insert_nth'.comp (hf.prod_mk hg : _)

theorem continuous_at_remove_nth {n : ℕ} {i : Finₓ (n+1)} : ∀ {l : Vector α (n+1)}, ContinuousAt (remove_nth i) l
| ⟨l, hl⟩ =>
  by 
    rw [ContinuousAt, remove_nth, tendsto_subtype_rng]
    simp only [←Subtype.val_eq_coe, Vector.remove_nth_val]
    exact tendsto.comp List.tendsto_remove_nth continuous_at_subtype_coe

theorem continuous_remove_nth {n : ℕ} {i : Finₓ (n+1)} : Continuous (remove_nth i : Vector α (n+1) → Vector α n) :=
  continuous_iff_continuous_at.mpr$ fun ⟨a, l⟩ => continuous_at_remove_nth

end Vector

