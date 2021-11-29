import Mathbin.Topology.Constructions 
import Mathbin.Topology.Algebra.Monoid

/-!
# Topology on lists and vectors

-/


open TopologicalSpace Set Filter

open_locale TopologicalSpace Filter

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

instance : TopologicalSpace (List α) :=
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

theorem List.tendsto_cons {a : α} {l : List α} :
  tendsto (fun p : α × List α => List.cons p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a :: l)) :=
  by 
    rw [nhds_cons, tendsto, map_prod] <;> exact le_reflₓ _

theorem Filter.Tendsto.cons {α : Type _} {f : α → β} {g : α → List β} {a : _root_.filter α} {b : β} {l : List β}
  (hf : tendsto f a (𝓝 b)) (hg : tendsto g a (𝓝 l)) : tendsto (fun a => List.cons (f a) (g a)) a (𝓝 (b :: l)) :=
  List.tendsto_cons.comp (tendsto.prod_mk hf hg)

namespace List

theorem tendsto_cons_iff {β : Type _} {f : List α → β} {b : _root_.filter β} {a : α} {l : List α} :
  tendsto f (𝓝 (a :: l)) b ↔ tendsto (fun p : α × List α => f (p.1 :: p.2)) (𝓝 a ×ᶠ 𝓝 l) b :=
  have  : 𝓝 (a :: l) = (𝓝 a ×ᶠ 𝓝 l).map fun p : α × List α => p.1 :: p.2 :=
    by 
      simp only [nhds_cons, Filter.prod_eq, (Filter.map_def _ _).symm, (Filter.seq_eq_filter_seq _ _).symm]
      simp' [-Filter.seq_eq_filter_seq, -Filter.map_def, · ∘ ·] with functor_norm 
  by 
    rw [this, Filter.tendsto_map'_iff]

theorem continuous_cons : Continuous fun x : α × List α => (x.1 :: x.2 : List α) :=
  continuous_iff_continuous_at.mpr$ fun ⟨x, y⟩ => continuous_at_fst.cons continuous_at_snd

theorem tendsto_nhds {β : Type _} {f : List α → β} {r : List α → _root_.filter β} (h_nil : tendsto f (pure []) (r []))
  (h_cons : ∀ l a, tendsto f (𝓝 l) (r l) → tendsto (fun p : α × List α => f (p.1 :: p.2)) (𝓝 a ×ᶠ 𝓝 l) (r (a :: l))) :
  ∀ l, tendsto f (𝓝 l) (r l)
| [] =>
  by 
    rwa [nhds_nil]
| a :: l =>
  by 
    rw [tendsto_cons_iff] <;> exact h_cons l a (tendsto_nhds l)

theorem continuous_at_length : ∀ l : List α, ContinuousAt List.length l :=
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

theorem tendsto_insert_nth' {a : α} :
  ∀ {n : ℕ} {l : List α}, tendsto (fun p : α × List α => insert_nth n p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insert_nth n a l))
| 0, l => tendsto_cons
| n+1, [] =>
  by 
    simp 
| n+1, a' :: l =>
  have  : 𝓝 a ×ᶠ 𝓝 (a' :: l) = (𝓝 a ×ᶠ (𝓝 a' ×ᶠ 𝓝 l)).map fun p : α × α × List α => (p.1, p.2.1 :: p.2.2) :=
    by 
      simp only [nhds_cons, Filter.prod_eq, ←Filter.map_def, ←Filter.seq_eq_filter_seq]
      simp' [-Filter.seq_eq_filter_seq, -Filter.map_def, · ∘ ·] with functor_norm 
  by 
    rw [this, tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insert_nth' n l).comp$ tendsto_fst.prod_mk$ tendsto_snd.comp tendsto_snd)

theorem tendsto_insert_nth {β} {n : ℕ} {a : α} {l : List α} {f : β → α} {g : β → List α} {b : _root_.filter β}
  (hf : tendsto f b (𝓝 a)) (hg : tendsto g b (𝓝 l)) :
  tendsto (fun b : β => insert_nth n (f b) (g b)) b (𝓝 (insert_nth n a l)) :=
  tendsto_insert_nth'.comp (tendsto.prod_mk hf hg)

theorem continuous_insert_nth {n : ℕ} : Continuous fun p : α × List α => insert_nth n p.1 p.2 :=
  continuous_iff_continuous_at.mpr$
    fun ⟨a, l⟩ =>
      by 
        rw [ContinuousAt, nhds_prod_eq] <;> exact tendsto_insert_nth'

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

theorem continuous_remove_nth {n : ℕ} : Continuous fun l : List α => remove_nth l n :=
  continuous_iff_continuous_at.mpr$ fun a => tendsto_remove_nth

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

instance (n : ℕ) : TopologicalSpace (Vector α n) :=
  by 
    unfold Vector <;> infer_instance

theorem tendsto_cons {n : ℕ} {a : α} {l : Vector α n} :
  tendsto (fun p : α × Vector α n => p.1::ᵥp.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a::ᵥl)) :=
  by 
    simp [tendsto_subtype_rng, ←Subtype.val_eq_coe, cons_val]
    exact tendsto_fst.cons (tendsto.comp continuous_at_subtype_coe tendsto_snd)

theorem tendsto_insert_nth {n : ℕ} {i : Finₓ (n+1)} {a : α} :
  ∀ {l : Vector α n}, tendsto (fun p : α × Vector α n => insert_nth p.1 i p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insert_nth a i l))
| ⟨l, hl⟩ =>
  by 
    rw [insert_nth, tendsto_subtype_rng]
    simp [insert_nth_val]
    exact List.tendsto_insert_nth tendsto_fst (tendsto.comp continuous_at_subtype_coe tendsto_snd : _)

theorem continuous_insert_nth' {n : ℕ} {i : Finₓ (n+1)} : Continuous fun p : α × Vector α n => insert_nth p.1 i p.2 :=
  continuous_iff_continuous_at.mpr$
    fun ⟨a, l⟩ =>
      by 
        rw [ContinuousAt, nhds_prod_eq] <;> exact tendsto_insert_nth

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

