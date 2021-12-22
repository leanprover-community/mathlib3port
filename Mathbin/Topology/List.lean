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

theorem nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as := by
  refine' nhds_mk_of_nhds _ _ _ _
  ·
    intro l
    induction l
    case list.nil =>
      exact le_reflₓ _
    case list.cons a l ih =>
      suffices ((List.cons <$> pure a)<*>pure l) ≤ (List.cons <$> 𝓝 a)<*>traverse 𝓝 l by
        simpa only with functor_norm using this
      exact Filter.seq_mono (Filter.map_mono $ pure_le_nhds a) ih
  ·
    intro l s hs
    rcases(mem_traverse_iff _ _).1 hs with ⟨u, hu, hus⟩
    clear as hs
    have : ∃ v : List (Set α), l.forall₂ (fun a s => IsOpen s ∧ a ∈ s) v ∧ sequence v ⊆ s := by
      induction hu generalizing s
      case list.forall₂.nil hs this =>
        exists
        simpa only [List.forall₂_nil_left_iff, exists_eq_left]
      case list.forall₂.cons a s as ss ht h ih t hts =>
        rcases mem_nhds_iff.1 ht with ⟨u, hut, hu⟩
        rcases ih (subset.refl _) with ⟨v, hv, hvss⟩
        exact ⟨u :: v, List.Forall₂.cons hu hv, subset.trans (Set.seq_mono (Set.image_subset _ hut) hvss) hts⟩
    rcases this with ⟨v, hv, hvs⟩
    refine' ⟨sequence v, mem_traverse _ _ _, hvs, _⟩
    ·
      exact hv.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha
    ·
      intro u hu
      have hu := (List.mem_traverse _ _).1 hu
      have : List.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) u v := by
        refine' List.Forall₂.flip _
        replace hv := hv.flip
        simp only [List.forall₂_and_left, flip] at hv⊢
        exact ⟨hv.1, hu.flip⟩
      refine' mem_of_superset _ hvs
      exact mem_traverse _ _ (this.imp $ fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha)

@[simp]
theorem nhds_nil : 𝓝 ([] : List α) = pure [] := by
  rw [nhds_list, List.traverse_nil _] <;> infer_instance

theorem nhds_cons (a : α) (l : List α) : 𝓝 (a :: l) = (List.cons <$> 𝓝 a)<*>𝓝 l := by
  rw [nhds_list, List.traverse_cons _, ← nhds_list] <;> infer_instance

theorem List.tendsto_cons {a : α} {l : List α} :
    tendsto (fun p : α × List α => List.cons p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a :: l)) := by
  rw [nhds_cons, tendsto, map_prod] <;> exact le_reflₓ _

theorem Filter.Tendsto.cons {α : Type _} {f : α → β} {g : α → List β} {a : _root_.filter α} {b : β} {l : List β}
    (hf : tendsto f a (𝓝 b)) (hg : tendsto g a (𝓝 l)) : tendsto (fun a => List.cons (f a) (g a)) a (𝓝 (b :: l)) :=
  List.tendsto_cons.comp (tendsto.prod_mk hf hg)

namespace List

theorem tendsto_cons_iff {β : Type _} {f : List α → β} {b : _root_.filter β} {a : α} {l : List α} :
    tendsto f (𝓝 (a :: l)) b ↔ tendsto (fun p : α × List α => f (p.1 :: p.2)) (𝓝 a ×ᶠ 𝓝 l) b :=
  have : 𝓝 (a :: l) = (𝓝 a ×ᶠ 𝓝 l).map fun p : α × List α => p.1 :: p.2 := by
    simp only [nhds_cons, Filter.prod_eq, (Filter.map_def _ _).symm, (Filter.seq_eq_filter_seq _ _).symm]
    simp' [-Filter.seq_eq_filter_seq, -Filter.map_def, · ∘ ·] with functor_norm
  by
  rw [this, Filter.tendsto_map'_iff]

theorem continuous_cons : Continuous fun x : α × List α => (x.1 :: x.2 : List α) :=
  continuous_iff_continuous_at.mpr $ fun ⟨x, y⟩ => continuous_at_fst.cons continuous_at_snd

theorem tendsto_nhds {β : Type _} {f : List α → β} {r : List α → _root_.filter β} (h_nil : tendsto f (pure []) (r []))
    (h_cons : ∀ l a, tendsto f (𝓝 l) (r l) → tendsto (fun p : α × List α => f (p.1 :: p.2)) (𝓝 a ×ᶠ 𝓝 l) (r (a :: l))) :
    ∀ l, tendsto f (𝓝 l) (r l)
  | [] => by
    rwa [nhds_nil]
  | a :: l => by
    rw [tendsto_cons_iff] <;> exact h_cons l a (tendsto_nhds l)

theorem continuous_at_length : ∀ l : List α, ContinuousAt List.length l := by
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
  | n+1, [] => by
    simp
  | n+1, a' :: l =>
    have : 𝓝 a ×ᶠ 𝓝 (a' :: l) = (𝓝 a ×ᶠ (𝓝 a' ×ᶠ 𝓝 l)).map fun p : α × α × List α => (p.1, p.2.1 :: p.2.2) := by
      simp only [nhds_cons, Filter.prod_eq, ← Filter.map_def, ← Filter.seq_eq_filter_seq]
      simp' [-Filter.seq_eq_filter_seq, -Filter.map_def, · ∘ ·] with functor_norm
    by
    rw [this, tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insert_nth' n l).comp $ tendsto_fst.prod_mk $ tendsto_snd.comp tendsto_snd)

theorem tendsto_insert_nth {β} {n : ℕ} {a : α} {l : List α} {f : β → α} {g : β → List α} {b : _root_.filter β}
    (hf : tendsto f b (𝓝 a)) (hg : tendsto g b (𝓝 l)) :
    tendsto (fun b : β => insert_nth n (f b) (g b)) b (𝓝 (insert_nth n a l)) :=
  tendsto_insert_nth'.comp (tendsto.prod_mk hf hg)

theorem continuous_insert_nth {n : ℕ} : Continuous fun p : α × List α => insert_nth n p.1 p.2 :=
  continuous_iff_continuous_at.mpr $ fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq] <;> exact tendsto_insert_nth'

theorem tendsto_remove_nth : ∀ {n : ℕ} {l : List α}, tendsto (fun l => remove_nth l n) (𝓝 l) (𝓝 (remove_nth l n))
  | _, [] => by
    rw [nhds_nil] <;> exact tendsto_pure_nhds _ _
  | 0, a :: l => by
    rw [tendsto_cons_iff] <;> exact tendsto_snd
  | n+1, a :: l => by
    rw [tendsto_cons_iff]
    dsimp [remove_nth]
    exact tendsto_fst.cons ((@tendsto_remove_nth n l).comp tendsto_snd)

theorem continuous_remove_nth {n : ℕ} : Continuous fun l : List α => remove_nth l n :=
  continuous_iff_continuous_at.mpr $ fun a => tendsto_remove_nth

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.toAdditive "to_additive" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `tendsto_prod [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `Monoidₓ [`α]) "]")
    (Term.instBinder "[" [] (Term.app `HasContinuousMul [`α]) "]")
    (Term.implicitBinder "{" [`l] [":" (Term.app `List [`α])] "}")]
   (Term.typeSpec
    ":"
    (Term.app
     `tendsto
     [`List.prod (Term.app (Topology.Basic.term𝓝 "𝓝") [`l]) (Term.app (Topology.Basic.term𝓝 "𝓝") [`l.prod])])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.induction'
         "induction'"
         [(Tactic.casesTarget [] `l)]
         []
         ["with" [(Lean.binderIdent `x) (Lean.binderIdent `l) (Lean.binderIdent `ih)]]
         [])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              ["("
               "config"
               ":="
               (Term.structInst
                "{"
                []
                [(group
                  (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                  [])]
                (Term.optEllipsis [])
                []
                "}")
               ")"]
              []
              ["["
               [(Tactic.simpLemma [] [] `nhds_nil)
                ","
                (Tactic.simpLemma [] [] `mem_of_mem_nhds)
                ","
                (Tactic.simpLemma [] [] `tendsto_pure_left)]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.simpRw
         "simp_rw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_cons_iff) "," (Tactic.rwRule [] `prod_cons)] "]")
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           []
           ":="
           (Term.app
            `continuous_iff_continuous_at.mp
            [`continuous_mul (Term.paren "(" [`x [(Term.tupleTail "," [`l.prod])]] ")")]))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ContinuousAt) "," (Tactic.rwRule [] `nhds_prod_eq)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        [])
       (group (Tactic.exact "exact" (Term.app `this.comp [(Term.app `tendsto_id.prod_map [`ih])])) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.induction'
        "induction'"
        [(Tactic.casesTarget [] `l)]
        []
        ["with" [(Lean.binderIdent `x) (Lean.binderIdent `l) (Lean.binderIdent `ih)]]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             ["("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                 [])]
               (Term.optEllipsis [])
               []
               "}")
              ")"]
             []
             ["["
              [(Tactic.simpLemma [] [] `nhds_nil)
               ","
               (Tactic.simpLemma [] [] `mem_of_mem_nhds)
               ","
               (Tactic.simpLemma [] [] `tendsto_pure_left)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_cons_iff) "," (Tactic.rwRule [] `prod_cons)] "]")
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          []
          ":="
          (Term.app
           `continuous_iff_continuous_at.mp
           [`continuous_mul (Term.paren "(" [`x [(Term.tupleTail "," [`l.prod])]] ")")]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ContinuousAt) "," (Tactic.rwRule [] `nhds_prod_eq)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])
      (group (Tactic.exact "exact" (Term.app `this.comp [(Term.app `tendsto_id.prod_map [`ih])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `this.comp [(Term.app `tendsto_id.prod_map [`ih])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `this.comp [(Term.app `tendsto_id.prod_map [`ih])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `tendsto_id.prod_map [`ih])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ih
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tendsto_id.prod_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `tendsto_id.prod_map [`ih]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this.comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ContinuousAt) "," (Tactic.rwRule [] `nhds_prod_eq)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nhds_prod_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousAt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     []
     ":="
     (Term.app
      `continuous_iff_continuous_at.mp
      [`continuous_mul (Term.paren "(" [`x [(Term.tupleTail "," [`l.prod])]] ")")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `continuous_iff_continuous_at.mp
   [`continuous_mul (Term.paren "(" [`x [(Term.tupleTail "," [`l.prod])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`x [(Term.tupleTail "," [`l.prod])]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l.prod
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `continuous_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_iff_continuous_at.mp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simpRw
   "simp_rw"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_cons_iff) "," (Tactic.rwRule [] `prod_cons)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `prod_cons
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tendsto_cons_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        ["("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
          (Term.optEllipsis [])
          []
          "}")
         ")"]
        []
        ["["
         [(Tactic.simpLemma [] [] `nhds_nil)
          ","
          (Tactic.simpLemma [] [] `mem_of_mem_nhds)
          ","
          (Tactic.simpLemma [] [] `tendsto_pure_left)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   []
   ["["
    [(Tactic.simpLemma [] [] `nhds_nil)
     ","
     (Tactic.simpLemma [] [] `mem_of_mem_nhds)
     ","
     (Tactic.simpLemma [] [] `tendsto_pure_left)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tendsto_pure_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_of_mem_nhds
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nhds_nil
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  theorem
    tendsto_prod
    [ Monoidₓ α ] [ HasContinuousMul α ] { l : List α } : tendsto List.prod 𝓝 l 𝓝 l.prod
    :=
      by
        induction' l with x l ih
          ·
            simp
              ( config := { contextual := Bool.true._@._internal._hyg.0 } )
              [ nhds_nil , mem_of_mem_nhds , tendsto_pure_left ]
          simp_rw [ tendsto_cons_iff , prod_cons ]
          have := continuous_iff_continuous_at.mp continuous_mul ( x , l.prod )
          rw [ ContinuousAt , nhds_prod_eq ] at this
          exact this.comp tendsto_id.prod_map ih

@[to_additive]
theorem continuous_prod [Monoidₓ α] [HasContinuousMul α] : Continuous (Prod : List α → α) :=
  continuous_iff_continuous_at.mpr $ fun l => tendsto_prod

end List

namespace Vector

open List

instance (n : ℕ) : TopologicalSpace (Vector α n) := by
  unfold Vector <;> infer_instance

theorem tendsto_cons {n : ℕ} {a : α} {l : Vector α n} :
    tendsto (fun p : α × Vector α n => p.1::ᵥp.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a::ᵥl)) := by
  simp [tendsto_subtype_rng, ← Subtype.val_eq_coe, cons_val]
  exact tendsto_fst.cons (tendsto.comp continuous_at_subtype_coe tendsto_snd)

theorem tendsto_insert_nth {n : ℕ} {i : Finₓ (n+1)} {a : α} :
    ∀ {l : Vector α n}, tendsto (fun p : α × Vector α n => insert_nth p.1 i p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insert_nth a i l))
  | ⟨l, hl⟩ => by
    rw [insert_nth, tendsto_subtype_rng]
    simp [insert_nth_val]
    exact List.tendsto_insert_nth tendsto_fst (tendsto.comp continuous_at_subtype_coe tendsto_snd : _)

theorem continuous_insert_nth' {n : ℕ} {i : Finₓ (n+1)} : Continuous fun p : α × Vector α n => insert_nth p.1 i p.2 :=
  continuous_iff_continuous_at.mpr $ fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq] <;> exact tendsto_insert_nth

theorem continuous_insert_nth {n : ℕ} {i : Finₓ (n+1)} {f : β → α} {g : β → Vector α n} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => insert_nth (f b) i (g b) :=
  continuous_insert_nth'.comp (hf.prod_mk hg : _)

theorem continuous_at_remove_nth {n : ℕ} {i : Finₓ (n+1)} : ∀ {l : Vector α (n+1)}, ContinuousAt (remove_nth i) l
  | ⟨l, hl⟩ => by
    rw [ContinuousAt, remove_nth, tendsto_subtype_rng]
    simp only [← Subtype.val_eq_coe, Vector.remove_nth_val]
    exact tendsto.comp List.tendsto_remove_nth continuous_at_subtype_coe

theorem continuous_remove_nth {n : ℕ} {i : Finₓ (n+1)} : Continuous (remove_nth i : Vector α (n+1) → Vector α n) :=
  continuous_iff_continuous_at.mpr $ fun ⟨a, l⟩ => continuous_at_remove_nth

end Vector

