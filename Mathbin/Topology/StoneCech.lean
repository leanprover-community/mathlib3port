import Mathbin.Topology.Bases
import Mathbin.Topology.DenseEmbedding

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

Parts of the formalization are based on "Ultrafilters and Topology"
by Marius Stekelenburg, particularly section 5.
-/


noncomputable section

open Filter Set

open_locale TopologicalSpace

universe u v

section Ultrafilter

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [(Command.docComment "/--" " Basis for the topology on `ultrafilter α`. -/")] [] [] [] [] [])
 (Command.def
  "def"
  (Command.declId `UltrafilterBasis [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [`u])] [] ")")]
   [(Term.typeSpec ":" (Term.app `Set [(Term.app `Set [(Term.app `Ultrafilter [`α])])]))])
  (Command.declValSimple
   ":="
   («term_$__»
    `range
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.app `Set [`α]))])]
      "=>"
      (Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}"))))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `range
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.app `Set [`α]))])]
     "=>"
     (Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.app `Set [`α]))])]
    "=>"
    (Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» `s " ∈ " `u)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Basis for the topology on `ultrafilter α`. -/
  def UltrafilterBasis ( α : Type u ) : Set Set Ultrafilter α := range $ fun s : Set α => { u | s ∈ u }

variable {α : Type u}

instance : TopologicalSpace (Ultrafilter α) :=
  TopologicalSpace.generateFrom (UltrafilterBasis α)

theorem ultrafilter_basis_is_basis : TopologicalSpace.IsTopologicalBasis (UltrafilterBasis α) :=
  ⟨by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
    refine' ⟨_, ⟨a ∩ b, rfl⟩, inter_mem ua ub, fun v hv => ⟨_, _⟩⟩ <;>
      apply mem_of_superset hv <;> simp [inter_subset_right a b],
    eq_univ_of_univ_subset $ subset_sUnion_of_mem $ ⟨univ, eq_univ_of_forall fun u => univ_mem⟩, rfl⟩

/--  The basic open sets for the topology on ultrafilters are open. -/
theorem ultrafilter_is_open_basic (s : Set α) : IsOpen { u : Ultrafilter α | s ∈ u } :=
  ultrafilter_basis_is_basis.IsOpen ⟨s, rfl⟩

/--  The basic open sets for the topology on ultrafilters are also closed. -/
theorem ultrafilter_is_closed_basic (s : Set α) : IsClosed { u : Ultrafilter α | s ∈ u } := by
  rw [← is_open_compl_iff]
  convert ultrafilter_is_open_basic (sᶜ)
  ext u
  exact ultrafilter.compl_mem_iff_not_mem.symm

/--  Every ultrafilter `u` on `ultrafilter α` converges to a unique
  point of `ultrafilter α`, namely `mjoin u`. -/
theorem ultrafilter_converges_iff {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α} : ↑u ≤ 𝓝 x ↔ x = mjoin u := by
  rw [eq_comm, ← Ultrafilter.coe_le_coe]
  change ↑u ≤ 𝓝 x ↔ ∀, ∀ s ∈ x, ∀, { v : Ultrafilter α | s ∈ v } ∈ u
  simp only [TopologicalSpace.nhds_generate_from, le_infi_iff, UltrafilterBasis, le_principal_iff, mem_set_of_eq]
  constructor
  ·
    intro h a ha
    exact h _ ⟨ha, a, rfl⟩
  ·
    rintro h a ⟨xi, a, rfl⟩
    exact h _ xi

instance ultrafilter_compact : CompactSpace (Ultrafilter α) :=
  ⟨is_compact_iff_ultrafilter_le_nhds.mpr $ fun f _ => ⟨mjoin f, trivialₓ, ultrafilter_converges_iff.mpr rfl⟩⟩

instance Ultrafilter.t2_space : T2Space (Ultrafilter α) :=
  t2_iff_ultrafilter.mpr $ fun x y f fx fy =>
    have hx : x = mjoin f := ultrafilter_converges_iff.mp fx
    have hy : y = mjoin f := ultrafilter_converges_iff.mp fy
    hx.trans hy.symm

instance : TotallyDisconnectedSpace (Ultrafilter α) := by
  rw [totally_disconnected_space_iff_connected_component_singleton]
  intro A
  simp only [Set.eq_singleton_iff_unique_mem, mem_connected_component, true_andₓ]
  intro B hB
  rw [← Ultrafilter.coe_le_coe]
  intro s hs
  rw [connected_component_eq_Inter_clopen, Set.mem_Inter] at hB
  let Z := { F : Ultrafilter α | s ∈ F }
  have hZ : IsClopen Z := ⟨ultrafilter_is_open_basic s, ultrafilter_is_closed_basic s⟩
  exact hB ⟨Z, hZ, hs⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `ultrafilter_comap_pure_nhds [])
  (Command.declSig
   [(Term.explicitBinder "(" [`b] [":" (Term.app `Ultrafilter [`α])] [] ")")]
   (Term.typeSpec ":" («term_≤_» (Term.app `comap [`pure (Term.app (Topology.Basic.term𝓝 "𝓝") [`b])]) "≤" `b)))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `TopologicalSpace.nhds_generate_from)] "]") [])
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `comap_infi) "," (Tactic.simpLemma [] [] `comap_principal)] "]"]
         [])
        [])
       (group (Tactic.intro "intro" [`s `hs]) [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `le_principal_iff)] "]") []) [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app `infi_le_of_le [(Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}") (Term.hole "_")]))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `infi_le_of_le
          [(Term.anonymousCtor "⟨" [`hs "," (Term.anonymousCtor "⟨" [`s "," `rfl] "⟩")] "⟩") (Term.hole "_")]))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj `principal_mono "." (fieldIdx "2"))
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" `id))]))
        [])])))
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
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `TopologicalSpace.nhds_generate_from)] "]") [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `comap_infi) "," (Tactic.simpLemma [] [] `comap_principal)] "]"]
        [])
       [])
      (group (Tactic.intro "intro" [`s `hs]) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `le_principal_iff)] "]") []) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app `infi_le_of_le [(Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}") (Term.hole "_")]))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `infi_le_of_le
         [(Term.anonymousCtor "⟨" [`hs "," (Term.anonymousCtor "⟨" [`s "," `rfl] "⟩")] "⟩") (Term.hole "_")]))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj `principal_mono "." (fieldIdx "2"))
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" `id))]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.proj `principal_mono "." (fieldIdx "2"))
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" `id))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `principal_mono "." (fieldIdx "2"))
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" `id))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" `id))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `principal_mono "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `principal_mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `infi_le_of_le
    [(Term.anonymousCtor "⟨" [`hs "," (Term.anonymousCtor "⟨" [`s "," `rfl] "⟩")] "⟩") (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `infi_le_of_le
   [(Term.anonymousCtor "⟨" [`hs "," (Term.anonymousCtor "⟨" [`s "," `rfl] "⟩")] "⟩") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.anonymousCtor "⟨" [`hs "," (Term.anonymousCtor "⟨" [`s "," `rfl] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`s "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `infi_le_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app `infi_le_of_le [(Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}") (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `infi_le_of_le [(Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}» "{" `u "|" (Init.Core.«term_∈_» `s " ∈ " `u) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» `s " ∈ " `u)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
theorem
  ultrafilter_comap_pure_nhds
  ( b : Ultrafilter α ) : comap pure 𝓝 b ≤ b
  :=
    by
      rw [ TopologicalSpace.nhds_generate_from ]
        simp only [ comap_infi , comap_principal ]
        intro s hs
        rw [ ← le_principal_iff ]
        refine' infi_le_of_le { u | s ∈ u } _
        refine' infi_le_of_le ⟨ hs , ⟨ s , rfl ⟩ ⟩ _
        exact principal_mono . 2 fun a => id

section Embedding

theorem ultrafilter_pure_injective : Function.Injective (pure : α → Ultrafilter α) := by
  intro x y h
  have : {x} ∈ (pure x : Ultrafilter α) := singleton_mem_pure
  rw [h] at this
  exact (mem_singleton_iff.mp (mem_pure.mp this)).symm

open TopologicalSpace

/--  The range of `pure : α → ultrafilter α` is dense in `ultrafilter α`. -/
theorem dense_range_pure : DenseRange (pure : α → Ultrafilter α) := fun x =>
  mem_closure_iff_ultrafilter.mpr ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pureₓ x).symm⟩

/--  The map `pure : α → ultra_filter α` induces on `α` the discrete topology. -/
theorem induced_topology_pure : TopologicalSpace.induced (pure : α → Ultrafilter α) Ultrafilter.topologicalSpace = ⊥ :=
  by
  apply eq_bot_of_singletons_open
  intro x
  use { u : Ultrafilter α | {x} ∈ u }, ultrafilter_is_open_basic _
  simp

/--  `pure : α → ultrafilter α` defines a dense inducing of `α` in `ultrafilter α`. -/
theorem dense_inducing_pure : @DenseInducing _ _ ⊥ _ (pure : α → Ultrafilter α) := by
  let this' : TopologicalSpace α := ⊥ <;> exact ⟨⟨induced_topology_pure.symm⟩, dense_range_pure⟩

/--  `pure : α → ultrafilter α` defines a dense embedding of `α` in `ultrafilter α`. -/
theorem dense_embedding_pure : @DenseEmbedding _ _ ⊥ _ (pure : α → Ultrafilter α) := by
  let this' : TopologicalSpace α := ⊥ <;> exact { dense_inducing_pure with inj := ultrafilter_pure_injective }

end Embedding

section Extension

variable {γ : Type _} [TopologicalSpace γ]

/--  The extension of a function `α → γ` to a function `ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous. -/
def Ultrafilter.extend (f : α → γ) : Ultrafilter α → γ := by
  let this' : TopologicalSpace α := ⊥ <;> exact dense_inducing_pure.extend f

variable [T2Space γ]

theorem ultrafilter_extend_extends (f : α → γ) : (Ultrafilter.extend f ∘ pure) = f := by
  let this' : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  exact funext (dense_inducing_pure.extend_eq continuous_of_discrete_topology)

variable [CompactSpace γ]

theorem continuous_ultrafilter_extend (f : α → γ) : Continuous (Ultrafilter.extend f) :=
  have : ∀ b : Ultrafilter α, ∃ c, tendsto f (comap pure (𝓝 b)) (𝓝 c) := fun b =>
    let ⟨c, _, h⟩ :=
      compact_univ.ultrafilter_le_nhds (b.map f)
        (by
          rw [le_principal_iff] <;> exact univ_mem)
    ⟨c, le_transₓ (map_mono (ultrafilter_comap_pure_nhds _)) h⟩
  by
  let this' : TopologicalSpace α := ⊥
  have : NormalSpace γ := normal_of_compact_t2
  exact dense_inducing_pure.continuous_extend this

/--  The value of `ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`. -/
theorem ultrafilter_extend_eq_iff {f : α → γ} {b : Ultrafilter α} {c : γ} :
    Ultrafilter.extend f b = c ↔ ↑b.map f ≤ 𝓝 c :=
  ⟨fun h => by
    let b' : Ultrafilter (Ultrafilter α) := b.map pure
    have t : ↑b' ≤ 𝓝 b
    exact ultrafilter_converges_iff.mpr (bind_pureₓ _).symm
    rw [← h]
    have := (continuous_ultrafilter_extend f).Tendsto b
    refine' le_transₓ _ (le_transₓ (map_mono t) this)
    change _ ≤ map (Ultrafilter.extend f ∘ pure) (↑b)
    rw [ultrafilter_extend_extends]
    exact le_reflₓ _, fun h => by
    let this' : TopologicalSpace α := ⊥ <;>
      exact dense_inducing_pure.extend_eq_of_tendsto (le_transₓ (map_mono (ultrafilter_comap_pure_nhds _)) h)⟩

end Extension

end Ultrafilter

section StoneCech

variable (α : Type u) [TopologicalSpace α]

-- failed to format: format: uncaught backtrack exception
instance
  stoneCechSetoid
  : Setoidₓ ( Ultrafilter α )
  where
    R
        x y
        :=
        ∀
          γ : Type u [ TopologicalSpace γ ]
          ,
          by
            exact
              ∀
                [ T2Space γ ] [ CompactSpace γ ] f : α → γ hf : Continuous f
                ,
                Ultrafilter.extend f x = Ultrafilter.extend f y
      iseqv
        :=
        ⟨
          fun x γ tγ h₁ h₂ f hf => rfl
            ,
            fun x y xy γ tγ h₁ h₂ f hf => by exact ( xy γ f hf ) . symm
            ,
            fun x y z xy yz γ tγ h₁ h₂ f hf => by exact ( xy γ f hf ) . trans ( yz γ f hf )
          ⟩

/--  The Stone-Čech compactification of a topological space. -/
def StoneCech : Type u :=
  Quotientₓ (stoneCechSetoid α)

variable {α}

instance : TopologicalSpace (StoneCech α) := by
  unfold StoneCech <;> infer_instance

instance [Inhabited α] : Inhabited (StoneCech α) := by
  unfold StoneCech <;> infer_instance

/--  The natural map from α to its Stone-Čech compactification. -/
def stoneCechUnit (x : α) : StoneCech α :=
  ⟦pure x⟧

/--  The image of stone_cech_unit is dense. (But stone_cech_unit need
  not be an embedding, for example if α is not Hausdorff.) -/
theorem dense_range_stone_cech_unit : DenseRange (stoneCechUnit : α → StoneCech α) :=
  dense_range_pure.Quotient

section Extension

variable {γ : Type u} [TopologicalSpace γ] [T2Space γ] [CompactSpace γ]

variable {f : α → γ} (hf : Continuous f)

attribute [local elab_with_expected_type] Quotientₓ.lift

/--  The extension of a continuous function from α to a compact
  Hausdorff space γ to the Stone-Čech compactification of α. -/
def stoneCechExtend : StoneCech α → γ :=
  Quotientₓ.lift (Ultrafilter.extend f) fun x y xy => xy γ f hf

theorem stone_cech_extend_extends : (stoneCechExtend hf ∘ stoneCechUnit) = f :=
  ultrafilter_extend_extends f

theorem continuous_stone_cech_extend : Continuous (stoneCechExtend hf) :=
  continuous_quot_lift _ (continuous_ultrafilter_extend f)

end Extension

theorem convergent_eqv_pure {u : Ultrafilter α} {x : α} (ux : ↑u ≤ 𝓝 x) : u ≈ pure x := fun γ tγ h₁ h₂ f hf => by
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
  continuous_iff_ultrafilter.mpr $ fun x g gx =>
    have : ↑g.map pure ≤ 𝓝 g := by
      rw [ultrafilter_converges_iff] <;> exact (bind_pureₓ _).symm
    have : (g.map stoneCechUnit : Filter (StoneCech α)) ≤ 𝓝 (⟦g⟧) :=
      continuous_at_iff_ultrafilter.mp (continuous_quotient_mk.Tendsto g) _ this
    by
    rwa [show ⟦g⟧ = ⟦pure x⟧ from Quotientₓ.sound $ convergent_eqv_pure gx] at this

instance StoneCech.t2_space : T2Space (StoneCech α) := by
  rw [t2_iff_ultrafilter]
  rintro ⟨x⟩ ⟨y⟩ g gx gy
  apply Quotientₓ.sound
  intro γ tγ h₁ h₂ f hf
  skip
  let ff := stoneCechExtend hf
  change ff (⟦x⟧) = ff (⟦y⟧)
  have lim := fun z : Ultrafilter α gz : (g : Filter (StoneCech α)) ≤ 𝓝 (⟦z⟧) =>
    ((continuous_stone_cech_extend hf).Tendsto _).mono_left gz
  exact tendsto_nhds_unique (limₓ x gx) (limₓ y gy)

instance StoneCech.compact_space : CompactSpace (StoneCech α) :=
  Quotientₓ.compact_space

end StoneCech

