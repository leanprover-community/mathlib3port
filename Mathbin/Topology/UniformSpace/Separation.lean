import Mathbin.Tactic.ApplyFun
import Mathbin.Data.Set.Pairwise
import Mathbin.Topology.UniformSpace.Basic
import Mathbin.Topology.Separation

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is regular (T₃), hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `separation_quotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `separation_quotient X`.
As usual, this allows to turn `separation_quotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separation_relation X : set (X × X)`: the separation relation
* `separated_space X`: a predicate class asserting that `X` is separated
* `is_separated s`: a predicate asserting that `s : set X` is separated
* `separation_quotient X`: the maximal separated quotient of `X`.
* `separation_quotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `separation_quotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `separation_quotient.uniform_continuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `separation_quotient.uniform_continuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separation_setoid` is not declared as a global instance.
It is made a local instance while building the theory of `separation_quotient`.
The factored map `separation_quotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/


open Filter TopologicalSpace Set Classical Function UniformSpace

open_locale Classical TopologicalSpace uniformity Filter

noncomputable section

-- ././Mathport/Syntax/Translate/Basic.lean:169:9: warning: unsupported option eqn_compiler.zeta
set_option eqn_compiler.zeta true

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-!
### Separated uniform spaces
-/


/--  The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def SeparationRel (α : Type u) [u : UniformSpace α] :=
  ⋂₀(𝓤 α).Sets

localized [uniformity] notation "𝓢" => SeparationRel

theorem separated_equiv : Equivalenceₓ fun x y => (x, y) ∈ 𝓢 α :=
  ⟨fun x => fun s => refl_mem_uniformity, fun x y => fun h s : Set (α × α) hs =>
    have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
    h _ this,
    fun x y z hxy : (x, y) ∈ 𝓢 α hyz : (y, z) ∈ 𝓢 α s hs : s ∈ 𝓤 α =>
    let ⟨t, ht, (h_ts : CompRel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs
    h_ts $ show (x, z) ∈ CompRel t t from ⟨y, hxy t ht, hyz t ht⟩⟩

/--  A uniform space is separated if its separation relation is trivial (each point
is related only to itself). -/
class SeparatedSpace (α : Type u) [UniformSpace α] : Prop where
  out : 𝓢 α = IdRel

theorem separated_space_iff {α : Type u} [UniformSpace α] : SeparatedSpace α ↔ 𝓢 α = IdRel :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem separated_def {α : Type u} [UniformSpace α] : SeparatedSpace α ↔ ∀ x y, (∀, ∀ r ∈ 𝓤 α, ∀, (x, y) ∈ r) → x = y :=
  by
  simp [separated_space_iff, id_rel_subset.2 separated_equiv.1, subset.antisymm_iff] <;>
    simp [subset_def, SeparationRel]

theorem separated_def' {α : Type u} [UniformSpace α] : SeparatedSpace α ↔ ∀ x y, x ≠ y → ∃ r ∈ 𝓤 α, (x, y) ∉ r :=
  separated_def.trans $
    forall_congrₓ $ fun x =>
      forall_congrₓ $ fun y => by
        rw [← not_imp_not] <;> simp [not_forall]

theorem eq_of_uniformity {α : Type _} [UniformSpace α] [SeparatedSpace α] {x y : α} (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) :
    x = y :=
  separated_def.mp ‹SeparatedSpace α› x y fun _ => h

theorem eq_of_uniformity_basis {α : Type _} [UniformSpace α] [SeparatedSpace α] {ι : Type _} {p : ι → Prop}
    {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α} (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  eq_of_uniformity fun V V_in =>
    let ⟨i, hi, H⟩ := hs.mem_iff.mp V_in
    H (h hi)

theorem eq_of_forall_symmetric {α : Type _} [UniformSpace α] [SeparatedSpace α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis has_basis_symmetric
    (by
      simpa [and_imp] using fun _ => h)

theorem id_rel_sub_separation_relation (α : Type _) [UniformSpace α] : IdRel ⊆ 𝓢 α := by
  unfold SeparationRel
  rw [id_rel_subset]
  intro x
  suffices ∀, ∀ t ∈ 𝓤 α, ∀, (x, x) ∈ t by
    simpa only [refl_mem_uniformity]
  exact fun t => refl_mem_uniformity

theorem separation_rel_comap {f : α → β} (h : ‹UniformSpace α› = UniformSpace.comap f ‹UniformSpace β›) :
    𝓢 α = Prod.map f f ⁻¹' 𝓢 β := by
  dsimp [SeparationRel]
  simp_rw [uniformity_comap h, (Filter.comap_has_basis (Prod.map f f) (𝓤 β)).sInter_sets, ← preimage_Inter,
    sInter_eq_bInter]
  rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Filter.HasBasis.separation_rel [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.sort "Sort" [(Level.hole "_")])] "}")
    (Term.implicitBinder "{" [`p] [":" (Term.arrow `ι "→" (Term.prop "Prop"))] "}")
    (Term.implicitBinder "{" [`s] [":" (Term.arrow `ι "→" (Term.app `Set [(«term_×_» `α "×" `α)]))] "}")
    (Term.explicitBinder
     "("
     [`h]
     [":" (Term.app `has_basis [(Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]) `p `s])]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app (Topology.UniformSpace.Separation.term𝓢 "𝓢") [`α])
     "="
     (Set.Data.Set.Lattice.«term⋂_,_»
      "⋂"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hi)] ":" (Term.app `p [`i]) ")")])
      ", "
      (Term.app `s [`i])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.unfold "unfold" [] [`SeparationRel] []) [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h.sInter_sets)] "]") []) [])])))
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
     [(group (Tactic.unfold "unfold" [] [`SeparationRel] []) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h.sInter_sets)] "]") []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h.sInter_sets)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h.sInter_sets
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.unfold "unfold" [] [`SeparationRel] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.unfold', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app (Topology.UniformSpace.Separation.term𝓢 "𝓢") [`α])
   "="
   (Set.Data.Set.Lattice.«term⋂_,_»
    "⋂"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hi)] ":" (Term.app `p [`i]) ")")])
    ", "
    (Term.app `s [`i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋂_,_»
   "⋂"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hi)] ":" (Term.app `p [`i]) ")")])
   ", "
   (Term.app `s [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `s [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
protected
  theorem
    Filter.HasBasis.separation_rel
    { ι : Sort _ } { p : ι → Prop } { s : ι → Set α × α } ( h : has_basis 𝓤 α p s )
      : 𝓢 α = ⋂ ( i : _ ) ( hi : p i ) , s i
    := by unfold SeparationRel rw [ h.sInter_sets ]

theorem separation_rel_eq_inter_closure : 𝓢 α = ⋂₀(Closure '' (𝓤 α).Sets) := by
  simp [uniformity_has_basis_closure.separation_rel]

theorem is_closed_separation_rel : IsClosed (𝓢 α) := by
  rw [separation_rel_eq_inter_closure]
  apply is_closed_sInter
  rintro _ ⟨t, t_in, rfl⟩
  exact is_closed_closure

theorem separated_iff_t2 : SeparatedSpace α ↔ T2Space α := by
  classical
  constructor <;> intro h
  ·
    rw [t2_iff_is_closed_diagonal, ← show 𝓢 α = diagonal α from h.1]
    exact is_closed_separation_rel
  ·
    rw [separated_def']
    intro x y hxy
    rcases t2_separation hxy with ⟨u, v, uo, vo, hx, hy, h⟩
    rcases is_open_iff_ball_subset.1 uo x hx with ⟨r, hrU, hr⟩
    exact ⟨r, hrU, fun H => disjoint_iff.2 h ⟨hr H, hy⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (d' «expr ∈ » expr𝓤() α)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.instance
  (Term.attrKind [])
  "instance"
  [(Command.namedPrio "(" "priority" ":=" (numLit "100") ")")]
  [(Command.declId `separated_regular [])]
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `SeparatedSpace [`α]) "]")]
   (Term.typeSpec ":" (Term.app `RegularSpace [`α])))
  (Command.declValSimple
   ":="
   (Term.structInst
    "{"
    [[(Term.app
       (Term.explicit "@" `T2Space.t1_space)
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app (Term.proj `separated_iff_t2 "." `mp) [(«term‹_›» "‹" (Term.hole "_") "›")])])]
     "with"]
    [(group
      (Term.structInstField
       (Term.structInstLVal `t0 [])
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl [] [] ":=" (Term.app `separated_iff_t2.mp [(«term‹_›» "‹" (Term.hole "_") "›")]))))
            [])
           (group (Tactic.exact "exact" `t1_space.t0_space.t0) [])]))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `regular [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`s `a `hs `ha] [])]
         "=>"
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              (Init.Core.«term_∈_»
               (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")
               " ∈ "
               (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
            ":="
            (Term.app `IsOpen.mem_nhds [`hs.is_open_compl `ha])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Init.Core.«term_∈_»
                (Set.«term{_|_}»
                 "{"
                 (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
                 "|"
                 (Term.arrow
                  («term_=_» (Term.proj `p "." (fieldIdx "1")) "=" `a)
                  "→"
                  (Init.Core.«term_∈_» (Term.proj `p "." (fieldIdx "2")) " ∈ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))
                 "}")
                " ∈ "
                (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α])))]
             ":="
             (Term.app (Term.proj `mem_nhds_uniformity_iff_right "." `mp) [`this])))
           []
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`d "," `hd "," `h] "⟩")
              []
              []
              ":="
              (Term.app `comp_mem_uniformity_sets [`this])))
            []
            (Term.let
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `e
               []
               []
               ":="
               (Set.«term{_|_}»
                "{"
                (Mathlib.ExtendedBinder.extBinder `y [":" `α])
                "|"
                (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`y])]] ")") " ∈ " `d)
                "}")))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hae []]
                [(Term.typeSpec ":" (Init.Core.«term_∈_» `a " ∈ " (Term.app `Closure [`e])))]
                ":="
                («term_$__» `subset_closure "$" (Term.app `refl_mem_uniformity [`hd]))))
              []
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   (Init.Core.«term_⊆_»
                    (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
                    " ⊆ "
                    (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
                        "]")
                       [])
                      [])
                     (group
                      (Tactic.change
                       "change"
                       («term_≤_»
                        (Order.CompleteLattice.«term⨅_,_»
                         "⨅"
                         (Lean.explicitBinders
                          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
                           (Lean.bracketedExplicitBinders
                            "("
                            [(Lean.binderIdent "_")]
                            ":"
                            (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                            ")")])
                         ", "
                         (Term.hole "_"))
                        "≤"
                        (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
                       [])
                      [])
                     (group
                      (Tactic.exact
                       "exact"
                       («term_$__»
                        (Term.app `infi_le_of_le [`d])
                        "$"
                        («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
                      [])])))))
               []
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`e_subset []]
                  [(Term.typeSpec
                    ":"
                    (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`a' `ha'] [])]
                    "=>"
                    (Term.let
                     "let"
                     (Term.letDecl
                      (Term.letPatDecl
                       (Term.anonymousCtor
                        "⟨"
                        [`x
                         ","
                         (Term.paren
                          "("
                          [`hx
                           [(Term.typeAscription
                             ":"
                             (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
                          ")")
                         ","
                         `y
                         ","
                         (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
                         ","
                         (Term.paren
                          "("
                          [`hy
                           [(Term.typeAscription
                             ":"
                             (Init.Core.«term_∈_»
                              (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")")
                              " ∈ "
                              `d))]]
                          ")")]
                        "⟩")
                       []
                       []
                       ":="
                       (Term.app
                        (Term.explicit "@" `this)
                        [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
                     []
                     (Term.have
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec
                          ":"
                          (Init.Core.«term_∈_»
                           (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
                           " ∈ "
                           (Term.app `CompRel [`d `d])))]
                        ":="
                        (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
                      []
                      (Term.app `h [`this `rfl])))))))
                []
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
                   ":="
                   (Term.app
                    (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
                    [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
                 []
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Order.Lattice.«term_⊓_»
                        (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
                        "⊓"
                        (Term.app
                         (Filter.Order.Filter.Basic.term𝓟 "𝓟")
                         [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
                       "="
                       (Order.BoundedOrder.«term⊥» "⊥")))]
                    ":="
                    (Term.app
                     (Term.proj
                      (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
                      "."
                      (fieldIdx "2"))
                     [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
                  []
                  (Term.anonymousCtor
                   "⟨"
                   [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
                    ","
                    (Term.proj `is_closed_closure "." `is_open_compl)
                    ","
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`x `h₁ `h₂] [])]
                      "=>"
                      (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
                    ","
                    `this]
                   "⟩")))))))))))))
      [])]
    (Term.optEllipsis [])
    []
    "}")
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   [[(Term.app
      (Term.explicit "@" `T2Space.t1_space)
      [(Term.hole "_")
       (Term.hole "_")
       (Term.app (Term.proj `separated_iff_t2 "." `mp) [(«term‹_›» "‹" (Term.hole "_") "›")])])]
    "with"]
   [(group
     (Term.structInstField
      (Term.structInstLVal `t0 [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl [] [] ":=" (Term.app `separated_iff_t2.mp [(«term‹_›» "‹" (Term.hole "_") "›")]))))
           [])
          (group (Tactic.exact "exact" `t1_space.t0_space.t0) [])]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `regular [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`s `a `hs `ha] [])]
        "=>"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_»
              (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")
              " ∈ "
              (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
           ":="
           (Term.app `IsOpen.mem_nhds [`hs.is_open_compl `ha])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              (Init.Core.«term_∈_»
               (Set.«term{_|_}»
                "{"
                (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
                "|"
                (Term.arrow
                 («term_=_» (Term.proj `p "." (fieldIdx "1")) "=" `a)
                 "→"
                 (Init.Core.«term_∈_» (Term.proj `p "." (fieldIdx "2")) " ∈ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))
                "}")
               " ∈ "
               (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α])))]
            ":="
            (Term.app (Term.proj `mem_nhds_uniformity_iff_right "." `mp) [`this])))
          []
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`d "," `hd "," `h] "⟩")
             []
             []
             ":="
             (Term.app `comp_mem_uniformity_sets [`this])))
           []
           (Term.let
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `e
              []
              []
              ":="
              (Set.«term{_|_}»
               "{"
               (Mathlib.ExtendedBinder.extBinder `y [":" `α])
               "|"
               (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`y])]] ")") " ∈ " `d)
               "}")))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hae []]
               [(Term.typeSpec ":" (Init.Core.«term_∈_» `a " ∈ " (Term.app `Closure [`e])))]
               ":="
               («term_$__» `subset_closure "$" (Term.app `refl_mem_uniformity [`hd]))))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Init.Core.«term_⊆_»
                   (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
                   " ⊆ "
                   (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
                       "]")
                      [])
                     [])
                    (group
                     (Tactic.change
                      "change"
                      («term_≤_»
                       (Order.CompleteLattice.«term⨅_,_»
                        "⨅"
                        (Lean.explicitBinders
                         [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
                          (Lean.bracketedExplicitBinders
                           "("
                           [(Lean.binderIdent "_")]
                           ":"
                           (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                           ")")])
                        ", "
                        (Term.hole "_"))
                       "≤"
                       (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
                      [])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      («term_$__»
                       (Term.app `infi_le_of_le [`d])
                       "$"
                       («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
                     [])])))))
              []
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`e_subset []]
                 [(Term.typeSpec
                   ":"
                   (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`a' `ha'] [])]
                   "=>"
                   (Term.let
                    "let"
                    (Term.letDecl
                     (Term.letPatDecl
                      (Term.anonymousCtor
                       "⟨"
                       [`x
                        ","
                        (Term.paren
                         "("
                         [`hx
                          [(Term.typeAscription
                            ":"
                            (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
                         ")")
                        ","
                        `y
                        ","
                        (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
                        ","
                        (Term.paren
                         "("
                         [`hy
                          [(Term.typeAscription
                            ":"
                            (Init.Core.«term_∈_»
                             (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")")
                             " ∈ "
                             `d))]]
                         ")")]
                       "⟩")
                      []
                      []
                      ":="
                      (Term.app
                       (Term.explicit "@" `this)
                       [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
                    []
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         (Init.Core.«term_∈_»
                          (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
                          " ∈ "
                          (Term.app `CompRel [`d `d])))]
                       ":="
                       (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
                     []
                     (Term.app `h [`this `rfl])))))))
               []
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
                  ":="
                  (Term.app
                   (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
                   [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
                []
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Order.Lattice.«term_⊓_»
                       (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
                       "⊓"
                       (Term.app
                        (Filter.Order.Filter.Basic.term𝓟 "𝓟")
                        [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
                      "="
                      (Order.BoundedOrder.«term⊥» "⊥")))]
                   ":="
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
                     "."
                     (fieldIdx "2"))
                    [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
                 []
                 (Term.anonymousCtor
                  "⟨"
                  [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
                   ","
                   (Term.proj `is_closed_closure "." `is_open_compl)
                   ","
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`x `h₁ `h₂] [])]
                     "=>"
                     (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
                   ","
                   `this]
                  "⟩")))))))))))))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`s `a `hs `ha] [])]
    "=>"
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       []
       [(Term.typeSpec
         ":"
         (Init.Core.«term_∈_» (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ") " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
       ":="
       (Term.app `IsOpen.mem_nhds [`hs.is_open_compl `ha])))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        []
        [(Term.typeSpec
          ":"
          (Init.Core.«term_∈_»
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
            "|"
            (Term.arrow
             («term_=_» (Term.proj `p "." (fieldIdx "1")) "=" `a)
             "→"
             (Init.Core.«term_∈_» (Term.proj `p "." (fieldIdx "2")) " ∈ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))
            "}")
           " ∈ "
           (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α])))]
        ":="
        (Term.app (Term.proj `mem_nhds_uniformity_iff_right "." `mp) [`this])))
      []
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`d "," `hd "," `h] "⟩")
         []
         []
         ":="
         (Term.app `comp_mem_uniformity_sets [`this])))
       []
       (Term.let
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `e
          []
          []
          ":="
          (Set.«term{_|_}»
           "{"
           (Mathlib.ExtendedBinder.extBinder `y [":" `α])
           "|"
           (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`y])]] ")") " ∈ " `d)
           "}")))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hae []]
           [(Term.typeSpec ":" (Init.Core.«term_∈_» `a " ∈ " (Term.app `Closure [`e])))]
           ":="
           («term_$__» `subset_closure "$" (Term.app `refl_mem_uniformity [`hd]))))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              (Init.Core.«term_⊆_»
               (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
               " ⊆ "
               (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.change
                  "change"
                  («term_≤_»
                   (Order.CompleteLattice.«term⨅_,_»
                    "⨅"
                    (Lean.explicitBinders
                     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
                      (Lean.bracketedExplicitBinders
                       "("
                       [(Lean.binderIdent "_")]
                       ":"
                       (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                       ")")])
                    ", "
                    (Term.hole "_"))
                   "≤"
                   (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
                  [])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  («term_$__»
                   (Term.app `infi_le_of_le [`d])
                   "$"
                   («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
                 [])])))))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`e_subset []]
             [(Term.typeSpec
               ":"
               (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`a' `ha'] [])]
               "=>"
               (Term.let
                "let"
                (Term.letDecl
                 (Term.letPatDecl
                  (Term.anonymousCtor
                   "⟨"
                   [`x
                    ","
                    (Term.paren
                     "("
                     [`hx
                      [(Term.typeAscription
                        ":"
                        (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
                     ")")
                    ","
                    `y
                    ","
                    (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
                    ","
                    (Term.paren
                     "("
                     [`hy
                      [(Term.typeAscription
                        ":"
                        (Init.Core.«term_∈_»
                         (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")")
                         " ∈ "
                         `d))]]
                     ")")]
                   "⟩")
                  []
                  []
                  ":="
                  (Term.app
                   (Term.explicit "@" `this)
                   [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
                []
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     (Init.Core.«term_∈_»
                      (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
                      " ∈ "
                      (Term.app `CompRel [`d `d])))]
                   ":="
                   (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
                 []
                 (Term.app `h [`this `rfl])))))))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
              ":="
              (Term.app
               (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
               [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Order.Lattice.«term_⊓_»
                   (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
                   "⊓"
                   (Term.app
                    (Filter.Order.Filter.Basic.term𝓟 "𝓟")
                    [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
                  "="
                  (Order.BoundedOrder.«term⊥» "⊥")))]
               ":="
               (Term.app
                (Term.proj
                 (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
                 "."
                 (fieldIdx "2"))
                [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
             []
             (Term.anonymousCtor
              "⟨"
              [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
               ","
               (Term.proj `is_closed_closure "." `is_open_compl)
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`x `h₁ `h₂] [])]
                 "=>"
                 (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
               ","
               `this]
              "⟩"))))))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∈_» (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ") " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
     ":="
     (Term.app `IsOpen.mem_nhds [`hs.is_open_compl `ha])))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec
        ":"
        (Init.Core.«term_∈_»
         (Set.«term{_|_}»
          "{"
          (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
          "|"
          (Term.arrow
           («term_=_» (Term.proj `p "." (fieldIdx "1")) "=" `a)
           "→"
           (Init.Core.«term_∈_» (Term.proj `p "." (fieldIdx "2")) " ∈ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))
          "}")
         " ∈ "
         (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α])))]
      ":="
      (Term.app (Term.proj `mem_nhds_uniformity_iff_right "." `mp) [`this])))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor "⟨" [`d "," `hd "," `h] "⟩")
       []
       []
       ":="
       (Term.app `comp_mem_uniformity_sets [`this])))
     []
     (Term.let
      "let"
      (Term.letDecl
       (Term.letIdDecl
        `e
        []
        []
        ":="
        (Set.«term{_|_}»
         "{"
         (Mathlib.ExtendedBinder.extBinder `y [":" `α])
         "|"
         (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`y])]] ")") " ∈ " `d)
         "}")))
      []
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hae []]
         [(Term.typeSpec ":" (Init.Core.«term_∈_» `a " ∈ " (Term.app `Closure [`e])))]
         ":="
         («term_$__» `subset_closure "$" (Term.app `refl_mem_uniformity [`hd]))))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Init.Core.«term_⊆_»
             (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
             " ⊆ "
             (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
                 "]")
                [])
               [])
              (group
               (Tactic.change
                "change"
                («term_≤_»
                 (Order.CompleteLattice.«term⨅_,_»
                  "⨅"
                  (Lean.explicitBinders
                   [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
                    (Lean.bracketedExplicitBinders
                     "("
                     [(Lean.binderIdent "_")]
                     ":"
                     (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                     ")")])
                  ", "
                  (Term.hole "_"))
                 "≤"
                 (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                («term_$__»
                 (Term.app `infi_le_of_le [`d])
                 "$"
                 («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
               [])])))))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`e_subset []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`a' `ha'] [])]
             "=>"
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor
                 "⟨"
                 [`x
                  ","
                  (Term.paren
                   "("
                   [`hx
                    [(Term.typeAscription
                      ":"
                      (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
                   ")")
                  ","
                  `y
                  ","
                  (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
                  ","
                  (Term.paren
                   "("
                   [`hy
                    [(Term.typeAscription
                      ":"
                      (Init.Core.«term_∈_»
                       (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")")
                       " ∈ "
                       `d))]]
                   ")")]
                 "⟩")
                []
                []
                ":="
                (Term.app
                 (Term.explicit "@" `this)
                 [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
              []
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   (Init.Core.«term_∈_»
                    (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
                    " ∈ "
                    (Term.app `CompRel [`d `d])))]
                 ":="
                 (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
               []
               (Term.app `h [`this `rfl])))))))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
            ":="
            (Term.app
             (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
             [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Order.Lattice.«term_⊓_»
                 (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
                 "⊓"
                 (Term.app
                  (Filter.Order.Filter.Basic.term𝓟 "𝓟")
                  [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
                "="
                (Order.BoundedOrder.«term⊥» "⊥")))]
             ":="
             (Term.app
              (Term.proj
               (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
               "."
               (fieldIdx "2"))
              [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
           []
           (Term.anonymousCtor
            "⟨"
            [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
             ","
             (Term.proj `is_closed_closure "." `is_open_compl)
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x `h₁ `h₂] [])]
               "=>"
               (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
             ","
             `this]
            "⟩"))))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∈_»
        (Set.«term{_|_}»
         "{"
         (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
         "|"
         (Term.arrow
          («term_=_» (Term.proj `p "." (fieldIdx "1")) "=" `a)
          "→"
          (Init.Core.«term_∈_» (Term.proj `p "." (fieldIdx "2")) " ∈ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))
         "}")
        " ∈ "
        (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α])))]
     ":="
     (Term.app (Term.proj `mem_nhds_uniformity_iff_right "." `mp) [`this])))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letPatDecl
      (Term.anonymousCtor "⟨" [`d "," `hd "," `h] "⟩")
      []
      []
      ":="
      (Term.app `comp_mem_uniformity_sets [`this])))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letIdDecl
       `e
       []
       []
       ":="
       (Set.«term{_|_}»
        "{"
        (Mathlib.ExtendedBinder.extBinder `y [":" `α])
        "|"
        (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`y])]] ")") " ∈ " `d)
        "}")))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`hae []]
        [(Term.typeSpec ":" (Init.Core.«term_∈_» `a " ∈ " (Term.app `Closure [`e])))]
        ":="
        («term_$__» `subset_closure "$" (Term.app `refl_mem_uniformity [`hd]))))
      []
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Init.Core.«term_⊆_»
            (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
            " ⊆ "
            (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
                "]")
               [])
              [])
             (group
              (Tactic.change
               "change"
               («term_≤_»
                (Order.CompleteLattice.«term⨅_,_»
                 "⨅"
                 (Lean.explicitBinders
                  [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
                   (Lean.bracketedExplicitBinders
                    "("
                    [(Lean.binderIdent "_")]
                    ":"
                    (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                    ")")])
                 ", "
                 (Term.hole "_"))
                "≤"
                (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
               [])
              [])
             (group
              (Tactic.exact
               "exact"
               («term_$__»
                (Term.app `infi_le_of_le [`d])
                "$"
                («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
              [])])))))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`e_subset []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`a' `ha'] [])]
            "=>"
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor
                "⟨"
                [`x
                 ","
                 (Term.paren
                  "("
                  [`hx
                   [(Term.typeAscription
                     ":"
                     (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
                  ")")
                 ","
                 `y
                 ","
                 (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
                 ","
                 (Term.paren
                  "("
                  [`hy
                   [(Term.typeAscription
                     ":"
                     (Init.Core.«term_∈_»
                      (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")")
                      " ∈ "
                      `d))]]
                  ")")]
                "⟩")
               []
               []
               ":="
               (Term.app
                (Term.explicit "@" `this)
                [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Init.Core.«term_∈_»
                   (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
                   " ∈ "
                   (Term.app `CompRel [`d `d])))]
                ":="
                (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
              []
              (Term.app `h [`this `rfl])))))))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
           ":="
           (Term.app
            (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
            [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_=_»
               (Order.Lattice.«term_⊓_»
                (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
                "⊓"
                (Term.app
                 (Filter.Order.Filter.Basic.term𝓟 "𝓟")
                 [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
               "="
               (Order.BoundedOrder.«term⊥» "⊥")))]
            ":="
            (Term.app
             (Term.proj
              (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
              "."
              (fieldIdx "2"))
             [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
          []
          (Term.anonymousCtor
           "⟨"
           [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
            ","
            (Term.proj `is_closed_closure "." `is_open_compl)
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x `h₁ `h₂] [])]
              "=>"
              (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
            ","
            `this]
           "⟩")))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Term.anonymousCtor "⟨" [`d "," `hd "," `h] "⟩")
     []
     []
     ":="
     (Term.app `comp_mem_uniformity_sets [`this])))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letIdDecl
      `e
      []
      []
      ":="
      (Set.«term{_|_}»
       "{"
       (Mathlib.ExtendedBinder.extBinder `y [":" `α])
       "|"
       (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`y])]] ")") " ∈ " `d)
       "}")))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`hae []]
       [(Term.typeSpec ":" (Init.Core.«term_∈_» `a " ∈ " (Term.app `Closure [`e])))]
       ":="
       («term_$__» `subset_closure "$" (Term.app `refl_mem_uniformity [`hd]))))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        []
        [(Term.typeSpec
          ":"
          (Init.Core.«term_⊆_»
           (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
           " ⊆ "
           (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
               "]")
              [])
             [])
            (group
             (Tactic.change
              "change"
              («term_≤_»
               (Order.CompleteLattice.«term⨅_,_»
                "⨅"
                (Lean.explicitBinders
                 [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent "_")]
                   ":"
                   (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                   ")")])
                ", "
                (Term.hole "_"))
               "≤"
               (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              («term_$__»
               (Term.app `infi_le_of_le [`d])
               "$"
               («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
             [])])))))
      []
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`e_subset []]
         [(Term.typeSpec
           ":"
           (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`a' `ha'] [])]
           "=>"
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor
               "⟨"
               [`x
                ","
                (Term.paren
                 "("
                 [`hx
                  [(Term.typeAscription
                    ":"
                    (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
                 ")")
                ","
                `y
                ","
                (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
                ","
                (Term.paren
                 "("
                 [`hy
                  [(Term.typeAscription
                    ":"
                    (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
                 ")")]
               "⟩")
              []
              []
              ":="
              (Term.app
               (Term.explicit "@" `this)
               [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Init.Core.«term_∈_»
                  (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
                  " ∈ "
                  (Term.app `CompRel [`d `d])))]
               ":="
               (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
             []
             (Term.app `h [`this `rfl])))))))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
          ":="
          (Term.app
           (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
           [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Order.Lattice.«term_⊓_»
               (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
               "⊓"
               (Term.app
                (Filter.Order.Filter.Basic.term𝓟 "𝓟")
                [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
              "="
              (Order.BoundedOrder.«term⊥» "⊥")))]
           ":="
           (Term.app
            (Term.proj
             (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
             "."
             (fieldIdx "2"))
            [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
         []
         (Term.anonymousCtor
          "⟨"
          [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
           ","
           (Term.proj `is_closed_closure "." `is_open_compl)
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x `h₁ `h₂] [])]
             "=>"
             (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
           ","
           `this]
          "⟩"))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `e
     []
     []
     ":="
     (Set.«term{_|_}»
      "{"
      (Mathlib.ExtendedBinder.extBinder `y [":" `α])
      "|"
      (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`y])]] ")") " ∈ " `d)
      "}")))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      [`hae []]
      [(Term.typeSpec ":" (Init.Core.«term_∈_» `a " ∈ " (Term.app `Closure [`e])))]
      ":="
      («term_$__» `subset_closure "$" (Term.app `refl_mem_uniformity [`hd]))))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       []
       [(Term.typeSpec
         ":"
         (Init.Core.«term_⊆_»
          (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
          " ⊆ "
          (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
              "]")
             [])
            [])
           (group
            (Tactic.change
             "change"
             («term_≤_»
              (Order.CompleteLattice.«term⨅_,_»
               "⨅"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent "_")]
                  ":"
                  (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                  ")")])
               ", "
               (Term.hole "_"))
              "≤"
              (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             («term_$__»
              (Term.app `infi_le_of_le [`d])
              "$"
              («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
            [])])))))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`e_subset []]
        [(Term.typeSpec
          ":"
          (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`a' `ha'] [])]
          "=>"
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor
              "⟨"
              [`x
               ","
               (Term.paren
                "("
                [`hx
                 [(Term.typeAscription
                   ":"
                   (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
                ")")
               ","
               `y
               ","
               (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
               ","
               (Term.paren
                "("
                [`hy
                 [(Term.typeAscription
                   ":"
                   (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
                ")")]
              "⟩")
             []
             []
             ":="
             (Term.app
              (Term.explicit "@" `this)
              [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Init.Core.«term_∈_»
                 (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
                 " ∈ "
                 (Term.app `CompRel [`d `d])))]
              ":="
              (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
            []
            (Term.app `h [`this `rfl])))))))
      []
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
         ":="
         (Term.app
          (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
          [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Order.Lattice.«term_⊓_»
              (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
              "⊓"
              (Term.app
               (Filter.Order.Filter.Basic.term𝓟 "𝓟")
               [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
             "="
             (Order.BoundedOrder.«term⊥» "⊥")))]
          ":="
          (Term.app
           (Term.proj
            (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
            "."
            (fieldIdx "2"))
           [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
        []
        (Term.anonymousCtor
         "⟨"
         [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
          ","
          (Term.proj `is_closed_closure "." `is_open_compl)
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `h₁ `h₂] [])]
            "=>"
            (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
          ","
          `this]
         "⟩")))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hae []]
     [(Term.typeSpec ":" (Init.Core.«term_∈_» `a " ∈ " (Term.app `Closure [`e])))]
     ":="
     («term_$__» `subset_closure "$" (Term.app `refl_mem_uniformity [`hd]))))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec
        ":"
        (Init.Core.«term_⊆_»
         (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
         " ⊆ "
         (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
             "]")
            [])
           [])
          (group
           (Tactic.change
            "change"
            («term_≤_»
             (Order.CompleteLattice.«term⨅_,_»
              "⨅"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
                (Lean.bracketedExplicitBinders
                 "("
                 [(Lean.binderIdent "_")]
                 ":"
                 (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                 ")")])
              ", "
              (Term.hole "_"))
             "≤"
             (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
            [])
           [])
          (group
           (Tactic.exact
            "exact"
            («term_$__»
             (Term.app `infi_le_of_le [`d])
             "$"
             («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
           [])])))))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`e_subset []]
       [(Term.typeSpec ":" (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`a' `ha'] [])]
         "=>"
         (Term.let
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Term.anonymousCtor
             "⟨"
             [`x
              ","
              (Term.paren
               "("
               [`hx
                [(Term.typeAscription
                  ":"
                  (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
               ")")
              ","
              `y
              ","
              (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
              ","
              (Term.paren
               "("
               [`hy
                [(Term.typeAscription
                  ":"
                  (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
               ")")]
             "⟩")
            []
            []
            ":="
            (Term.app
             (Term.explicit "@" `this)
             [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Init.Core.«term_∈_»
                (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
                " ∈ "
                (Term.app `CompRel [`d `d])))]
             ":="
             (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
           []
           (Term.app `h [`this `rfl])))))))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        []
        [(Term.typeSpec
          ":"
          (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
        ":="
        (Term.app
         (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
         [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
      []
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Order.Lattice.«term_⊓_»
             (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
             "⊓"
             (Term.app
              (Filter.Order.Filter.Basic.term𝓟 "𝓟")
              [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
            "="
            (Order.BoundedOrder.«term⊥» "⊥")))]
         ":="
         (Term.app
          (Term.proj
           (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
           "."
           (fieldIdx "2"))
          [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
       []
       (Term.anonymousCtor
        "⟨"
        [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
         ","
         (Term.proj `is_closed_closure "." `is_open_compl)
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x `h₁ `h₂] [])]
           "=>"
           (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
         ","
         `this]
        "⟩"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Init.Core.«term_⊆_»
        (Term.app `Set.Prod [(Term.app `Closure [`e]) (Term.app `Closure [`e])])
        " ⊆ "
        (Term.app `CompRel [`d (Term.app `CompRel [(Term.app `Set.Prod [`e `e]) `d])])))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
            "]")
           [])
          [])
         (group
          (Tactic.change
           "change"
           («term_≤_»
            (Order.CompleteLattice.«term⨅_,_»
             "⨅"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
               (Lean.bracketedExplicitBinders
                "("
                [(Lean.binderIdent "_")]
                ":"
                (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                ")")])
             ", "
             (Term.hole "_"))
            "≤"
            (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
           [])
          [])
         (group
          (Tactic.exact
           "exact"
           («term_$__»
            (Term.app `infi_le_of_le [`d])
            "$"
            («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
          [])])))))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      [`e_subset []]
      [(Term.typeSpec ":" (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`a' `ha'] [])]
        "=>"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor
            "⟨"
            [`x
             ","
             (Term.paren
              "("
              [`hx
               [(Term.typeAscription
                 ":"
                 (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
              ")")
             ","
             `y
             ","
             (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
             ","
             (Term.paren
              "("
              [`hy
               [(Term.typeAscription
                 ":"
                 (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
              ")")]
            "⟩")
           []
           []
           ":="
           (Term.app
            (Term.explicit "@" `this)
            [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              (Init.Core.«term_∈_»
               (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
               " ∈ "
               (Term.app `CompRel [`d `d])))]
            ":="
            (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
          []
          (Term.app `h [`this `rfl])))))))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       []
       [(Term.typeSpec
         ":"
         (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
       ":="
       (Term.app
        (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
        [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        []
        [(Term.typeSpec
          ":"
          («term_=_»
           (Order.Lattice.«term_⊓_»
            (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
            "⊓"
            (Term.app
             (Filter.Order.Filter.Basic.term𝓟 "𝓟")
             [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
           "="
           (Order.BoundedOrder.«term⊥» "⊥")))]
        ":="
        (Term.app
         (Term.proj
          (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
          "."
          (fieldIdx "2"))
         [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
      []
      (Term.anonymousCtor
       "⟨"
       [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
        ","
        (Term.proj `is_closed_closure "." `is_open_compl)
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x `h₁ `h₂] [])]
          "=>"
          (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
        ","
        `this]
       "⟩")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`e_subset []]
     [(Term.typeSpec ":" (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")))]
     ":="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`a' `ha'] [])]
       "=>"
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.anonymousCtor
           "⟨"
           [`x
            ","
            (Term.paren
             "("
             [`hx
              [(Term.typeAscription
                ":"
                (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
             ")")
            ","
            `y
            ","
            (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
            ","
            (Term.paren
             "("
             [`hy
              [(Term.typeAscription
                ":"
                (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
             ")")]
           "⟩")
          []
          []
          ":="
          (Term.app
           (Term.explicit "@" `this)
           [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_»
              (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
              " ∈ "
              (Term.app `CompRel [`d `d])))]
           ":="
           (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
         []
         (Term.app `h [`this `rfl])))))))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec
        ":"
        (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
      ":="
      (Term.app
       (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
       [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       []
       [(Term.typeSpec
         ":"
         («term_=_»
          (Order.Lattice.«term_⊓_»
           (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
           "⊓"
           (Term.app
            (Filter.Order.Filter.Basic.term𝓟 "𝓟")
            [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
          "="
          (Order.BoundedOrder.«term⊥» "⊥")))]
       ":="
       (Term.app
        (Term.proj
         (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
         "."
         (fieldIdx "2"))
        [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
     []
     (Term.anonymousCtor
      "⟨"
      [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
       ","
       (Term.proj `is_closed_closure "." `is_open_compl)
       ","
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x `h₁ `h₂] [])]
         "=>"
         (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
       ","
       `this]
      "⟩"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])))]
     ":="
     (Term.app
      (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
      [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec
        ":"
        («term_=_»
         (Order.Lattice.«term_⊓_»
          (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
          "⊓"
          (Term.app
           (Filter.Order.Filter.Basic.term𝓟 "𝓟")
           [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
         "="
         (Order.BoundedOrder.«term⊥» "⊥")))]
      ":="
      (Term.app
       (Term.proj
        (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
        "."
        (fieldIdx "2"))
       [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
    []
    (Term.anonymousCtor
     "⟨"
     [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
      ","
      (Term.proj `is_closed_closure "." `is_open_compl)
      ","
      (Term.fun
       "fun"
       (Term.basicFun [(Term.simpleBinder [`x `h₁ `h₂] [])] "=>" (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
      ","
      `this]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       («term_=_»
        (Order.Lattice.«term_⊓_»
         (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
         "⊓"
         (Term.app
          (Filter.Order.Filter.Basic.term𝓟 "𝓟")
          [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
        "="
        (Order.BoundedOrder.«term⊥» "⊥")))]
     ":="
     (Term.app
      (Term.proj
       (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
       "."
       (fieldIdx "2"))
      [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])))
   []
   (Term.anonymousCtor
    "⟨"
    [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
     ","
     (Term.proj `is_closed_closure "." `is_open_compl)
     ","
     (Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [`x `h₁ `h₂] [])] "=>" (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
     ","
     `this]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
    ","
    (Term.proj `is_closed_closure "." `is_open_compl)
    ","
    (Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`x `h₁ `h₂] [])] "=>" (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
    ","
    `this]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`x `h₁ `h₂] [])] "=>" (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.explicit "@" `e_subset) [`x `h₂ `h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `e_subset)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e_subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `is_closed_closure "." `is_open_compl)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `is_closed_closure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
  (Term.app `Closure [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Closure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1022, (some 1023, term) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 999, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   (Term.proj
    (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
    "."
    (fieldIdx "2"))
   [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `le_principal_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `le_principal_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `le_principal_iff "." (fieldIdx "2")) [`this]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
   "."
   (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `is_compl_principal [(Term.app `Closure [`e])]) "." `inf_right_eq_bot_iff)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `is_compl_principal [(Term.app `Closure [`e])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Closure [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Closure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Closure [`e]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_compl_principal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `is_compl_principal [(Term.paren "(" [(Term.app `Closure [`e]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Order.Lattice.«term_⊓_»
    (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
    "⊓"
    (Term.app (Filter.Order.Filter.Basic.term𝓟 "𝓟") [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
   "="
   (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Order.Lattice.«term_⊓_»
   (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
   "⊓"
   (Term.app (Filter.Order.Filter.Basic.term𝓟 "𝓟") [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Lattice.«term_⊓_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Filter.Order.Filter.Basic.term𝓟 "𝓟") [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
  (Term.app `Closure [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Closure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1022, (some 1023, term) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 999, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Order.BooleanAlgebra.«term_ᶜ» (Term.app `Closure [`e]) "ᶜ") []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Filter.Order.Filter.Basic.term𝓟 "𝓟")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.term𝓟', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1022, (some 1023, term) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 69, (some 70, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
   [(Term.app `mem_nhds_left [`a `hd]) `subset_closure])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `subset_closure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `mem_nhds_left [`a `hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_nhds_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `mem_nhds_left [`a `hd]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) "." `sets_of_superset)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app (Topology.Basic.term𝓝 "𝓝") [`a]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» (Term.app `Closure [`e]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `Closure [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Closure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a' `ha'] [])]
    "=>"
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor
        "⟨"
        [`x
         ","
         (Term.paren
          "("
          [`hx
           [(Term.typeAscription
             ":"
             (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
          ")")
         ","
         `y
         ","
         (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
         ","
         (Term.paren
          "("
          [`hy
           [(Term.typeAscription
             ":"
             (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
          ")")]
        "⟩")
       []
       []
       ":="
       (Term.app
        (Term.explicit "@" `this)
        [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
     []
     (Term.have
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        []
        [(Term.typeSpec
          ":"
          (Init.Core.«term_∈_»
           (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
           " ∈ "
           (Term.app `CompRel [`d `d])))]
        ":="
        (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
      []
      (Term.app `h [`this `rfl])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Term.anonymousCtor
      "⟨"
      [`x
       ","
       (Term.paren
        "("
        [`hx
         [(Term.typeAscription
           ":"
           (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
        ")")
       ","
       `y
       ","
       (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
       ","
       (Term.paren
        "("
        [`hy
         [(Term.typeAscription
           ":"
           (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
        ")")]
      "⟩")
     []
     []
     ":="
     (Term.app
      (Term.explicit "@" `this)
      [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec
        ":"
        (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")") " ∈ " (Term.app `CompRel [`d `d])))]
      ":="
      (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
    []
    (Term.app `h [`this `rfl])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")") " ∈ " (Term.app `CompRel [`d `d])))]
     ":="
     (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")))
   []
   (Term.app `h [`this `rfl]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h [`this `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.anonymousCtor "⟨" [`y "," `hx₂ "," `hy] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")") " ∈ " (Term.app `CompRel [`d `d]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `CompRel [`d `d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `CompRel
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren "(" [`a [(Term.tupleTail "," [`a'])]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   (Term.explicit "@" `this)
   [(Term.anonymousCtor "⟨" [`a "," `a'] "⟩") (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`hae "," `ha'] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ha'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hae
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.anonymousCtor "⟨" [`a "," `a'] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `this)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`x
    ","
    (Term.paren
     "("
     [`hx
      [(Term.typeAscription ":" (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
     ")")
    ","
    `y
    ","
    (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
    ","
    (Term.paren
     "("
     [`hy
      [(Term.typeAscription
        ":"
        (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
     ")")]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [`hy
    [(Term.typeAscription
      ":"
      (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")") " ∈ " `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren "(" [`y [(Term.tupleTail "," [(Term.hole "_")])]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`hx₁ "," `hx₂] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [`hx
    [(Term.typeAscription ":" (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")") " ∈ " `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren "(" [`a [(Term.tupleTail "," [`x])]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_⊆_» (Term.app `Closure [`e]) " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 999, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `Closure [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Closure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `closure_prod_eq) "," (Tactic.rwRule [] `closure_eq_inter_uniformity)]
         "]")
        [])
       [])
      (group
       (Tactic.change
        "change"
        («term_≤_»
         (Order.CompleteLattice.«term⨅_,_»
          "⨅"
          (Lean.explicitBinders
           [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
            (Lean.bracketedExplicitBinders
             "("
             [(Lean.binderIdent "_")]
             ":"
             (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
             ")")])
          ", "
          (Term.hole "_"))
         "≤"
         (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        («term_$__»
         (Term.app `infi_le_of_le [`d])
         "$"
         («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
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
   («term_$__»
    (Term.app `infi_le_of_le [`d])
    "$"
    («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `infi_le_of_le [`d])
   "$"
   («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» (Term.app `infi_le_of_le [`hd]) "$" (Term.app `le_reflₓ [(Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_reflₓ [(Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app `infi_le_of_le [`hd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `infi_le_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app `infi_le_of_le [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `infi_le_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.change
   "change"
   («term_≤_»
    (Order.CompleteLattice.«term⨅_,_»
     "⨅"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
       (Lean.bracketedExplicitBinders
        "("
        [(Lean.binderIdent "_")]
        ":"
        (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
        ")")])
     ", "
     (Term.hole "_"))
    "≤"
    (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.change', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Order.CompleteLattice.«term⨅_,_»
    "⨅"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent "_")]
       ":"
       (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
       ")")])
    ", "
    (Term.hole "_"))
   "≤"
   (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `CompRel [`d (Term.app `CompRel [(Term.hole "_") `d])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `CompRel [(Term.hole "_") `d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `CompRel
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `CompRel [(Term.hole "_") `d]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `CompRel
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Order.CompleteLattice.«term⨅_,_»
   "⨅"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `d')] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent "_")]
      ":"
      (Init.Core.«term_∈_» `d' " ∈ " (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
      ")")])
   ", "
   (Term.hole "_"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  separated_regular
  [ SeparatedSpace α ] : RegularSpace α
  :=
    {
      @ T2Space.t1_space _ _ separated_iff_t2 . mp ‹ _ › with
      t0 := by have := separated_iff_t2.mp ‹ _ › exact t1_space.t0_space.t0 ,
        regular
          :=
          fun
            s a hs ha
              =>
              have
                : s ᶜ ∈ 𝓝 a := IsOpen.mem_nhds hs.is_open_compl ha
                have
                  : { p : α × α | p . 1 = a → p . 2 ∈ s ᶜ } ∈ 𝓤 α := mem_nhds_uniformity_iff_right . mp this
                  let
                    ⟨ d , hd , h ⟩ := comp_mem_uniformity_sets this
                    let
                      e := { y : α | ( a , y ) ∈ d }
                      have
                        hae : a ∈ Closure e := subset_closure $ refl_mem_uniformity hd
                        have
                          : Set.Prod Closure e Closure e ⊆ CompRel d CompRel Set.Prod e e d
                            :=
                            by
                              rw [ ← closure_prod_eq , closure_eq_inter_uniformity ]
                                change ⨅ ( d' : _ ) ( _ : d' ∈ 𝓤 α ) , _ ≤ CompRel d CompRel _ d
                                exact infi_le_of_le d $ infi_le_of_le hd $ le_reflₓ _
                          have
                            e_subset
                              : Closure e ⊆ s ᶜ
                              :=
                              fun
                                a' ha'
                                  =>
                                  let
                                    ⟨ x , ( hx : ( a , x ) ∈ d ) , y , ⟨ hx₁ , hx₂ ⟩ , ( hy : ( y , _ ) ∈ d ) ⟩
                                      :=
                                      @ this ⟨ a , a' ⟩ ⟨ hae , ha' ⟩
                                    have : ( a , a' ) ∈ CompRel d d := ⟨ y , hx₂ , hy ⟩ h this rfl
                            have
                              : Closure e ∈ 𝓝 a := 𝓝 a . sets_of_superset mem_nhds_left a hd subset_closure
                              have
                                : 𝓝 a ⊓ 𝓟 Closure e ᶜ = ⊥
                                  :=
                                  is_compl_principal Closure e . inf_right_eq_bot_iff . 2 le_principal_iff . 2 this
                                ⟨
                                  Closure e ᶜ
                                    ,
                                    is_closed_closure . is_open_compl
                                    ,
                                    fun x h₁ h₂ => @ e_subset x h₂ h₁
                                    ,
                                    this
                                  ⟩
      }

theorem is_closed_of_spaced_out [SeparatedSpace α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
    (hs : s.pairwise fun x y => (x, y) ∉ V₀) : IsClosed s := by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply is_closed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by
    rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in V_symm
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y
  ·
    by_contra hzy
    exact hs hz' hy' hzy (h_comp $ mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz

theorem is_closed_range_of_spaced_out {ι} [SeparatedSpace α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {f : ι → α}
    (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  is_closed_of_spaced_out V₀_in $ by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf x y (ne_of_apply_ne f h)

/-!
### Separated sets
-/


-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (x y «expr ∈ » s)
/--  A set `s` in a uniform space `α` is separated if the separation relation `𝓢 α`
induces the trivial relation on `s`. -/
def IsSeparated (s : Set α) : Prop :=
  ∀ x y _ : x ∈ s _ : y ∈ s, (x, y) ∈ 𝓢 α → x = y

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (x y «expr ∈ » s)
theorem is_separated_def (s : Set α) : IsSeparated s ↔ ∀ x y _ : x ∈ s _ : y ∈ s, (x, y) ∈ 𝓢 α → x = y :=
  Iff.rfl

theorem is_separated_def' (s : Set α) : IsSeparated s ↔ s.prod s ∩ 𝓢 α ⊆ IdRel := by
  rw [is_separated_def]
  constructor
  ·
    rintro h ⟨x, y⟩ ⟨⟨x_in, y_in⟩, H⟩
    simp [h x y x_in y_in H]
  ·
    intro h x y x_in y_in xy_in
    rw [← mem_id_rel]
    exact h ⟨mk_mem_prod x_in y_in, xy_in⟩

theorem IsSeparated.mono {s t : Set α} (hs : IsSeparated s) (hts : t ⊆ s) : IsSeparated t := fun x y hx hy =>
  hs x y (hts hx) (hts hy)

theorem univ_separated_iff : IsSeparated (univ : Set α) ↔ SeparatedSpace α := by
  simp only [IsSeparated, mem_univ, true_implies_iff, separated_space_iff]
  constructor
  ·
    intro h
    exact subset.antisymm (fun ⟨x, y⟩ xy_in => h x y xy_in) (id_rel_sub_separation_relation α)
  ·
    intro h x y xy_in
    rwa [h] at xy_in

theorem is_separated_of_separated_space [SeparatedSpace α] (s : Set α) : IsSeparated s := by
  rw [IsSeparated, SeparatedSpace.out]
  tauto

theorem is_separated_iff_induced {s : Set α} : IsSeparated s ↔ SeparatedSpace s := by
  rw [separated_space_iff]
  change _ ↔ 𝓢 { x // x ∈ s } = _
  rw [separation_rel_comap rfl, is_separated_def']
  constructor <;> intro h
  ·
    ext ⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩
    suffices (x, y) ∈ 𝓢 α ↔ x = y by
      simpa only [mem_id_rel]
    refine' ⟨fun H => h ⟨mk_mem_prod x_in y_in, H⟩, _⟩
    rintro rfl
    exact id_rel_sub_separation_relation α rfl
  ·
    rintro ⟨x, y⟩ ⟨⟨x_in, y_in⟩, hS⟩
    have A : (⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩ : ↥s × ↥s) ∈ Prod.map (coeₓ : s → α) (coeₓ : s → α) ⁻¹' 𝓢 α
    exact hS
    simpa using h.subset A

theorem eq_of_uniformity_inf_nhds_of_is_separated {s : Set α} (hs : IsSeparated s) :
    ∀ {x y : α}, x ∈ s → y ∈ s → ClusterPt (x, y) (𝓤 α) → x = y := by
  intro x y x_in y_in H
  have : ∀, ∀ V ∈ 𝓤 α, ∀, (x, y) ∈ Closure V := by
    intro V V_in
    rw [mem_closure_iff_cluster_pt]
    have : 𝓤 α ≤ 𝓟 V := by
      rwa [le_principal_iff]
    exact H.mono this
  apply hs x y x_in y_in
  simpa [separation_rel_eq_inter_closure]

theorem eq_of_uniformity_inf_nhds [SeparatedSpace α] : ∀ {x y : α}, ClusterPt (x, y) (𝓤 α) → x = y := by
  have : IsSeparated (univ : Set α) := by
    rw [univ_separated_iff]
    assumption
  introv
  simpa using eq_of_uniformity_inf_nhds_of_is_separated this

/-!
### Separation quotient
-/


namespace UniformSpace

/--  The separation relation of a uniform space seen as a setoid. -/
def separation_setoid (α : Type u) [UniformSpace α] : Setoidₓ α :=
  ⟨fun x y => (x, y) ∈ 𝓢 α, separated_equiv⟩

attribute [local instance] separation_setoid

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.instance
  (Term.attrKind [])
  "instance"
  []
  [(Command.declId `separation_setoid.uniform_space [])]
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [`u])] "}")
    (Term.instBinder "[" [`u ":"] (Term.app `UniformSpace [`α]) "]")]
   (Term.typeSpec ":" (Term.app `UniformSpace [(Term.app `Quotientₓ [(Term.app `separation_setoid [`α])])])))
  (Command.whereStructInst
   "where"
   [(group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `toTopologicalSpace
        []
        []
        ":="
        (Term.app
         `u.to_topological_space.coinduced
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Quot.Data.Quot.«term⟦_⟧» "⟦" `x "⟧")))]))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `uniformity
        []
        []
        ":="
        (Term.app
         `map
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`p] [(Term.typeSpec ":" («term_×_» `α "×" `α))])]
            "=>"
            (Term.paren
             "("
             [(Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "1")) "⟧")
              [(Term.tupleTail "," [(Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "2")) "⟧")])]]
             ")")))
          `u.uniformity]))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `refl
        []
        []
        ":="
        (Term.app
         `le_transₓ
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `Quotientₓ.exists_rep)] "]"] []) [])])))
          (Term.app `Filter.map_mono [`refl_le_uniformity])]))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `symm
        []
        []
        ":="
        («term_$__»
         `tendsto_map'
         "$"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.«tactic_<;>_»
               (Tactic.simp
                "simp"
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `Prod.swap)
                  ","
                  (Tactic.simpLemma [] [] (Rel.Data.Rel.«term_∘_» (Term.cdot "·") " ∘ " (Term.cdot "·")))]
                 "]"]
                [])
               "<;>"
               (Tactic.exact "exact" (Term.app `tendsto_map.comp [`tendsto_swap_uniformity])))
              [])])))))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `comp
        []
        []
        ":="
        (calc
         "calc"
         [(calcStep
           («term_=_»
            (Term.app
             (Term.proj
              (Term.app
               `map
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`p] [(Term.typeSpec ":" («term_×_» `α "×" `α))])]
                  "=>"
                  (Term.paren
                   "("
                   [(Quot.Data.Quot.«term⟦_⟧» "⟦" `p.fst "⟧")
                    [(Term.tupleTail "," [(Quot.Data.Quot.«term⟦_⟧» "⟦" `p.snd "⟧")])]]
                   ")")))
                `u.uniformity])
              "."
              `lift')
             [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.app `CompRel [`s `s])))])
            "="
            (Term.app
             `u.uniformity.lift'
             [(Rel.Data.Rel.«term_∘_»
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.app `CompRel [`s `s])))
               " ∘ "
               (Term.app
                `image
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`p] [(Term.typeSpec ":" («term_×_» `α "×" `α))])]
                   "=>"
                   (Term.paren
                    "("
                    [(Quot.Data.Quot.«term⟦_⟧» "⟦" `p.fst "⟧")
                     [(Term.tupleTail "," [(Quot.Data.Quot.«term⟦_⟧» "⟦" `p.snd "⟧")])]]
                    ")")))]))]))
           ":="
           («term_$__» `map_lift'_eq2 "$" (Term.app `monotone_comp_rel [`monotone_id `monotone_id])))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Term.app
             `u.uniformity.lift'
             [(Rel.Data.Rel.«term_∘_»
               (Term.app
                `image
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`p] [(Term.typeSpec ":" («term_×_» `α "×" `α))])]
                   "=>"
                   (Term.paren
                    "("
                    [(Quot.Data.Quot.«term⟦_⟧» "⟦" `p.fst "⟧")
                     [(Term.tupleTail "," [(Quot.Data.Quot.«term⟦_⟧» "⟦" `p.snd "⟧")])]]
                    ")")))])
               " ∘ "
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.app `Set [(«term_×_» `α "×" `α)]))])]
                 "=>"
                 (Term.app `CompRel [`s (Term.app `CompRel [`s `s])]))))]))
           ":="
           («term_$__»
            `lift'_mono'
            "$"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`s `hs] [])
               (Term.anonymousCtor "⟨" [`a "," `b] "⟩")
               (Term.anonymousCtor
                "⟨"
                [`c
                 ","
                 (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a₁ "," `a₂] "⟩") "," `ha "," `a_eq] "⟩")
                 ","
                 (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b₁ "," `b₂] "⟩") "," `hb "," `b_eq] "⟩")]
                "⟩")]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`a_eq] []))]) [])
                  (group (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`b_eq] []))]) [])
                  (group
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`h []]
                      [(Term.typeSpec
                        ":"
                        («term_=_» (Quot.Data.Quot.«term⟦_⟧» "⟦" `a₂ "⟧") "=" (Quot.Data.Quot.«term⟦_⟧» "⟦" `b₁ "⟧")))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [] `a_eq.right) "," (Tactic.rwRule [] `b_eq.left)]
                             "]")
                            [])
                           [])]))))))
                   [])
                  (group
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`h []]
                      [(Term.typeSpec
                        ":"
                        (Init.Core.«term_∈_»
                         (Term.paren "(" [`a₂ [(Term.tupleTail "," [`b₁])]] ")")
                         " ∈ "
                         (Term.app (Topology.UniformSpace.Separation.term𝓢 "𝓢") [`α])))]
                      ":="
                      (Term.app `Quotientₓ.exact [`h]))))
                   [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `Function.comp)
                      ","
                      (Tactic.simpLemma [] [] `Set.Image)
                      ","
                      (Tactic.simpLemma [] [] `CompRel)
                      ","
                      (Tactic.simpLemma [] [] `And.comm)
                      ","
                      (Tactic.simpLemma [] [] `And.left_comm)
                      ","
                      (Tactic.simpLemma [] [] `And.assoc)]
                     "]"]
                    [])
                   [])
                  (group
                   (Tactic.exact
                    "exact"
                    (Term.anonymousCtor
                     "⟨"
                     [`a₁
                      ","
                      `a_eq.left
                      ","
                      `b₂
                      ","
                      `b_eq.right
                      ","
                      `a₂
                      ","
                      `ha
                      ","
                      `b₁
                      ","
                      (Term.app `h [`s `hs])
                      ","
                      `hb]
                     "⟩"))
                   [])])))))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Term.app
             `map
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`p] [(Term.typeSpec ":" («term_×_» `α "×" `α))])]
                "=>"
                (Term.paren
                 "("
                 [(Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "1")) "⟧")
                  [(Term.tupleTail "," [(Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "2")) "⟧")])]]
                 ")")))
              (Term.app
               `u.uniformity.lift'
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.app `Set [(«term_×_» `α "×" `α)]))])]
                  "=>"
                  (Term.app `CompRel [`s (Term.app `CompRel [`s `s])])))])]))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.«tactic_<;>_»
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `map_lift'_eq)] "]") [])
                 "<;>"
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `monotone_comp_rel
                   [`monotone_id (Term.app `monotone_comp_rel [`monotone_id `monotone_id])])))
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Term.app
             `map
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`p] [(Term.typeSpec ":" («term_×_» `α "×" `α))])]
                "=>"
                (Term.paren
                 "("
                 [(Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "1")) "⟧")
                  [(Term.tupleTail "," [(Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "2")) "⟧")])]]
                 ")")))
              `u.uniformity]))
           ":="
           (Term.app `map_mono [`comp_le_uniformity3]))]))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `is_open_uniformity
        [(Term.simpleBinder [(Term.simpleBinder [`s] [])] [])]
        []
        ":="
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`a] [])]
              ","
              (Term.arrow
               (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") " ∈ " `s)
               "→"
               («term_↔_»
                (Init.Core.«term_∈_»
                 (Set.«term{_|_}»
                  "{"
                  (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
                  "|"
                  (Term.arrow
                   («term_=_» (Term.proj `p "." (fieldIdx "1")) "=" `a)
                   "→"
                   (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "2")) "⟧") " ∈ " `s))
                  "}")
                 " ∈ "
                 (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
                "↔"
                (Init.Core.«term_∈_»
                 (Set.«term{_|_}»
                  "{"
                  (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
                  "|"
                  (Term.arrow
                   (StrictWeakOrder.Init.Algebra.Classes.«term_≈_» (Term.proj `p "." (fieldIdx "1")) " ≈ " `a)
                   "→"
                   (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "2")) "⟧") " ∈ " `s))
                  "}")
                 " ∈ "
                 (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`a `ha] [])]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`h] [])]
                 "=>"
                 (Term.let
                  "let"
                  (Term.letDecl
                   (Term.letPatDecl
                    (Term.anonymousCtor "⟨" [`t "," `ht "," `hts] "⟩")
                    []
                    []
                    ":="
                    (Term.app `comp_mem_uniformity_sets [`h])))
                  []
                  (Term.have
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hts []]
                     [(Term.typeSpec
                       ":"
                       (Term.forall
                        "∀"
                        [(Term.implicitBinder "{" [`a₁ `a₂] [] "}")]
                        ","
                        (Term.arrow
                         (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`a₁])]] ")") " ∈ " `t)
                         "→"
                         (Term.arrow
                          (Init.Core.«term_∈_» (Term.paren "(" [`a₁ [(Term.tupleTail "," [`a₂])]] ")") " ∈ " `t)
                          "→"
                          (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" `a₂ "⟧") " ∈ " `s)))))]
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`a₁ `a₂ `ha₁ `ha₂] [])]
                       "=>"
                       (Term.app
                        (Term.explicit "@" `hts)
                        [(Term.paren "(" [`a [(Term.tupleTail "," [`a₂])]] ")")
                         (Term.anonymousCtor "⟨" [`a₁ "," `ha₁ "," `ha₂] "⟩")
                         `rfl])))))
                   []
                   (Term.have
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`ht' []]
                      [(Term.typeSpec
                        ":"
                        (Term.forall
                         "∀"
                         [(Term.implicitBinder "{" [`a₁ `a₂] [] "}")]
                         ","
                         (Term.arrow
                          (StrictWeakOrder.Init.Algebra.Classes.«term_≈_» `a₁ " ≈ " `a₂)
                          "→"
                          (Init.Core.«term_∈_» (Term.paren "(" [`a₁ [(Term.tupleTail "," [`a₂])]] ")") " ∈ " `t))))]
                      ":="
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`a₁ `a₂ `h] [])]
                        "=>"
                        (Term.app `sInter_subset_of_mem [`ht `h])))))
                    []
                    («term_$__»
                     (Term.app `u.uniformity.sets_of_superset [`ht])
                     "$"
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`a₁ "," `a₂] "⟩") (Term.simpleBinder [`h₁ `h₂] [])]
                       "=>"
                       (Term.app `hts [(«term_$__» `ht' "$" (Term.app `Setoidₓ.symm [`h₂])) `h₁])))))))))
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`h] [])]
                 "=>"
                 («term_$__»
                  (Term.app `u.uniformity.sets_of_superset [`h])
                  "$"
                  (Term.byTactic
                   "by"
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
                            (Term.structInstField
                             (Term.structInstLVal `contextual [])
                             ":="
                             `Bool.true._@._internal._hyg.0)
                            [])]
                          (Term.optEllipsis [])
                          []
                          "}")
                         ")"]
                        []
                        []
                        [])
                       [])]))))))]
              "⟩")))))
         []
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.simp
               "simp"
               []
               []
               ["["
                [(Tactic.simpLemma [] [] `TopologicalSpace.coinduced)
                 ","
                 (Tactic.simpLemma [] [] `u.is_open_uniformity)
                 ","
                 (Tactic.simpLemma [] [] `uniformity)
                 ","
                 (Tactic.simpLemma [] [] `forall_quotient_iff)]
                "]"]
               [])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`h `a `ha] [])]
                   "=>"
                   («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mp) "$" (Term.app `h [`a `ha]))))
                 ","
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`h `a `ha] [])]
                   "=>"
                   («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mpr) "$" (Term.app `h [`a `ha]))))]
                "⟩"))
              [])])))))))
     [])])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructField', expected 'Lean.Parser.Command.whereStructField.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`a] [])]
        ","
        (Term.arrow
         (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") " ∈ " `s)
         "→"
         («term_↔_»
          (Init.Core.«term_∈_»
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
            "|"
            (Term.arrow
             («term_=_» (Term.proj `p "." (fieldIdx "1")) "=" `a)
             "→"
             (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "2")) "⟧") " ∈ " `s))
            "}")
           " ∈ "
           (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))
          "↔"
          (Init.Core.«term_∈_»
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder `p [":" («term_×_» `α "×" `α)])
            "|"
            (Term.arrow
             (StrictWeakOrder.Init.Algebra.Classes.«term_≈_» (Term.proj `p "." (fieldIdx "1")) " ≈ " `a)
             "→"
             (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" (Term.proj `p "." (fieldIdx "2")) "⟧") " ∈ " `s))
            "}")
           " ∈ "
           (Term.app (Topology.UniformSpace.Basic.term𝓤 "𝓤") [`α]))))))]
     ":="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`a `ha] [])]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`h] [])]
           "=>"
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`t "," `ht "," `hts] "⟩")
              []
              []
              ":="
              (Term.app `comp_mem_uniformity_sets [`h])))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hts []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.implicitBinder "{" [`a₁ `a₂] [] "}")]
                  ","
                  (Term.arrow
                   (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`a₁])]] ")") " ∈ " `t)
                   "→"
                   (Term.arrow
                    (Init.Core.«term_∈_» (Term.paren "(" [`a₁ [(Term.tupleTail "," [`a₂])]] ")") " ∈ " `t)
                    "→"
                    (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" `a₂ "⟧") " ∈ " `s)))))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`a₁ `a₂ `ha₁ `ha₂] [])]
                 "=>"
                 (Term.app
                  (Term.explicit "@" `hts)
                  [(Term.paren "(" [`a [(Term.tupleTail "," [`a₂])]] ")")
                   (Term.anonymousCtor "⟨" [`a₁ "," `ha₁ "," `ha₂] "⟩")
                   `rfl])))))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`ht' []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [(Term.implicitBinder "{" [`a₁ `a₂] [] "}")]
                   ","
                   (Term.arrow
                    (StrictWeakOrder.Init.Algebra.Classes.«term_≈_» `a₁ " ≈ " `a₂)
                    "→"
                    (Init.Core.«term_∈_» (Term.paren "(" [`a₁ [(Term.tupleTail "," [`a₂])]] ")") " ∈ " `t))))]
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun [(Term.simpleBinder [`a₁ `a₂ `h] [])] "=>" (Term.app `sInter_subset_of_mem [`ht `h])))))
              []
              («term_$__»
               (Term.app `u.uniformity.sets_of_superset [`ht])
               "$"
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`a₁ "," `a₂] "⟩") (Term.simpleBinder [`h₁ `h₂] [])]
                 "=>"
                 (Term.app `hts [(«term_$__» `ht' "$" (Term.app `Setoidₓ.symm [`h₂])) `h₁])))))))))
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`h] [])]
           "=>"
           («term_$__»
            (Term.app `u.uniformity.sets_of_superset [`h])
            "$"
            (Term.byTactic
             "by"
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
                  []
                  [])
                 [])]))))))]
        "⟩")))))
   []
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `TopologicalSpace.coinduced)
           ","
           (Tactic.simpLemma [] [] `u.is_open_uniformity)
           ","
           (Tactic.simpLemma [] [] `uniformity)
           ","
           (Tactic.simpLemma [] [] `forall_quotient_iff)]
          "]"]
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`h `a `ha] [])]
             "=>"
             («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mp) "$" (Term.app `h [`a `ha]))))
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`h `a `ha] [])]
             "=>"
             («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mpr) "$" (Term.app `h [`a `ha]))))]
          "⟩"))
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `TopologicalSpace.coinduced)
          ","
          (Tactic.simpLemma [] [] `u.is_open_uniformity)
          ","
          (Tactic.simpLemma [] [] `uniformity)
          ","
          (Tactic.simpLemma [] [] `forall_quotient_iff)]
         "]"]
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`h `a `ha] [])]
            "=>"
            («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mp) "$" (Term.app `h [`a `ha]))))
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`h `a `ha] [])]
            "=>"
            («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mpr) "$" (Term.app `h [`a `ha]))))]
         "⟩"))
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
   (Term.anonymousCtor
    "⟨"
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`h `a `ha] [])]
       "=>"
       («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mp) "$" (Term.app `h [`a `ha]))))
     ","
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`h `a `ha] [])]
       "=>"
       («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mpr) "$" (Term.app `h [`a `ha]))))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`h `a `ha] [])]
      "=>"
      («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mp) "$" (Term.app `h [`a `ha]))))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`h `a `ha] [])]
      "=>"
      («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mpr) "$" (Term.app `h [`a `ha]))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`h `a `ha] [])]
    "=>"
    («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mpr) "$" (Term.app `h [`a `ha]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mpr) "$" (Term.app `h [`a `ha]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h [`a `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ha
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj (Term.app `this [`a `ha]) "." `mpr)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `this [`a `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ha
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `this [`a `ha]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`h `a `ha] [])]
    "=>"
    («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mp) "$" (Term.app `h [`a `ha]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» (Term.proj (Term.app `this [`a `ha]) "." `mp) "$" (Term.app `h [`a `ha]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h [`a `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ha
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj (Term.app `this [`a `ha]) "." `mp)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `this [`a `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ha
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `this [`a `ha]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `TopologicalSpace.coinduced)
     ","
     (Tactic.simpLemma [] [] `u.is_open_uniformity)
     ","
     (Tactic.simpLemma [] [] `uniformity)
     ","
     (Tactic.simpLemma [] [] `forall_quotient_iff)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `forall_quotient_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `uniformity
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u.is_open_uniformity
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `TopologicalSpace.coinduced
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a `ha] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`h] [])]
        "=>"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`t "," `ht "," `hts] "⟩")
           []
           []
           ":="
           (Term.app `comp_mem_uniformity_sets [`h])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hts []]
            [(Term.typeSpec
              ":"
              (Term.forall
               "∀"
               [(Term.implicitBinder "{" [`a₁ `a₂] [] "}")]
               ","
               (Term.arrow
                (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`a₁])]] ")") " ∈ " `t)
                "→"
                (Term.arrow
                 (Init.Core.«term_∈_» (Term.paren "(" [`a₁ [(Term.tupleTail "," [`a₂])]] ")") " ∈ " `t)
                 "→"
                 (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" `a₂ "⟧") " ∈ " `s)))))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`a₁ `a₂ `ha₁ `ha₂] [])]
              "=>"
              (Term.app
               (Term.explicit "@" `hts)
               [(Term.paren "(" [`a [(Term.tupleTail "," [`a₂])]] ")")
                (Term.anonymousCtor "⟨" [`a₁ "," `ha₁ "," `ha₂] "⟩")
                `rfl])))))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`ht' []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.implicitBinder "{" [`a₁ `a₂] [] "}")]
                ","
                (Term.arrow
                 (StrictWeakOrder.Init.Algebra.Classes.«term_≈_» `a₁ " ≈ " `a₂)
                 "→"
                 (Init.Core.«term_∈_» (Term.paren "(" [`a₁ [(Term.tupleTail "," [`a₂])]] ")") " ∈ " `t))))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`a₁ `a₂ `h] [])] "=>" (Term.app `sInter_subset_of_mem [`ht `h])))))
           []
           («term_$__»
            (Term.app `u.uniformity.sets_of_superset [`ht])
            "$"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.anonymousCtor "⟨" [`a₁ "," `a₂] "⟩") (Term.simpleBinder [`h₁ `h₂] [])]
              "=>"
              (Term.app `hts [(«term_$__» `ht' "$" (Term.app `Setoidₓ.symm [`h₂])) `h₁])))))))))
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`h] [])]
        "=>"
        («term_$__»
         (Term.app `u.uniformity.sets_of_superset [`h])
         "$"
         (Term.byTactic
          "by"
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
               []
               [])
              [])]))))))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`h] [])]
      "=>"
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`t "," `ht "," `hts] "⟩")
         []
         []
         ":="
         (Term.app `comp_mem_uniformity_sets [`h])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hts []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.implicitBinder "{" [`a₁ `a₂] [] "}")]
             ","
             (Term.arrow
              (Init.Core.«term_∈_» (Term.paren "(" [`a [(Term.tupleTail "," [`a₁])]] ")") " ∈ " `t)
              "→"
              (Term.arrow
               (Init.Core.«term_∈_» (Term.paren "(" [`a₁ [(Term.tupleTail "," [`a₂])]] ")") " ∈ " `t)
               "→"
               (Init.Core.«term_∈_» (Quot.Data.Quot.«term⟦_⟧» "⟦" `a₂ "⟧") " ∈ " `s)))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`a₁ `a₂ `ha₁ `ha₂] [])]
            "=>"
            (Term.app
             (Term.explicit "@" `hts)
             [(Term.paren "(" [`a [(Term.tupleTail "," [`a₂])]] ")")
              (Term.anonymousCtor "⟨" [`a₁ "," `ha₁ "," `ha₂] "⟩")
              `rfl])))))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`ht' []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.implicitBinder "{" [`a₁ `a₂] [] "}")]
              ","
              (Term.arrow
               (StrictWeakOrder.Init.Algebra.Classes.«term_≈_» `a₁ " ≈ " `a₂)
               "→"
               (Init.Core.«term_∈_» (Term.paren "(" [`a₁ [(Term.tupleTail "," [`a₂])]] ")") " ∈ " `t))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`a₁ `a₂ `h] [])] "=>" (Term.app `sInter_subset_of_mem [`ht `h])))))
         []
         («term_$__»
          (Term.app `u.uniformity.sets_of_superset [`ht])
          "$"
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.anonymousCtor "⟨" [`a₁ "," `a₂] "⟩") (Term.simpleBinder [`h₁ `h₂] [])]
            "=>"
            (Term.app `hts [(«term_$__» `ht' "$" (Term.app `Setoidₓ.symm [`h₂])) `h₁])))))))))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`h] [])]
      "=>"
      («term_$__»
       (Term.app `u.uniformity.sets_of_superset [`h])
       "$"
       (Term.byTactic
        "by"
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
             []
             [])
            [])]))))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`h] [])]
    "=>"
    («term_$__»
     (Term.app `u.uniformity.sets_of_superset [`h])
     "$"
     (Term.byTactic
      "by"
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
           []
           [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `u.uniformity.sets_of_superset [`h])
   "$"
   (Term.byTactic
    "by"
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
         []
         [])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
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
        []
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
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
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  separation_setoid.uniform_space
  { α : Type u } [ u : UniformSpace α ] : UniformSpace Quotientₓ separation_setoid α
  where
    toTopologicalSpace := u.to_topological_space.coinduced fun x => ⟦ x ⟧
      uniformity := map fun p : α × α => ( ⟦ p . 1 ⟧ , ⟦ p . 2 ⟧ ) u.uniformity
      refl := le_transₓ by simp [ Quotientₓ.exists_rep ] Filter.map_mono refl_le_uniformity
      symm := tendsto_map' $ by simp [ Prod.swap , · ∘ · ] <;> exact tendsto_map.comp tendsto_swap_uniformity
      comp
        :=
        calc
          map fun p : α × α => ( ⟦ p.fst ⟧ , ⟦ p.snd ⟧ ) u.uniformity . lift' fun s => CompRel s s
                =
                u.uniformity.lift' fun s => CompRel s s ∘ image fun p : α × α => ( ⟦ p.fst ⟧ , ⟦ p.snd ⟧ )
              :=
              map_lift'_eq2 $ monotone_comp_rel monotone_id monotone_id
            _
                ≤
                u.uniformity.lift'
                  image fun p : α × α => ( ⟦ p.fst ⟧ , ⟦ p.snd ⟧ ) ∘ fun s : Set α × α => CompRel s CompRel s s
              :=
              lift'_mono'
                $
                fun
                  s hs ⟨ a , b ⟩ ⟨ c , ⟨ ⟨ a₁ , a₂ ⟩ , ha , a_eq ⟩ , ⟨ ⟨ b₁ , b₂ ⟩ , hb , b_eq ⟩ ⟩
                    =>
                    by
                      simp at a_eq
                        simp at b_eq
                        have h : ⟦ a₂ ⟧ = ⟦ b₁ ⟧ := by rw [ a_eq.right , b_eq.left ]
                        have h : ( a₂ , b₁ ) ∈ 𝓢 α := Quotientₓ.exact h
                        simp [ Function.comp , Set.Image , CompRel , And.comm , And.left_comm , And.assoc ]
                        exact ⟨ a₁ , a_eq.left , b₂ , b_eq.right , a₂ , ha , b₁ , h s hs , hb ⟩
            _
                =
                map
                  fun p : α × α => ( ⟦ p . 1 ⟧ , ⟦ p . 2 ⟧ )
                    u.uniformity.lift' fun s : Set α × α => CompRel s CompRel s s
              :=
              by rw [ map_lift'_eq ] <;> exact monotone_comp_rel monotone_id monotone_comp_rel monotone_id monotone_id
            _ ≤ map fun p : α × α => ( ⟦ p . 1 ⟧ , ⟦ p . 2 ⟧ ) u.uniformity := map_mono comp_le_uniformity3
      is_open_uniformity
        s
        :=
        have
          :
              ∀
                a
                ,
                ⟦ a ⟧ ∈ s
                  →
                  { p : α × α | p . 1 = a → ⟦ p . 2 ⟧ ∈ s } ∈ 𝓤 α ↔ { p : α × α | p . 1 ≈ a → ⟦ p . 2 ⟧ ∈ s } ∈ 𝓤 α
            :=
            fun
              a ha
                =>
                ⟨
                  fun
                      h
                        =>
                        let
                          ⟨ t , ht , hts ⟩ := comp_mem_uniformity_sets h
                          have
                            hts
                              : ∀ { a₁ a₂ } , ( a , a₁ ) ∈ t → ( a₁ , a₂ ) ∈ t → ⟦ a₂ ⟧ ∈ s
                              :=
                              fun a₁ a₂ ha₁ ha₂ => @ hts ( a , a₂ ) ⟨ a₁ , ha₁ , ha₂ ⟩ rfl
                            have
                              ht' : ∀ { a₁ a₂ } , a₁ ≈ a₂ → ( a₁ , a₂ ) ∈ t := fun a₁ a₂ h => sInter_subset_of_mem ht h
                              u.uniformity.sets_of_superset ht $ fun ⟨ a₁ , a₂ ⟩ h₁ h₂ => hts ht' $ Setoidₓ.symm h₂ h₁
                    ,
                    fun
                      h
                        =>
                        u.uniformity.sets_of_superset h
                          $
                          by simp ( config := { contextual := Bool.true._@._internal._hyg.0 } )
                  ⟩
          by
            simp [ TopologicalSpace.coinduced , u.is_open_uniformity , uniformity , forall_quotient_iff ]
              exact ⟨ fun h a ha => this a ha . mp $ h a ha , fun h a ha => this a ha . mpr $ h a ha ⟩

theorem uniformity_quotient : 𝓤 (Quotientₓ (separation_setoid α)) = (𝓤 α).map fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
  rfl

theorem uniform_continuous_quotient_mk : UniformContinuous (Quotientₓ.mk : α → Quotientₓ (separation_setoid α)) :=
  le_reflₓ _

theorem uniform_continuous_quotient {f : Quotientₓ (separation_setoid α) → β}
    (hf : UniformContinuous fun x => f (⟦x⟧)) : UniformContinuous f :=
  hf

theorem uniform_continuous_quotient_lift {f : α → β} {h : ∀ a b, (a, b) ∈ 𝓢 α → f a = f b} (hf : UniformContinuous f) :
    UniformContinuous fun a => Quotientₓ.lift f h a :=
  uniform_continuous_quotient hf

theorem uniform_continuous_quotient_lift₂ {f : α → β → γ} {h : ∀ a c b d, (a, b) ∈ 𝓢 α → (c, d) ∈ 𝓢 β → f a c = f b d}
    (hf : UniformContinuous fun p : α × β => f p.1 p.2) :
    UniformContinuous fun p : _ × _ => Quotientₓ.lift₂ f h p.1 p.2 := by
  rw [UniformContinuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient, Filter.prod_map_map_eq,
    Filter.tendsto_map'_iff, Filter.tendsto_map'_iff]
  rwa [UniformContinuous, uniformity_prod_eq_prod, Filter.tendsto_map'_iff] at hf

theorem comap_quotient_le_uniformity :
    ((𝓤 $ Quotientₓ $ separation_setoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) ≤ 𝓤 α := fun t' ht' =>
  let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht'
  let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht
  ⟨(fun p : α × α => (⟦p.1⟧, ⟦p.2⟧)) '' s, (𝓤 α).sets_of_superset hs $ fun x hx => ⟨x, hx, rfl⟩,
    fun ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩ =>
    have : ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧ := Prod.mk.inj ab_eq
    have : b₁ ≈ a₁ ∧ b₂ ≈ a₂ := And.imp Quotientₓ.exact Quotientₓ.exact this
    have ab₁ : (a₁, b₁) ∈ t := (Setoidₓ.symm this.left) t ht
    have ba₂ : (b₂, a₂) ∈ s := this.right s hs
    tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t from ab₁, ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s from hb, ba₂⟩⟩⟩

theorem comap_quotient_eq_uniformity :
    ((𝓤 $ Quotientₓ $ separation_setoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) = 𝓤 α :=
  le_antisymmₓ comap_quotient_le_uniformity le_comap_map

instance separated_separation : SeparatedSpace (Quotientₓ (separation_setoid α)) :=
  ⟨Set.ext $ fun ⟨a, b⟩ =>
      Quotientₓ.induction_on₂ a b $ fun a b =>
        ⟨fun h =>
          have : a ≈ b := fun s hs =>
            have : s ∈ (𝓤 $ Quotientₓ $ separation_setoid α).comap fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
              comap_quotient_le_uniformity hs
            let ⟨t, ht, hts⟩ := this
            hts
              (by
                dsimp [preimage]
                exact h t ht)
          show ⟦a⟧ = ⟦b⟧ from Quotientₓ.sound this,
          fun heq : ⟦a⟧ = ⟦b⟧ => fun h hs => HEq ▸ refl_mem_uniformity hs⟩⟩

theorem separated_of_uniform_continuous {f : α → β} {x y : α} (H : UniformContinuous f) (h : x ≈ y) : f x ≈ f y :=
  fun _ h' => h _ (H h')

theorem eq_of_separated_of_uniform_continuous [SeparatedSpace β] {f : α → β} {x y : α} (H : UniformContinuous f)
    (h : x ≈ y) : f x = f y :=
  separated_def.1
      (by
        infer_instance)
      _ _ $
    separated_of_uniform_continuous H h

theorem _root_.is_separated.eq_of_uniform_continuous {f : α → β} {x y : α} {s : Set β} (hs : IsSeparated s)
    (hxs : f x ∈ s) (hys : f y ∈ s) (H : UniformContinuous f) (h : x ≈ y) : f x = f y :=
  (is_separated_def _).mp hs _ _ hxs hys $ fun _ h' => h _ (H h')

/--  The maximal separated quotient of a uniform space `α`. -/
def separation_quotient (α : Type _) [UniformSpace α] :=
  Quotientₓ (separation_setoid α)

namespace SeparationQuotient

instance : UniformSpace (separation_quotient α) := by
  dunfold separation_quotient <;> infer_instance

instance : SeparatedSpace (separation_quotient α) := by
  dunfold separation_quotient <;> infer_instance

instance [Inhabited α] : Inhabited (separation_quotient α) := by
  unfold separation_quotient <;> infer_instance

/--  Factoring functions to a separated space through the separation quotient. -/
def lift [SeparatedSpace β] (f : α → β) : separation_quotient α → β :=
  if h : UniformContinuous f then Quotientₓ.lift f fun x y => eq_of_separated_of_uniform_continuous h
  else fun x => f (Nonempty.some ⟨x.out⟩)

theorem lift_mk [SeparatedSpace β] {f : α → β} (h : UniformContinuous f) (a : α) : lift f (⟦a⟧) = f a := by
  rw [lift, dif_pos h] <;> rfl

theorem uniform_continuous_lift [SeparatedSpace β] (f : α → β) : UniformContinuous (lift f) := by
  by_cases' hf : UniformContinuous f
  ·
    rw [lift, dif_pos hf]
    exact uniform_continuous_quotient_lift hf
  ·
    rw [lift, dif_neg hf]
    exact uniform_continuous_of_const fun a b => rfl

/--  The separation quotient functor acting on functions. -/
def map (f : α → β) : separation_quotient α → separation_quotient β :=
  lift (Quotientₓ.mk ∘ f)

theorem map_mk {f : α → β} (h : UniformContinuous f) (a : α) : map f (⟦a⟧) = ⟦f a⟧ := by
  rw [map, lift_mk (uniform_continuous_quotient_mk.comp h)]

theorem uniform_continuous_map (f : α → β) : UniformContinuous (map f) :=
  uniform_continuous_lift (Quotientₓ.mk ∘ f)

theorem map_unique {f : α → β} (hf : UniformContinuous f) {g : separation_quotient α → separation_quotient β}
    (comm : (Quotientₓ.mk ∘ f) = (g ∘ Quotientₓ.mk)) : map f = g := by
  ext ⟨a⟩ <;> calc map f (⟦a⟧) = ⟦f a⟧ := map_mk hf a _ = g (⟦a⟧) := congr_funₓ comm a

theorem map_id : map (@id α) = id :=
  map_unique uniform_continuous_id rfl

theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    (map g ∘ map f) = map (g ∘ f) :=
  (map_unique (hg.comp hf) $ by
      simp only [· ∘ ·, map_mk, hf, hg]).symm

end SeparationQuotient

theorem separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ := by
  constructor
  ·
    intro h
    exact
      ⟨separated_of_uniform_continuous uniform_continuous_fst h,
        separated_of_uniform_continuous uniform_continuous_snd h⟩
  ·
    rintro ⟨eqv_α, eqv_β⟩ r r_in
    rw [uniformity_prod] at r_in
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, rfl⟩
    let p_α := fun p : (α × β) × α × β => (p.1.1, p.2.1)
    let p_β := fun p : (α × β) × α × β => (p.1.2, p.2.2)
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α := by
      simp [p_α, eqv_α r_α r_α_in]
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β := by
      simp [p_β, eqv_β r_β r_β_in]
    exact ⟨h_α key_α, h_β key_β⟩

instance separated.prod [SeparatedSpace α] [SeparatedSpace β] : SeparatedSpace (α × β) :=
  separated_def.2 $ fun x y H =>
    Prod.extₓ (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
      (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)

theorem _root_.is_separated.prod {s : Set α} {t : Set β} (hs : IsSeparated s) (ht : IsSeparated t) :
    IsSeparated (s.prod t) :=
  (is_separated_def _).mpr $ fun x y hx hy H =>
    Prod.extₓ (hs.eq_of_uniform_continuous hx.1 hy.1 uniform_continuous_fst H)
      (ht.eq_of_uniform_continuous hx.2 hy.2 uniform_continuous_snd H)

end UniformSpace

