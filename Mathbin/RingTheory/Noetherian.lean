import Mathbin.GroupTheory.Finiteness
import Mathbin.Data.Multiset.FinsetOps
import Mathbin.Algebra.Algebra.Tower
import Mathbin.Order.OrderIsoNat
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.Order.CompactlyGenerated
import Mathbin.LinearAlgebra.LinearIndependent

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `submodule.fg N : Prop` is the assertion that `N` is finitely generated as an `R`-module.

* `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

* `is_noetherian_iff_well_founded` is the theorem that an R-module M is Noetherian iff
  `>` is well-founded on `submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `ring_theory.polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/


open Set

open_locale BigOperators Pointwise

namespace Submodule

variable {R : Type _} {M : Type _} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

/--  A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def fg (N : Submodule R M) : Prop :=
  ∃ S : Finset M, Submodule.span R (↑S) = N

theorem fg_def {N : Submodule R M} : N.fg ↔ ∃ S : Set M, finite S ∧ span R S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_to_set t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩

theorem fg_iff_add_submonoid_fg (P : Submodule ℕ M) : P.fg ↔ P.to_add_submonoid.fg :=
  ⟨fun ⟨S, hS⟩ =>
    ⟨S, by
      simpa [← span_nat_eq_add_submonoid_closure] using hS⟩,
    fun ⟨S, hS⟩ =>
    ⟨S, by
      simpa [← span_nat_eq_add_submonoid_closure] using hS⟩⟩

theorem fg_iff_add_subgroup_fg {G : Type _} [AddCommGroupₓ G] (P : Submodule ℤ G) : P.fg ↔ P.to_add_subgroup.fg :=
  ⟨fun ⟨S, hS⟩ =>
    ⟨S, by
      simpa [← span_int_eq_add_subgroup_closure] using hS⟩,
    fun ⟨S, hS⟩ =>
    ⟨S, by
      simpa [← span_int_eq_add_subgroup_closure] using hS⟩⟩

theorem fg_iff_exists_fin_generating_family {N : Submodule R M} :
    N.fg ↔ ∃ (n : ℕ)(s : Finₓ n → M), span R (range s) = N := by
  rw [fg_def]
  constructor
  ·
    rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  ·
    rintro ⟨n, s, hs⟩
    refine' ⟨range s, finite_range s, hs⟩

/--  **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2,
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV) -/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type _} [CommRingₓ R] {M : Type _} [AddCommGroupₓ M]
    [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.fg) (hin : N ≤ I • N) :
    ∃ r : R, r - 1 ∈ I ∧ ∀, ∀ n ∈ N, ∀, r • n = (0 : M) := by
  rw [fg_def] at hn
  rcases hn with ⟨s, hfs, hs⟩
  have : ∃ r : R, r - 1 ∈ I ∧ N ≤ (I • span R s).comap (LinearMap.lsmul R M r) ∧ s ⊆ N := by
    refine' ⟨1, _, _, _⟩
    ·
      rw [sub_self]
      exact I.zero_mem
    ·
      rw [hs]
      intro n hn
      rw [mem_comap]
      change (1 : R) • n ∈ I • N
      rw [one_smul]
      exact hin hn
    ·
      rw [← span_le, hs]
      exact le_reflₓ N
  clear hin hs
  revert this
  refine' Set.Finite.dinduction_on hfs (fun H => _) fun i s his hfs ih H => _
  ·
    rcases H with ⟨r, hr1, hrn, hs⟩
    refine' ⟨r, hr1, fun n hn => _⟩
    specialize hrn hn
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn
  apply ih
  rcases H with ⟨r, hr1, hrn, hs⟩
  rw [← Set.singleton_union, span_union, smul_sup] at hrn
  rw [Set.insert_subset] at hs
  have : ∃ c : R, c - 1 ∈ I ∧ c • i ∈ I • span R s := by
    specialize hrn hs.1
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    change (y+z) = r • i at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨c, hci, rfl⟩
    use r - c
    constructor
    ·
      rw [sub_right_comm]
      exact I.sub_mem hr1 hci
    ·
      rw [sub_smul, ← hyz, add_sub_cancel']
      exact hz
  rcases this with ⟨c, hc1, hci⟩
  refine' ⟨c*r, _, _, hs.2⟩
  ·
    rw [← Ideal.Quotient.eq, RingHom.map_one] at hr1 hc1⊢
    rw [RingHom.map_mul, hc1, hr1, mul_oneₓ]
  ·
    intro n hn
    specialize hrn hn
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    change (y+z) = r • n at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨d, hdi, rfl⟩
    change _ • _ ∈ I • span R s
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_commₓ, mul_smul]
    exact add_mem _ (smul_mem _ _ hci) (smul_mem _ _ hz)

theorem fg_bot : (⊥ : Submodule R M).Fg :=
  ⟨∅, by
    rw [Finset.coe_empty, span_empty]⟩

theorem fg_span {s : Set M} (hs : finite s) : fg (span R s) :=
  ⟨hs.to_finset, by
    rw [hs.coe_to_finset]⟩

theorem fg_span_singleton (x : M) : fg (R∙x) :=
  fg_span (finite_singleton x)

theorem fg_sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.fg) (hN₂ : N₂.fg) : (N₁⊔N₂).Fg :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2
    ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by
      rw [span_union, ht₁.2, ht₂.2]⟩

variable {P : Type _} [AddCommMonoidₓ P] [Module R P]

variable (f : M →ₗ[R] P)

theorem fg.map {N : Submodule R M} (hs : N.fg) : (N.map f).Fg :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2
    ⟨f '' t, ht.1.Image _, by
      rw [span_image, ht.2]⟩

variable {f}

theorem fg_of_fg_map_injective (f : M →ₗ[R] P) (hf : Function.Injective f) {N : Submodule R M} (hfn : (N.map f).Fg) :
    N.fg :=
  let ⟨t, ht⟩ := hfn
  ⟨t.preimage f $ fun x _ y _ h => hf h,
    Submodule.map_injective_of_injective hf $ by
      rw [f.map_span, Finset.coe_preimage, Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left, ht]
      rw [← LinearMap.range_coe, ← span_le, ht, ← map_top]
      exact map_mono le_top⟩

theorem fg_of_fg_map {R M P : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ P] [Module R P]
    (f : M →ₗ[R] P) (hf : f.ker = ⊥) {N : Submodule R M} (hfn : (N.map f).Fg) : N.fg :=
  fg_of_fg_map_injective f (LinearMap.ker_eq_bot.1 hf) hfn

theorem fg_top (N : Submodule R M) : (⊤ : Submodule R N).Fg ↔ N.fg :=
  ⟨fun h => N.range_subtype ▸ map_top N.subtype ▸ h.map _, fun h =>
    fg_of_fg_map_injective N.subtype Subtype.val_injective $ by
      rwa [map_top, range_subtype]⟩

theorem fg_of_linear_equiv (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).Fg) : (⊤ : Submodule R M).Fg :=
  e.symm.range ▸ map_top (e.symm : P →ₗ[R] M) ▸ h.map _

theorem fg_prod {sb : Submodule R M} {sc : Submodule R P} (hsb : sb.fg) (hsc : sc.fg) : (sb.prod sc).Fg :=
  let ⟨tb, htb⟩ := fg_def.1 hsb
  let ⟨Tc, htc⟩ := fg_def.1 hsc
  fg_def.2
    ⟨LinearMap.inl R M P '' tb ∪ LinearMap.inr R M P '' Tc, (htb.1.Image _).union (htc.1.Image _), by
      rw [LinearMap.span_inl_union_inr, htb.2, htc.2]⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `fg_pi [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.implicitBinder "{" [`M] [":" (Term.arrow `ι "→" (Term.type "Type" [(Level.hole "_")]))] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`ι]) "]")
    (Term.instBinder
     "["
     []
     (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `AddCommMonoidₓ [(Term.app `M [`i])]))
     "]")
    (Term.instBinder
     "["
     []
     (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `Module [`R (Term.app `M [`i])]))
     "]")
    (Term.implicitBinder
     "{"
     [`p]
     [":" (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `Submodule [`R (Term.app `M [`i])]))]
     "}")
    (Term.explicitBinder
     "("
     [`hsb]
     [":" (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.proj (Term.app `p [`i]) "." `Fg))]
     []
     ")")]
   (Term.typeSpec ":" (Term.proj (Term.app `Submodule.pi [`Set.Univ `p]) "." `Fg)))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.classical "classical") [])
       (group
        (Tactic.simpRw
         "simp_rw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `fg_def)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hsb] ["⊢"]))])
        [])
       (group (Tactic.choose "choose" [`t `htf `hts] ["using" `hsb]) [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            ", "
            (Set.Data.Set.Basic.term_''_
             (Term.paren
              "("
              [(Term.app `LinearMap.single [`i])
               [(Term.typeAscription
                 ":"
                 (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.hole "_") " →ₗ[" `R "] " (Term.hole "_")))]]
              ")")
             " '' "
             (Term.app `t [`i])))
           ","
           («term_$__»
            `Set.finite_Union
            "$"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`i] [])]
              "=>"
              (Term.app (Term.proj (Term.app `htf [`i]) "." `Image) [(Term.hole "_")]))))
           ","
           (Term.hole "_")]
          "⟩"))
        [])
       (group
        (Tactic.simpRw
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `span_Union)
           ","
           (Tactic.rwRule [] `span_image)
           ","
           (Tactic.rwRule [] `hts)
           ","
           (Tactic.rwRule [] `Submodule.supr_map_single)]
          "]")
         [])
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
     [(group (Tactic.classical "classical") [])
      (group
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `fg_def)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hsb] ["⊢"]))])
       [])
      (group (Tactic.choose "choose" [`t `htf `hts] ["using" `hsb]) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Set.Data.Set.Lattice.«term⋃_,_»
           "⋃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
           ", "
           (Set.Data.Set.Basic.term_''_
            (Term.paren
             "("
             [(Term.app `LinearMap.single [`i])
              [(Term.typeAscription
                ":"
                (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.hole "_") " →ₗ[" `R "] " (Term.hole "_")))]]
             ")")
            " '' "
            (Term.app `t [`i])))
          ","
          («term_$__»
           `Set.finite_Union
           "$"
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`i] [])]
             "=>"
             (Term.app (Term.proj (Term.app `htf [`i]) "." `Image) [(Term.hole "_")]))))
          ","
          (Term.hole "_")]
         "⟩"))
       [])
      (group
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `span_Union)
          ","
          (Tactic.rwRule [] `span_image)
          ","
          (Tactic.rwRule [] `hts)
          ","
          (Tactic.rwRule [] `Submodule.supr_map_single)]
         "]")
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
  (Tactic.simpRw
   "simp_rw"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `span_Union)
     ","
     (Tactic.rwRule [] `span_image)
     ","
     (Tactic.rwRule [] `hts)
     ","
     (Tactic.rwRule [] `Submodule.supr_map_single)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Submodule.supr_map_single
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hts
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `span_image
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `span_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Set.Data.Set.Lattice.«term⋃_,_»
      "⋃"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      ", "
      (Set.Data.Set.Basic.term_''_
       (Term.paren
        "("
        [(Term.app `LinearMap.single [`i])
         [(Term.typeAscription
           ":"
           (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.hole "_") " →ₗ[" `R "] " (Term.hole "_")))]]
        ")")
       " '' "
       (Term.app `t [`i])))
     ","
     («term_$__»
      `Set.finite_Union
      "$"
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`i] [])]
        "=>"
        (Term.app (Term.proj (Term.app `htf [`i]) "." `Image) [(Term.hole "_")]))))
     ","
     (Term.hole "_")]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Set.Data.Set.Lattice.«term⋃_,_»
     "⋃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     ", "
     (Set.Data.Set.Basic.term_''_
      (Term.paren
       "("
       [(Term.app `LinearMap.single [`i])
        [(Term.typeAscription
          ":"
          (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.hole "_") " →ₗ[" `R "] " (Term.hole "_")))]]
       ")")
      " '' "
      (Term.app `t [`i])))
    ","
    («term_$__»
     `Set.finite_Union
     "$"
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i] [])]
       "=>"
       (Term.app (Term.proj (Term.app `htf [`i]) "." `Image) [(Term.hole "_")]))))
    ","
    (Term.hole "_")]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `Set.finite_Union
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`i] [])]
     "=>"
     (Term.app (Term.proj (Term.app `htf [`i]) "." `Image) [(Term.hole "_")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.app (Term.proj (Term.app `htf [`i]) "." `Image) [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `htf [`i]) "." `Image) [(Term.hole "_")])
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
  (Term.proj (Term.app `htf [`i]) "." `Image)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `htf [`i])
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
  `htf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `htf [`i]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `Set.finite_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Set.Data.Set.Basic.term_''_
    (Term.paren
     "("
     [(Term.app `LinearMap.single [`i])
      [(Term.typeAscription
        ":"
        (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.hole "_") " →ₗ[" `R "] " (Term.hole "_")))]]
     ")")
    " '' "
    (Term.app `t [`i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.term_''_
   (Term.paren
    "("
    [(Term.app `LinearMap.single [`i])
     [(Term.typeAscription
       ":"
       (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.hole "_") " →ₗ[" `R "] " (Term.hole "_")))]]
    ")")
   " '' "
   (Term.app `t [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `t [`i])
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
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.paren
   "("
   [(Term.app `LinearMap.single [`i])
    [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.hole "_") " →ₗ[" `R "] " (Term.hole "_")))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.hole "_") " →ₗ[" `R "] " (Term.hole "_"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Module.LinearMap.«term_→ₗ[_]_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `LinearMap.single [`i])
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
  `LinearMap.single
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  fg_pi
  { ι : Type _ }
      { M : ι → Type _ }
      [ Fintype ι ]
      [ ∀ i , AddCommMonoidₓ M i ]
      [ ∀ i , Module R M i ]
      { p : ∀ i , Submodule R M i }
      ( hsb : ∀ i , p i . Fg )
    : Submodule.pi Set.Univ p . Fg
  :=
    by
      classical
        simp_rw [ fg_def ] at hsb ⊢
        choose t htf hts using hsb
        refine' ⟨ ⋃ i , ( LinearMap.single i : _ →ₗ[ R ] _ ) '' t i , Set.finite_Union $ fun i => htf i . Image _ , _ ⟩
        simp_rw [ span_Union , span_image , hts , Submodule.supr_map_single ]

/--  If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker {R M P : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ P]
    [Module R P] (f : M →ₗ[R] P) {s : Submodule R M} (hs1 : (s.map f).Fg) (hs2 : (s⊓f.ker).Fg) : s.fg := by
  have := Classical.decEq R
  have := Classical.decEq M
  have := Classical.decEq P
  cases' hs1 with t1 ht1
  cases' hs2 with t2 ht2
  have : ∀, ∀ y ∈ t1, ∀, ∃ x ∈ s, f x = y := by
    intro y hy
    have : y ∈ map f s := by
      rw [← ht1]
      exact subset_span hy
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  have : ∃ g : P → M, ∀, ∀ y ∈ t1, ∀, g y ∈ s ∧ f (g y) = y := by
    choose g hg1 hg2
    exists fun y => if H : y ∈ t1 then g y H else 0
    intro y H
    constructor
    ·
      simp only [dif_pos H]
      apply hg1
    ·
      simp only [dif_pos H]
      apply hg2
  cases' this with g hg
  clear this
  exists t1.image g ∪ t2
  rw [Finset.coe_union, span_union, Finset.coe_image]
  apply le_antisymmₓ
  ·
    refine' sup_le (span_le.2 $ image_subset_iff.2 _) (span_le.2 _)
    ·
      intro y hy
      exact (hg y hy).1
    ·
      intro x hx
      have := subset_span hx
      rw [ht2] at this
      exact this.1
  intro x hx
  have : f x ∈ map f s := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1, ← Set.image_id (↑t1), Finsupp.mem_span_image_iff_total] at this
  rcases this with ⟨l, hl1, hl2⟩
  refine'
    mem_sup.2
      ⟨(Finsupp.total M M R id).toFun ((Finsupp.lmapDomain R R g : (P →₀ R) → M →₀ R) l), _,
        x - Finsupp.total M M R id ((Finsupp.lmapDomain R R g : (P →₀ R) → M →₀ R) l), _, add_sub_cancel'_right _ _⟩
  ·
    rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_total]
    refine' ⟨_, _, rfl⟩
    have : Inhabited P := ⟨0⟩
    rw [← Finsupp.lmap_domain_supported _ _ g, mem_map]
    refine' ⟨l, hl1, _⟩
    rfl
  rw [ht2, mem_inf]
  constructor
  ·
    apply s.sub_mem hx
    rw [Finsupp.total_apply, Finsupp.lmap_domain_apply, Finsupp.sum_map_domain_index]
    refine' s.sum_mem _
    ·
      intro y hy
      exact s.smul_mem _ (hg y (hl1 hy)).1
    ·
      exact zero_smul _
    ·
      exact fun _ _ _ => add_smul _ _ _
  ·
    rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    rw [Finsupp.total_apply, Finsupp.total_apply, Finsupp.lmap_domain_apply]
    rw [Finsupp.sum_map_domain_index, Finsupp.sum, Finsupp.sum, f.map_sum]
    rw [sub_eq_zero]
    refine' Finset.sum_congr rfl fun y hy => _
    unfold id
    rw [f.map_smul, (hg y (hl1 hy)).2]
    ·
      exact zero_smul _
    ·
      exact fun _ _ _ => add_smul _ _ _

/--  An ideal of `R` is finitely generated if it is the span of a finite subset of `R`.

This is defeq to `submodule.fg`, but unfolds more nicely. -/
def _root_.ideal.fg (I : Ideal R) : Prop :=
  ∃ S : Finset R, Ideal.span (↑S) = I

/--  The image of a finitely generated ideal is finitely generated.

This is the `ideal` version of `submodule.fg.map`. -/
theorem _root_.ideal.fg.map {R S : Type _} [Semiringₓ R] [Semiringₓ S] {I : Ideal R} (h : I.fg) (f : R →+* S) :
    (I.map f).Fg := by
  classical
  obtain ⟨s, hs⟩ := h
  refine' ⟨s.image f, _⟩
  rw [Finset.coe_image, ← Ideal.map_span, hs]

/--  The kernel of the composition of two linear maps is finitely generated if both kernels are and
the first morphism is surjective. -/
theorem fg_ker_comp {R M N P : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ N] [Module R N]
    [AddCommGroupₓ P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf1 : f.ker.fg) (hf2 : g.ker.fg)
    (hsur : Function.Surjective f) : (g.comp f).ker.Fg := by
  rw [LinearMap.ker_comp]
  apply fg_of_fg_map_of_fg_inf_ker f
  ·
    rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
  ·
    rwa [inf_of_le_right (show f.ker ≤ comap f g.ker from comap_mono bot_le)]

theorem fg_restrict_scalars {R S M : Type _} [CommRingₓ R] [CommRingₓ S] [Algebra R S] [AddCommGroupₓ M] [Module S M]
    [Module R M] [IsScalarTower R S M] (N : Submodule S M) (hfin : N.fg) (h : Function.Surjective (algebraMap R S)) :
    (Submodule.restrictScalars R N).Fg := by
  obtain ⟨X, rfl⟩ := hfin
  use X
  exact Submodule.span_eq_restrict_scalars R S M X h

theorem _root_.ideal.fg_ker_comp {R S A : Type _} [CommRingₓ R] [CommRingₓ S] [CommRingₓ A] (f : R →+* S) (g : S →+* A)
    (hf : f.ker.fg) (hg : g.ker.fg) (hsur : Function.Surjective f) : (g.comp f).ker.Fg := by
  let this' : Algebra R S := RingHom.toAlgebra f
  let this' : Algebra R A := RingHom.toAlgebra (g.comp f)
  let this' : Algebra S A := RingHom.toAlgebra g
  let this' : IsScalarTower R S A := IsScalarTower.of_algebra_map_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  exact fg_ker_comp f₁ g₁ hf (fg_restrict_scalars g.ker hg hsur) hsur

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (x «expr ∈ » t)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (x «expr ∈ » («expr↑ »(t) : set M))
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Finitely generated submodules are precisely compact elements in the submodule lattice. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `fg_iff_compact [])
  (Command.declSig
   [(Term.explicitBinder "(" [`s] [":" (Term.app `Submodule [`R `M])] [] ")")]
   (Term.typeSpec ":" («term_↔_» `s.fg "↔" (Term.app `CompleteLattice.IsCompactElement [`s]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.classical "classical") [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `sp
           [(Term.typeSpec ":" (Term.arrow `M "→" (Term.app `Submodule [`R `M])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.app `span [`R (Set.«term{_}» "{" [`a] "}")]))))))
        [])
       (group
        (Tactic.have''
         "have"
         [`supr_rw []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.simpleBinder [`t] [(Term.typeSpec ":" (Term.app `Finset [`M]))])]
            ","
            («term_=_»
             (Order.CompleteLattice.«term⨆_,_»
              "⨆"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
              ", "
              (Term.app `sp [`x]))
             "="
             (Order.CompleteLattice.«term⨆_,_»
              "⨆"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
                (Lean.bracketedExplicitBinders
                 "("
                 [(Lean.binderIdent "_")]
                 ":"
                 (Init.Core.«term_∈_»
                  `x
                  " ∈ "
                  (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
                 ")")])
              ", "
              (Term.app `sp [`x])))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`t] [])]
           "=>"
           (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])]))))))
        [])
       (group (Tactic.constructor "constructor") [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rintro
              "rintro"
              [(Tactic.rintroPat.one
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `span_eq_supr_of_singleton_spans)
                ","
                (Tactic.rwRule ["←"] `supr_rw)
                ","
                (Tactic.rwRule ["←"] (Term.app `Finset.sup_eq_supr [`t `sp]))]
               "]")
              [])
             [])
            (group (Tactic.apply "apply" `CompleteLattice.finset_sup_compact_of_compact) [])
            (group
             (Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`n (Term.hole "_")] [])]
                "=>"
                (Term.app `singleton_span_is_compact_element [`n]))))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`h]) [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`sSup []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   `s
                   "="
                   (Term.app `Sup [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s))])))]
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
                       [(Tactic.rwRule [] `Sup_eq_supr)
                        ","
                        (Tactic.rwRule [] `supr_image)
                        ","
                        (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
                        ","
                        (Tactic.rwRule [] `eq_comm)
                        ","
                        (Tactic.rwRule [] `span_eq)]
                       "]")
                      [])
                     [])]))))))
             [])
            (group
             (Tactic.obtain
              "obtain"
              [(Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `u)]) [])
                   ","
                   (Tactic.rcasesPatLo
                    (Tactic.rcasesPatMed
                     [(Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `huspan)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `husup)]) [])]
                       "⟩")])
                    [])]
                  "⟩")])]
              []
              [":="
               [(Term.app
                 `h
                 [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s)) (Term.app `le_of_eqₓ [`sSup])])]])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`ssup []]
                [(Term.typeSpec ":" («term_=_» `s "=" (Term.app `u.sup [`id])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.suffices' "suffices" [] [(Term.typeSpec ":" («term_≤_» (Term.app `u.sup [`id]) "≤" `s))])
                     [])
                    (group (Tactic.exact "exact" (Term.app `le_antisymmₓ [`husup `this])) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sSup) "," (Tactic.rwRule [] `Finset.sup_id_eq_Sup)] "]")
                      [])
                     [])
                    (group (Tactic.exact "exact" (Term.app `Sup_le_Sup [`huspan])) [])]))))))
             [])
            (group
             (Tactic.obtain
              "obtain"
              [(Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
                   ","
                   (Tactic.rcasesPatLo
                    (Tactic.rcasesPatMed
                     [(Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hts)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                       "⟩")])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `finset.subset_image_iff.mp [`huspan])]])
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Finset.sup_finset_image)
                ","
                (Tactic.rwRule [] `Function.comp.left_id)
                ","
                (Tactic.rwRule [] `Finset.sup_eq_supr)
                ","
                (Tactic.rwRule [] `supr_rw)
                ","
                (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
                ","
                (Tactic.rwRule [] `eq_comm)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`ssup] []))])
             [])
            (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`t "," `ssup] "⟩")) [])])))
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
     [(group (Tactic.classical "classical") [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `sp
          [(Term.typeSpec ":" (Term.arrow `M "→" (Term.app `Submodule [`R `M])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.app `span [`R (Set.«term{_}» "{" [`a] "}")]))))))
       [])
      (group
       (Tactic.have''
        "have"
        [`supr_rw []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`t] [(Term.typeSpec ":" (Term.app `Finset [`M]))])]
           ","
           («term_=_»
            (Order.CompleteLattice.«term⨆_,_»
             "⨆"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
               (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
             ", "
             (Term.app `sp [`x]))
            "="
            (Order.CompleteLattice.«term⨆_,_»
             "⨆"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
               (Lean.bracketedExplicitBinders
                "("
                [(Lean.binderIdent "_")]
                ":"
                (Init.Core.«term_∈_»
                 `x
                 " ∈ "
                 (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
                ")")])
             ", "
             (Term.app `sp [`x])))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`t] [])]
          "=>"
          (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])]))))))
       [])
      (group (Tactic.constructor "constructor") [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                "⟩"))]
             [])
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `span_eq_supr_of_singleton_spans)
               ","
               (Tactic.rwRule ["←"] `supr_rw)
               ","
               (Tactic.rwRule ["←"] (Term.app `Finset.sup_eq_supr [`t `sp]))]
              "]")
             [])
            [])
           (group (Tactic.apply "apply" `CompleteLattice.finset_sup_compact_of_compact) [])
           (group
            (Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`n (Term.hole "_")] [])]
               "=>"
               (Term.app `singleton_span_is_compact_element [`n]))))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`h]) [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`sSup []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  `s
                  "="
                  (Term.app `Sup [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s))])))]
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
                      [(Tactic.rwRule [] `Sup_eq_supr)
                       ","
                       (Tactic.rwRule [] `supr_image)
                       ","
                       (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
                       ","
                       (Tactic.rwRule [] `eq_comm)
                       ","
                       (Tactic.rwRule [] `span_eq)]
                      "]")
                     [])
                    [])]))))))
            [])
           (group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `u)]) [])
                  ","
                  (Tactic.rcasesPatLo
                   (Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `huspan)]) [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `husup)]) [])]
                      "⟩")])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                `h
                [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s)) (Term.app `le_of_eqₓ [`sSup])])]])
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`ssup []]
               [(Term.typeSpec ":" («term_=_» `s "=" (Term.app `u.sup [`id])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.suffices' "suffices" [] [(Term.typeSpec ":" («term_≤_» (Term.app `u.sup [`id]) "≤" `s))])
                    [])
                   (group (Tactic.exact "exact" (Term.app `le_antisymmₓ [`husup `this])) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sSup) "," (Tactic.rwRule [] `Finset.sup_id_eq_Sup)] "]")
                     [])
                    [])
                   (group (Tactic.exact "exact" (Term.app `Sup_le_Sup [`huspan])) [])]))))))
            [])
           (group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
                  ","
                  (Tactic.rcasesPatLo
                   (Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hts)]) [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                      "⟩")])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `finset.subset_image_iff.mp [`huspan])]])
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Finset.sup_finset_image)
               ","
               (Tactic.rwRule [] `Function.comp.left_id)
               ","
               (Tactic.rwRule [] `Finset.sup_eq_supr)
               ","
               (Tactic.rwRule [] `supr_rw)
               ","
               (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
               ","
               (Tactic.rwRule [] `eq_comm)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`ssup] []))])
            [])
           (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`t "," `ssup] "⟩")) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`h]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`sSup []]
          [(Term.typeSpec
            ":"
            («term_=_» `s "=" (Term.app `Sup [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s))])))]
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
                 [(Tactic.rwRule [] `Sup_eq_supr)
                  ","
                  (Tactic.rwRule [] `supr_image)
                  ","
                  (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
                  ","
                  (Tactic.rwRule [] `eq_comm)
                  ","
                  (Tactic.rwRule [] `span_eq)]
                 "]")
                [])
               [])]))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `u)]) [])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `huspan)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `husup)]) [])]
                 "⟩")])
              [])]
            "⟩")])]
        []
        [":="
         [(Term.app
           `h
           [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s)) (Term.app `le_of_eqₓ [`sSup])])]])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`ssup []]
          [(Term.typeSpec ":" («term_=_» `s "=" (Term.app `u.sup [`id])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.suffices' "suffices" [] [(Term.typeSpec ":" («term_≤_» (Term.app `u.sup [`id]) "≤" `s))])
               [])
              (group (Tactic.exact "exact" (Term.app `le_antisymmₓ [`husup `this])) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sSup) "," (Tactic.rwRule [] `Finset.sup_id_eq_Sup)] "]")
                [])
               [])
              (group (Tactic.exact "exact" (Term.app `Sup_le_Sup [`huspan])) [])]))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hts)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                 "⟩")])
              [])]
            "⟩")])]
        []
        [":=" [(Term.app `finset.subset_image_iff.mp [`huspan])]])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Finset.sup_finset_image)
          ","
          (Tactic.rwRule [] `Function.comp.left_id)
          ","
          (Tactic.rwRule [] `Finset.sup_eq_supr)
          ","
          (Tactic.rwRule [] `supr_rw)
          ","
          (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
          ","
          (Tactic.rwRule [] `eq_comm)]
         "]")
        [(Tactic.location "at" (Tactic.locationHyp [`ssup] []))])
       [])
      (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`t "," `ssup] "⟩")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`t "," `ssup] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`t "," `ssup] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ssup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `Finset.sup_finset_image)
     ","
     (Tactic.rwRule [] `Function.comp.left_id)
     ","
     (Tactic.rwRule [] `Finset.sup_eq_supr)
     ","
     (Tactic.rwRule [] `supr_rw)
     ","
     (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
     ","
     (Tactic.rwRule [] `eq_comm)]
    "]")
   [(Tactic.location "at" (Tactic.locationHyp [`ssup] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ssup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_comm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `span_eq_supr_of_singleton_spans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `supr_rw
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sup_eq_supr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Function.comp.left_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sup_finset_image
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
        ","
        (Tactic.rcasesPatLo
         (Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hts)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
            "⟩")])
         [])]
       "⟩")])]
   []
   [":=" [(Term.app `finset.subset_image_iff.mp [`huspan])]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finset.subset_image_iff.mp [`huspan])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `huspan
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finset.subset_image_iff.mp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatMed', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`ssup []]
     [(Term.typeSpec ":" («term_=_» `s "=" (Term.app `u.sup [`id])))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.suffices' "suffices" [] [(Term.typeSpec ":" («term_≤_» (Term.app `u.sup [`id]) "≤" `s))]) [])
         (group (Tactic.exact "exact" (Term.app `le_antisymmₓ [`husup `this])) [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sSup) "," (Tactic.rwRule [] `Finset.sup_id_eq_Sup)] "]")
           [])
          [])
         (group (Tactic.exact "exact" (Term.app `Sup_le_Sup [`huspan])) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.suffices' "suffices" [] [(Term.typeSpec ":" («term_≤_» (Term.app `u.sup [`id]) "≤" `s))]) [])
      (group (Tactic.exact "exact" (Term.app `le_antisymmₓ [`husup `this])) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sSup) "," (Tactic.rwRule [] `Finset.sup_id_eq_Sup)] "]")
        [])
       [])
      (group (Tactic.exact "exact" (Term.app `Sup_le_Sup [`huspan])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `Sup_le_Sup [`huspan]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sup_le_Sup [`huspan])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `huspan
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Sup_le_Sup
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
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sSup) "," (Tactic.rwRule [] `Finset.sup_id_eq_Sup)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sup_id_eq_Sup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sSup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.exact "exact" (Term.app `le_antisymmₓ [`husup `this]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_antisymmₓ [`husup `this])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `husup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_antisymmₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.suffices' "suffices" [] [(Term.typeSpec ":" («term_≤_» (Term.app `u.sup [`id]) "≤" `s))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.suffices'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.app `u.sup [`id]) "≤" `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `u.sup [`id])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `u.sup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `s "=" (Term.app `u.sup [`id]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `u.sup [`id])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `u.sup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `u)]) [])
        ","
        (Tactic.rcasesPatLo
         (Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `huspan)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `husup)]) [])]
            "⟩")])
         [])]
       "⟩")])]
   []
   [":="
    [(Term.app
      `h
      [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s)) (Term.app `le_of_eqₓ [`sSup])])]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s)) (Term.app `le_of_eqₓ [`sSup])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_of_eqₓ [`sSup])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sSup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_of_eqₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_of_eqₓ [`sSup]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `sp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatMed', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`sSup []]
     [(Term.typeSpec
       ":"
       («term_=_» `s "=" (Term.app `Sup [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s))])))]
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
            [(Tactic.rwRule [] `Sup_eq_supr)
             ","
             (Tactic.rwRule [] `supr_image)
             ","
             (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
             ","
             (Tactic.rwRule [] `eq_comm)
             ","
             (Tactic.rwRule [] `span_eq)]
            "]")
           [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
         [(Tactic.rwRule [] `Sup_eq_supr)
          ","
          (Tactic.rwRule [] `supr_image)
          ","
          (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
          ","
          (Tactic.rwRule [] `eq_comm)
          ","
          (Tactic.rwRule [] `span_eq)]
         "]")
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
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `Sup_eq_supr)
     ","
     (Tactic.rwRule [] `supr_image)
     ","
     (Tactic.rwRule ["←"] `span_eq_supr_of_singleton_spans)
     ","
     (Tactic.rwRule [] `eq_comm)
     ","
     (Tactic.rwRule [] `span_eq)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `span_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_comm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `span_eq_supr_of_singleton_spans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `supr_image
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Sup_eq_supr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `s "=" (Term.app `Sup [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sup [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `sp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Set.Data.Set.Basic.term_''_ `sp " '' " (Init.Coe.«term↑_» "↑" `s)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Sup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
           "⟩"))]
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `span_eq_supr_of_singleton_spans)
          ","
          (Tactic.rwRule ["←"] `supr_rw)
          ","
          (Tactic.rwRule ["←"] (Term.app `Finset.sup_eq_supr [`t `sp]))]
         "]")
        [])
       [])
      (group (Tactic.apply "apply" `CompleteLattice.finset_sup_compact_of_compact) [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`n (Term.hole "_")] [])]
          "=>"
          (Term.app `singleton_span_is_compact_element [`n]))))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`n (Term.hole "_")] [])]
     "=>"
     (Term.app `singleton_span_is_compact_element [`n]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`n (Term.hole "_")] [])]
    "=>"
    (Term.app `singleton_span_is_compact_element [`n])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `singleton_span_is_compact_element [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `singleton_span_is_compact_element
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `CompleteLattice.finset_sup_compact_of_compact)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `CompleteLattice.finset_sup_compact_of_compact
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `span_eq_supr_of_singleton_spans)
     ","
     (Tactic.rwRule ["←"] `supr_rw)
     ","
     (Tactic.rwRule ["←"] (Term.app `Finset.sup_eq_supr [`t `sp]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.sup_eq_supr [`t `sp])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sup_eq_supr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `supr_rw
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `span_eq_supr_of_singleton_spans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
      "⟩"))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.constructor', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.exact
   "exact"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`t] [])]
     "=>"
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`t] [])]
    "=>"
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.have''
   "have"
   [`supr_rw []]
   [(Term.typeSpec
     ":"
     (Term.forall
      "∀"
      [(Term.simpleBinder [`t] [(Term.typeSpec ":" (Term.app `Finset [`M]))])]
      ","
      («term_=_»
       (Order.CompleteLattice.«term⨆_,_»
        "⨆"
        (Lean.explicitBinders
         [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
          (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
        ", "
        (Term.app `sp [`x]))
       "="
       (Order.CompleteLattice.«term⨆_,_»
        "⨆"
        (Lean.explicitBinders
         [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
          (Lean.bracketedExplicitBinders
           "("
           [(Lean.binderIdent "_")]
           ":"
           (Init.Core.«term_∈_»
            `x
            " ∈ "
            (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
           ")")])
        ", "
        (Term.app `sp [`x])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.have''', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`t] [(Term.typeSpec ":" (Term.app `Finset [`M]))])]
   ","
   («term_=_»
    (Order.CompleteLattice.«term⨆_,_»
     "⨆"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
     ", "
     (Term.app `sp [`x]))
    "="
    (Order.CompleteLattice.«term⨆_,_»
     "⨆"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
       (Lean.bracketedExplicitBinders
        "("
        [(Lean.binderIdent "_")]
        ":"
        (Init.Core.«term_∈_»
         `x
         " ∈ "
         (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
        ")")])
     ", "
     (Term.app `sp [`x]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Order.CompleteLattice.«term⨆_,_»
    "⨆"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
    ", "
    (Term.app `sp [`x]))
   "="
   (Order.CompleteLattice.«term⨆_,_»
    "⨆"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent "_")]
       ":"
       (Init.Core.«term_∈_»
        `x
        " ∈ "
        (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
       ")")])
    ", "
    (Term.app `sp [`x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent "_")]
      ":"
      (Init.Core.«term_∈_»
       `x
       " ∈ "
       (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
      ")")])
   ", "
   (Term.app `sp [`x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sp [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/-- Finitely generated submodules are precisely compact elements in the submodule lattice. -/
  theorem
    fg_iff_compact
    ( s : Submodule R M ) : s.fg ↔ CompleteLattice.IsCompactElement s
    :=
      by
        classical
          let sp : M → Submodule R M := fun a => span R { a }
          have
            supr_rw
            : ∀ t : Finset M , ⨆ ( x : _ ) ( _ : x ∈ t ) , sp x = ⨆ ( x : _ ) ( _ : x ∈ ( ↑ t : Set M ) ) , sp x
          exact fun t => by rfl
          constructor
          ·
            rintro ⟨ t , rfl ⟩
              rw [ span_eq_supr_of_singleton_spans , ← supr_rw , ← Finset.sup_eq_supr t sp ]
              apply CompleteLattice.finset_sup_compact_of_compact
              exact fun n _ => singleton_span_is_compact_element n
          ·
            intro h
              have
                sSup
                  : s = Sup sp '' ↑ s
                  :=
                  by rw [ Sup_eq_supr , supr_image , ← span_eq_supr_of_singleton_spans , eq_comm , span_eq ]
              obtain ⟨ u , ⟨ huspan , husup ⟩ ⟩ := h sp '' ↑ s le_of_eqₓ sSup
              have
                ssup
                  : s = u.sup id
                  :=
                  by
                    suffices : u.sup id ≤ s
                      exact le_antisymmₓ husup this
                      rw [ sSup , Finset.sup_id_eq_Sup ]
                      exact Sup_le_Sup huspan
              obtain ⟨ t , ⟨ hts , rfl ⟩ ⟩ := finset.subset_image_iff.mp huspan
              rw
                [
                  Finset.sup_finset_image
                    ,
                    Function.comp.left_id
                    ,
                    Finset.sup_eq_supr
                    ,
                    supr_rw
                    ,
                    ← span_eq_supr_of_singleton_spans
                    ,
                    eq_comm
                  ]
                at ssup
              exact ⟨ t , ssup ⟩

end Submodule

/-- 
`is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
class IsNoetherian (R M) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Prop where
  noetherian : ∀ s : Submodule R M, s.fg

section

variable {R : Type _} {M : Type _} {P : Type _}

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ P]

variable [Module R M] [Module R P]

open IsNoetherian

include R

/--  An R-module is Noetherian iff all its submodules are finitely-generated. -/
theorem is_noetherian_def : IsNoetherian R M ↔ ∀ s : Submodule R M, s.fg :=
  ⟨fun h => h.noetherian, IsNoetherian.mk⟩

theorem is_noetherian_submodule {N : Submodule R M} : IsNoetherian R N ↔ ∀ s : Submodule R M, s ≤ N → s.fg := by
  refine'
    ⟨fun ⟨hn⟩ => fun s hs =>
      have : s ≤ N.subtype.range := N.range_subtype.symm ▸ hs
      Submodule.map_comap_eq_self this ▸ (hn _).map _,
      fun h => ⟨fun s => _⟩⟩
  have f := (Submodule.equivMapOfInjective N.subtype Subtype.val_injective s).symm
  have h₁ := h (s.map N.subtype) (Submodule.map_subtype_le N s)
  have h₂ : (⊤ : Submodule R (s.map N.subtype)).map (↑f : _ →ₗ[R] s) = ⊤ := by
    simp
  have h₃ := ((Submodule.fg_top _).2 h₁).map (↑f : _ →ₗ[R] s)
  exact (Submodule.fg_top _).1 (h₂ ▸ h₃)

theorem is_noetherian_submodule_left {N : Submodule R M} : IsNoetherian R N ↔ ∀ s : Submodule R M, (N⊓s).Fg :=
  is_noetherian_submodule.trans ⟨fun H s => H _ inf_le_left, fun H s hs => inf_of_le_right hs ▸ H _⟩

theorem is_noetherian_submodule_right {N : Submodule R M} : IsNoetherian R N ↔ ∀ s : Submodule R M, (s⊓N).Fg :=
  is_noetherian_submodule.trans ⟨fun H s => H _ inf_le_right, fun H s hs => inf_of_le_left hs ▸ H _⟩

instance is_noetherian_submodule' [IsNoetherian R M] (N : Submodule R M) : IsNoetherian R N :=
  is_noetherian_submodule.2 $ fun _ _ => IsNoetherian.noetherian _

theorem is_noetherian_of_le {s t : Submodule R M} [ht : IsNoetherian R t] (h : s ≤ t) : IsNoetherian R s :=
  is_noetherian_submodule.mpr fun s' hs' => is_noetherian_submodule.mp ht _ (le_transₓ hs' h)

variable (M)

theorem is_noetherian_of_surjective (f : M →ₗ[R] P) (hf : f.range = ⊤) [IsNoetherian R M] : IsNoetherian R P :=
  ⟨fun s =>
    have : (s.comap f).map f = s := Submodule.map_comap_eq_self $ hf.symm ▸ le_top
    this ▸ (noetherian _).map _⟩

variable {M}

theorem is_noetherian_of_linear_equiv (f : M ≃ₗ[R] P) [IsNoetherian R M] : IsNoetherian R P :=
  is_noetherian_of_surjective _ f.to_linear_map f.range

theorem is_noetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M := by
  (
    constructor <;> intro h)
  ·
    exact is_noetherian_of_linear_equiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
  ·
    exact is_noetherian_of_linear_equiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl).symm

theorem is_noetherian_of_injective [IsNoetherian R P] (f : M →ₗ[R] P) (hf : Function.Injective f) : IsNoetherian R M :=
  is_noetherian_of_linear_equiv (LinearEquiv.ofInjective f hf).symm

theorem fg_of_injective [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P) (hf : Function.Injective f) : N.fg :=
  @IsNoetherian.noetherian _ _ _ (is_noetherian_of_injective f hf) N

end

section

variable {R : Type _} {M : Type _} {P : Type _}

variable [Ringₓ R] [AddCommGroupₓ M] [AddCommGroupₓ P]

variable [Module R M] [Module R P]

open IsNoetherian

include R

theorem is_noetherian_of_ker_bot [IsNoetherian R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) : IsNoetherian R M :=
  is_noetherian_of_linear_equiv (LinearEquiv.ofInjective f $ LinearMap.ker_eq_bot.mp hf).symm

theorem fg_of_ker_bot [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P) (hf : f.ker = ⊥) : N.fg :=
  @IsNoetherian.noetherian _ _ _ (is_noetherian_of_ker_bot f hf) N

instance is_noetherian_prod [IsNoetherian R M] [IsNoetherian R P] : IsNoetherian R (M × P) :=
  ⟨fun s =>
    Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M P) (noetherian _) $
      have : s⊓LinearMap.ker (LinearMap.snd R M P) ≤ LinearMap.range (LinearMap.inl R M P) := fun x ⟨hx1, hx2⟩ =>
        ⟨x.1, Prod.extₓ rfl $ Eq.symm $ LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩

instance is_noetherian_pi {R ι : Type _} {M : ι → Type _} [Ringₓ R] [∀ i, AddCommGroupₓ (M i)] [∀ i, Module R (M i)]
    [Fintype ι] [∀ i, IsNoetherian R (M i)] : IsNoetherian R (∀ i, M i) := by
  have := Classical.decEq ι
  suffices on_finset : ∀ s : Finset ι, IsNoetherian R (∀ i : s, M i)
  ·
    let coe_e := Equivₓ.subtypeUnivEquiv Finset.mem_univ
    let this' : IsNoetherian R (∀ i : Finset.univ, M (coe_e i)) := on_finset Finset.univ
    exact is_noetherian_of_linear_equiv (LinearEquiv.piCongrLeft R M coe_e)
  intro s
  induction' s using Finset.induction with a s has ih
  ·
    constructor
    intro s
    convert Submodule.fg_bot
    apply eq_bot_iff.2
    intro x hx
    refine' (Submodule.mem_bot R).2 _
    ext i
    cases i.2
  refine' @is_noetherian_of_linear_equiv _ _ _ _ _ _ _ _ _ (@is_noetherian_prod _ (M a) _ _ _ _ _ _ _ ih)
  fconstructor
  ·
    exact fun f i =>
      Or.byCases (Finset.mem_insert.1 i.2) (fun h : i.1 = a => show M i.1 from Eq.recOnₓ h.symm f.1) fun h : i.1 ∈ s =>
        show M i.1 from f.2 ⟨i.1, h⟩
  ·
    intro f g
    ext i
    unfold Or.byCases
    cases' i with i hi
    rcases Finset.mem_insert.1 hi with (rfl | h)
    ·
      change _ = _+_
      simp only [dif_pos]
      rfl
    ·
      change _ = _+_
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      rfl
  ·
    intro c f
    ext i
    unfold Or.byCases
    cases' i with i hi
    rcases Finset.mem_insert.1 hi with (rfl | h)
    ·
      change _ = c • _
      simp only [dif_pos]
      rfl
    ·
      change _ = c • _
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      rfl
  ·
    exact fun f => (f ⟨a, Finset.mem_insert_self _ _⟩, fun i => f ⟨i.1, Finset.mem_insert_of_mem i.2⟩)
  ·
    intro f
    apply Prod.extₓ
    ·
      simp only [Or.byCases, dif_pos]
    ·
      ext ⟨i, his⟩
      have : ¬i = a := by
        rintro rfl
        exact has his
      dsimp only [Or.byCases]
      change i ∈ s at his
      rw [dif_neg this, dif_pos his]
  ·
    intro f
    ext ⟨i, hi⟩
    rcases Finset.mem_insert.1 hi with (rfl | h)
    ·
      simp only [Or.byCases, dif_pos]
    ·
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [Or.byCases, dif_neg this, dif_pos h]

/--  A version of `is_noetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance is_noetherian_pi' {R ι M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [Fintype ι] [IsNoetherian R M] :
    IsNoetherian R (ι → M) :=
  is_noetherian_pi

end

open IsNoetherian Submodule Function

section

universe w

variable {R M P : Type _} {N : Type w} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [AddCommMonoidₓ N] [Module R N]
  [AddCommMonoidₓ P] [Module R P]

theorem is_noetherian_iff_well_founded :
    IsNoetherian R M ↔ WellFounded (· > · : Submodule R M → Submodule R M → Prop) := by
  rw [(CompleteLattice.well_founded_characterisations $ Submodule R M).out 0 3]
  exact ⟨fun ⟨h⟩ => fun k => (fg_iff_compact k).mp (h k), fun h => ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩

variable (R M)

theorem well_founded_submodule_gt R M [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] :
    ∀ [IsNoetherian R M], WellFounded (· > · : Submodule R M → Submodule R M → Prop) :=
  is_noetherian_iff_well_founded.mp

variable {R M}

/--  A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
theorem set_has_maximal_iff_noetherian :
    (∀ a : Set $ Submodule R M, a.nonempty → ∃ M' ∈ a, ∀, ∀ I ∈ a, ∀, M' ≤ I → I = M') ↔ IsNoetherian R M := by
  rw [is_noetherian_iff_well_founded, WellFounded.well_founded_iff_has_max']

/--  A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
    (∀ f : ℕ →ₘ Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
  rw [is_noetherian_iff_well_founded, WellFounded.monotone_chain_condition]

/--  If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop} (hgt : ∀ I, (∀, ∀ J > I, ∀, P J) → P I)
    (I : Submodule R M) : P I :=
  WellFounded.recursionₓ (well_founded_submodule_gt R M) I hgt

end

section

universe w

variable {R M P : Type _} {N : Type w} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ N] [Module R N]
  [AddCommGroupₓ P] [Module R P]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `finite_of_linear_independent [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `Nontrivial [`R]) "]")
    (Term.instBinder "[" [] (Term.app `IsNoetherian [`R `M]) "]")
    (Term.implicitBinder "{" [`s] [":" (Term.app `Set [`M])] "}")
    (Term.explicitBinder
     "("
     [`hs]
     [":"
      (Term.app
       `LinearIndependent
       [`R (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `s "→" `M))]] ")")])]
     []
     ")")]
   (Term.typeSpec ":" `s.finite))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.refine'
         "refine'"
         (Term.app
          `Classical.by_contradiction
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`hf] [])]
             "=>"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj `RelEmbedding.well_founded_iff_no_descending_seq "." (fieldIdx "1"))
                [(Term.app `well_founded_submodule_gt [`R `M])])
               "."
               `elim')
              [(Term.hole "_")])))]))
        [])
       (group
        (Tactic.have'' "have" [`f []] [(Term.typeSpec ":" (Function.Logic.Embedding.«term_↪_» (termℕ "ℕ") " ↪ " `s))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          (Term.explicit "@" `Infinite.natEmbedding)
          [`s
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" (Term.app `hf [(Term.anonymousCtor "⟨" [`f] "⟩")])))]
            "⟩")]))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [])]
              ","
              (Init.Core.«term_⊆_»
               (Set.Data.Set.Basic.term_''_
                («term_∘_» `coeₓ "∘" `f)
                " '' "
                (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `n) "}"))
               " ⊆ "
               `s)))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one (Tactic.rcasesPat.one `n))
                  (Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
                  (Tactic.rintroPat.one
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy₁)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy₂)]) [])]
                    "⟩"))]
                 [])
                [])
               (group (Tactic.subst "subst" [`hy₂]) [])
               (group (Tactic.exact "exact" (Term.proj (Term.app `f [`y]) "." (fieldIdx "2"))) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`a `b] [(Term.typeSpec ":" (termℕ "ℕ"))])]
              ","
              («term_↔_»
               («term_≤_» `a "≤" `b)
               "↔"
               («term_≤_»
                (Term.app
                 `span
                 [`R
                  (Set.Data.Set.Basic.term_''_
                   («term_∘_» `coeₓ "∘" `f)
                   " '' "
                   (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `a) "}"))])
                "≤"
                (Term.app
                 `span
                 [`R
                  (Set.Data.Set.Basic.term_''_
                   («term_∘_» `coeₓ "∘" `f)
                   " '' "
                   (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `b) "}"))])))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`a `b]) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `span_le_span_iff [`hs (Term.app `this [`a]) (Term.app `this [`b])]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app `Set.image_subset_image_iff [(Term.app `subtype.coe_injective.comp [`f.injective])]))
                   ","
                   (Tactic.rwRule [] `Set.subset_def)]
                  "]")
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
                     [(Term.simpleBinder [`hab `x] [])
                      (Term.simpleBinder [`hxa] [(Term.typeSpec ":" («term_≤_» `x "≤" `a))])]
                     "=>"
                     (Term.app `le_transₓ [`hxa `hab])))
                   ","
                   (Term.fun
                    "fun"
                    (Term.basicFun [(Term.simpleBinder [`hx] [])] "=>" (Term.app `hx [`a (Term.app `le_reflₓ [`a])])))]
                  "⟩"))
                [])]))))))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`n] [])]
               "=>"
               (Term.app
                `span
                [`R
                 (Set.Data.Set.Basic.term_''_
                  («term_∘_» `coeₓ "∘" `f)
                  " '' "
                  (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `n) "}"))])))
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x `y] [])]
               "=>"
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
                     ["["
                      [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
                       ","
                       (Tactic.simpLemma
                        []
                        []
                        (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
                      "]"]
                     [])
                    [])])))))]
            "⟩")
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.«tactic_<;>_»
                 (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Gt)] "]"] [] [])
                 "<;>"
                 (Tactic.«tactic_<;>_»
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `lt_iff_le_not_leₓ)
                     ","
                     (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
                    "]"]
                   [])
                  "<;>"
                  (Tactic.tauto "tauto" [])))
                [])])))]
          "⟩"))
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `Classical.by_contradiction
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`hf] [])]
            "=>"
            (Term.app
             (Term.proj
              (Term.app
               (Term.proj `RelEmbedding.well_founded_iff_no_descending_seq "." (fieldIdx "1"))
               [(Term.app `well_founded_submodule_gt [`R `M])])
              "."
              `elim')
             [(Term.hole "_")])))]))
       [])
      (group
       (Tactic.have'' "have" [`f []] [(Term.typeSpec ":" (Function.Logic.Embedding.«term_↪_» (termℕ "ℕ") " ↪ " `s))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.explicit "@" `Infinite.natEmbedding)
         [`s
          (Term.anonymousCtor
           "⟨"
           [(Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" (Term.app `hf [(Term.anonymousCtor "⟨" [`f] "⟩")])))]
           "⟩")]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])]
             ","
             (Init.Core.«term_⊆_»
              (Set.Data.Set.Basic.term_''_
               («term_∘_» `coeₓ "∘" `f)
               " '' "
               (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `n) "}"))
              " ⊆ "
              `s)))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `n))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
                 (Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy₁)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy₂)]) [])]
                   "⟩"))]
                [])
               [])
              (group (Tactic.subst "subst" [`hy₂]) [])
              (group (Tactic.exact "exact" (Term.proj (Term.app `f [`y]) "." (fieldIdx "2"))) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`a `b] [(Term.typeSpec ":" (termℕ "ℕ"))])]
             ","
             («term_↔_»
              («term_≤_» `a "≤" `b)
              "↔"
              («term_≤_»
               (Term.app
                `span
                [`R
                 (Set.Data.Set.Basic.term_''_
                  («term_∘_» `coeₓ "∘" `f)
                  " '' "
                  (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `a) "}"))])
               "≤"
               (Term.app
                `span
                [`R
                 (Set.Data.Set.Basic.term_''_
                  («term_∘_» `coeₓ "∘" `f)
                  " '' "
                  (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `b) "}"))])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`a `b]) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `span_le_span_iff [`hs (Term.app `this [`a]) (Term.app `this [`b])]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Set.image_subset_image_iff [(Term.app `subtype.coe_injective.comp [`f.injective])]))
                  ","
                  (Tactic.rwRule [] `Set.subset_def)]
                 "]")
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
                    [(Term.simpleBinder [`hab `x] [])
                     (Term.simpleBinder [`hxa] [(Term.typeSpec ":" («term_≤_» `x "≤" `a))])]
                    "=>"
                    (Term.app `le_transₓ [`hxa `hab])))
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun [(Term.simpleBinder [`hx] [])] "=>" (Term.app `hx [`a (Term.app `le_reflₓ [`a])])))]
                 "⟩"))
               [])]))))))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`n] [])]
              "=>"
              (Term.app
               `span
               [`R
                (Set.Data.Set.Basic.term_''_
                 («term_∘_» `coeₓ "∘" `f)
                 " '' "
                 (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `n) "}"))])))
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x `y] [])]
              "=>"
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
                    ["["
                     [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
                      ","
                      (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
                     "]"]
                    [])
                   [])])))))]
           "⟩")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.«tactic_<;>_»
                (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Gt)] "]"] [] [])
                "<;>"
                (Tactic.«tactic_<;>_»
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `lt_iff_le_not_leₓ)
                    ","
                    (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
                   "]"]
                  [])
                 "<;>"
                 (Tactic.tauto "tauto" [])))
               [])])))]
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
    [(Term.anonymousCtor
      "⟨"
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`n] [])]
         "=>"
         (Term.app
          `span
          [`R
           (Set.Data.Set.Basic.term_''_
            («term_∘_» `coeₓ "∘" `f)
            " '' "
            (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `n) "}"))])))
       ","
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x `y] [])]
         "=>"
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
               ["["
                [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
                 ","
                 (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
                "]"]
               [])
              [])])))))]
      "⟩")
     ","
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.«tactic_<;>_»
           (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Gt)] "]"] [] [])
           "<;>"
           (Tactic.«tactic_<;>_»
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `lt_iff_le_not_leₓ)
               ","
               (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
              "]"]
             [])
            "<;>"
            (Tactic.tauto "tauto" [])))
          [])])))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.anonymousCtor
     "⟨"
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`n] [])]
        "=>"
        (Term.app
         `span
         [`R
          (Set.Data.Set.Basic.term_''_
           («term_∘_» `coeₓ "∘" `f)
           " '' "
           (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `n) "}"))])))
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x `y] [])]
        "=>"
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
              ["["
               [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
                ","
                (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
               "]"]
              [])
             [])])))))]
     "⟩")
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.«tactic_<;>_»
          (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Gt)] "]"] [] [])
          "<;>"
          (Tactic.«tactic_<;>_»
           (Tactic.simp
            "simp"
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `lt_iff_le_not_leₓ)
              ","
              (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
             "]"]
            [])
           "<;>"
           (Tactic.tauto "tauto" [])))
         [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Gt)] "]"] [] [])
        "<;>"
        (Tactic.«tactic_<;>_»
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] `lt_iff_le_not_leₓ)
            ","
            (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
           "]"]
          [])
         "<;>"
         (Tactic.tauto "tauto" [])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Gt)] "]"] [] [])
   "<;>"
   (Tactic.«tactic_<;>_»
    (Tactic.simp
     "simp"
     []
     ["only"]
     ["["
      [(Tactic.simpLemma [] [] `lt_iff_le_not_leₓ)
       ","
       (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
      "]"]
     [])
    "<;>"
    (Tactic.tauto "tauto" [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.simp
    "simp"
    []
    ["only"]
    ["["
     [(Tactic.simpLemma [] [] `lt_iff_le_not_leₓ)
      ","
      (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
     "]"]
    [])
   "<;>"
   (Tactic.tauto "tauto" []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tauto "tauto" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tauto', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `lt_iff_le_not_leₓ)
     ","
     (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `this [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `this [(Term.hole "_") (Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `lt_iff_le_not_leₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `Gt)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Gt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`n] [])]
      "=>"
      (Term.app
       `span
       [`R
        (Set.Data.Set.Basic.term_''_
         («term_∘_» `coeₓ "∘" `f)
         " '' "
         (Set.«term{_|_}» "{" `m "|" («term_≤_» `m "≤" `n) "}"))])))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x `y] [])]
      "=>"
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
            ["["
             [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
              ","
              (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
             "]"]
            [])
           [])])))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x `y] [])]
    "=>"
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
          ["["
           [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
            ","
            (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
           "]"]
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
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
        ["["
         [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
          ","
          (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
         "]"]
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
   ["["
    [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
     ","
     (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `this [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `this [(Term.hole "_") (Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `le_antisymm_iffₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
  finite_of_linear_independent
  [ Nontrivial R ] [ IsNoetherian R M ] { s : Set M } ( hs : LinearIndependent R ( coeₓ : s → M ) ) : s.finite
  :=
    by
      refine'
          Classical.by_contradiction
            fun hf => RelEmbedding.well_founded_iff_no_descending_seq . 1 well_founded_submodule_gt R M . elim' _
        have f : ℕ ↪ s
        exact @ Infinite.natEmbedding s ⟨ fun f => hf ⟨ f ⟩ ⟩
        have : ∀ n , coeₓ ∘ f '' { m | m ≤ n } ⊆ s := by rintro n x ⟨ y , hy₁ , hy₂ ⟩ subst hy₂ exact f y . 2
        have
          : ∀ a b : ℕ , a ≤ b ↔ span R coeₓ ∘ f '' { m | m ≤ a } ≤ span R coeₓ ∘ f '' { m | m ≤ b }
            :=
            by
              intro a b
                rw
                  [
                    span_le_span_iff hs this a this b
                      ,
                      Set.image_subset_image_iff subtype.coe_injective.comp f.injective
                      ,
                      Set.subset_def
                    ]
                exact ⟨ fun hab x hxa : x ≤ a => le_transₓ hxa hab , fun hx => hx a le_reflₓ a ⟩
        exact
          ⟨
            ⟨
                fun n => span R coeₓ ∘ f '' { m | m ≤ n }
                  ,
                  fun
                    x y
                      =>
                      by
                        simp
                          ( config := { contextual := Bool.true._@._internal._hyg.0 } )
                          [ le_antisymm_iffₓ , this _ _ . symm ]
                ⟩
              ,
              by dsimp [ Gt ] <;> simp only [ lt_iff_le_not_leₓ , this _ _ . symm ] <;> tauto
            ⟩

/--  If the first and final modules in a short exact sequence are noetherian,
  then the middle module is also noetherian. -/
theorem is_noetherian_of_range_eq_ker [IsNoetherian R M] [IsNoetherian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : f.range = g.ker) : IsNoetherian R N :=
  is_noetherian_iff_well_founded.2 $
    well_founded_gt_exact_sequence (well_founded_submodule_gt R M) (well_founded_submodule_gt R P) f.range
      (Submodule.map f) (Submodule.comap f) (Submodule.comap g) (Submodule.map g) (Submodule.gciMapComap hf)
      (Submodule.giMapComap hg)
      (by
        simp [Submodule.map_comap_eq, inf_comm])
      (by
        simp [Submodule.comap_map_eq, h])

/-- 
For any endomorphism of a Noetherian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot [I : IsNoetherian R M] (f : M →ₗ[R] M) :
    ∃ n : ℕ, n ≠ 0 ∧ (f^n).ker⊓(f^n).range = ⊥ := by
  obtain ⟨n, w⟩ :=
    monotone_stabilizes_iff_noetherian.mpr I
      (f.iterate_ker.comp
        ⟨fun n => n+1, fun n m w => by
          linarith⟩)
  specialize
    w ((2*n)+1)
      (by
        linarith)
  dsimp  at w
  refine' ⟨n+1, Nat.succ_ne_zero _, _⟩
  rw [eq_bot_iff]
  rintro - ⟨h, ⟨y, rfl⟩⟩
  rw [mem_bot, ← LinearMap.mem_ker, w]
  erw [LinearMap.mem_ker] at h⊢
  change ((f^n+1)*f^n+1) y = 0 at h
  rw [← pow_addₓ] at h
  convert h using 3
  linarith

/--  Any surjective endomorphism of a Noetherian module is injective. -/
theorem IsNoetherian.injective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M) (s : surjective f) :
    injective f := by
  obtain ⟨n, ne, w⟩ := IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot f
  rw [linear_map.range_eq_top.mpr (LinearMap.iterate_surjective s n), inf_top_eq, LinearMap.ker_eq_bot] at w
  exact LinearMap.injective_of_iterate_injective Ne w

/--  Any surjective endomorphism of a Noetherian module is bijective. -/
theorem IsNoetherian.bijective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M) (s : surjective f) :
    bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩

/-- 
A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
theorem IsNoetherian.disjoint_partial_sups_eventually_bot [I : IsNoetherian R M] (f : ℕ → Submodule R M)
    (h : ∀ n, Disjoint (partialSups f n) (f (n+1))) : ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ := by
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m+1) = ⊥
  ·
    obtain ⟨n, w⟩ := t
    use n+1
    rintro (_ | m) p
    ·
      cases p
    ·
      apply w
      exact nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partialSups f)
  exact ⟨n, fun m p => eq_bot_of_disjoint_absorbs (h m) ((Eq.symm (w (m+1) (le_add_right p))).trans (w m p))⟩

/-- 
If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
noncomputable def IsNoetherian.equivPunitOfProdInjective [IsNoetherian R M] (f : M × N →ₗ[R] M) (i : injective f) :
    N ≃ₗ[R] PUnit.{w + 1} := by
  apply Nonempty.some
  obtain ⟨n, w⟩ := IsNoetherian.disjoint_partial_sups_eventually_bot (f.tailing i) (f.tailings_disjoint_tailing i)
  specialize w n (le_reflₓ n)
  apply Nonempty.intro
  refine' (f.tailing_linear_equiv i n).symm ≪≫ₗ _
  rw [w]
  exact Submodule.botEquivPunit

end

/-- 
A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
class IsNoetherianRing (R) [Semiringₓ R] extends IsNoetherian R R : Prop

theorem is_noetherian_ring_iff {R} [Semiringₓ R] : IsNoetherianRing R ↔ IsNoetherian R R :=
  ⟨fun h => h.1, @IsNoetherianRing.mk _ _⟩

/--  A commutative ring is Noetherian if and only if all its ideals are finitely-generated. -/
theorem is_noetherian_ring_iff_ideal_fg (R : Type _) [CommSemiringₓ R] : IsNoetherianRing R ↔ ∀ I : Ideal R, I.fg :=
  is_noetherian_ring_iff.trans is_noetherian_def

instance (priority := 80) Ringₓ.is_noetherian_of_fintype R M [Fintype M] [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] :
    IsNoetherian R M := by
  let this' := Classical.dec <;>
    exact
      ⟨fun s =>
        ⟨to_finset s, by
          rw [Set.coe_to_finset, Submodule.span_eq]⟩⟩

theorem Ringₓ.is_noetherian_of_zero_eq_one {R} [Semiringₓ R] (h01 : (0 : R) = 1) : IsNoetherianRing R := by
  have := subsingleton_of_zero_eq_one h01 <;>
    have := Fintype.ofSubsingleton (0 : R) <;> exact is_noetherian_ring_iff.2 (Ringₓ.is_noetherian_of_fintype R R)

theorem is_noetherian_of_submodule_of_noetherian R M [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (N : Submodule R M)
    (h : IsNoetherian R M) : IsNoetherian R N := by
  rw [is_noetherian_iff_well_founded] at h⊢
  exact OrderEmbedding.well_founded (Submodule.MapSubtype.orderEmbedding N).dual h

instance Submodule.Quotient.is_noetherian {R} [Ringₓ R] {M} [AddCommGroupₓ M] [Module R M] (N : Submodule R M)
    [h : IsNoetherian R M] : IsNoetherian R (M ⧸ N) := by
  rw [is_noetherian_iff_well_founded] at h⊢
  exact OrderEmbedding.well_founded (Submodule.ComapMkq.orderEmbedding N).dual h

/--  If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem is_noetherian_of_tower R {S M} [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ M] [HasScalar R S] [Module S M]
    [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M := by
  rw [is_noetherian_iff_well_founded] at h⊢
  refine' (Submodule.restrictScalarsEmbedding R S M).dual.WellFounded h

instance Ideal.Quotient.is_noetherian_ring {R : Type _} [CommRingₓ R] [h : IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (R ⧸ I) :=
  is_noetherian_ring_iff.mpr $ is_noetherian_of_tower R $ Submodule.Quotient.is_noetherian _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `is_noetherian_of_fg_of_noetherian [])
  (Command.declSig
   [(Term.implicitBinder "{" [`R `M] [] "}")
    (Term.instBinder "[" [] (Term.app `Ringₓ [`R]) "]")
    (Term.instBinder "[" [] (Term.app `AddCommGroupₓ [`M]) "]")
    (Term.instBinder "[" [] (Term.app `Module [`R `M]) "]")
    (Term.explicitBinder "(" [`N] [":" (Term.app `Submodule [`R `M])] [] ")")
    (Term.instBinder "[" [] (Term.app `IsNoetherianRing [`R]) "]")
    (Term.explicitBinder "(" [`hN] [":" `N.fg] [] ")")]
   (Term.typeSpec ":" (Term.app `IsNoetherian [`R `N])))
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`s "," `hs] "⟩") [] [] ":=" `hN))
    []
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`M]))))
         [])
        (group
         (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`R]))))
         [])
        (group
         (Tactic.tacticLet_
          "let"
          (Term.letDecl
           (Term.letIdDecl
            `this'
            []
            [(Term.typeSpec ":" (Term.app `IsNoetherian [`R `R]))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
         [])
        (group
         (Tactic.have''
          "have"
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `x
              («binderTerm∈_» "∈" `s)
              ","
              (Term.forall "∀" [] "," (Init.Core.«term_∈_» `x " ∈ " `N)))))])
         [])
        (group
         (Tactic.exact
          "exact"
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `hx] [])]
            "=>"
            (Term.subst `hs "▸" [(Term.app `Submodule.subset_span [`hx])]))))
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           (Term.explicit "@" `is_noetherian_of_surjective)
           [(Term.arrow
             (Term.paren "(" [(Init.Coe.«term↑_» "↑" `s) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
             "→"
             `R)
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.app `Pi.module [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            `is_noetherian_pi]))
         [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.fapply "fapply" `LinearMap.mk) [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.exact
                    "exact"
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`f] [])]
                      "=>"
                      (Term.anonymousCtor
                       "⟨"
                       [(Algebra.BigOperators.Basic.«term∑_in_,_»
                         "∑"
                         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                         " in "
                         `s.attach
                         ", "
                         (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.proj `i "." (fieldIdx "1"))))
                        ","
                        (Term.app
                         `N.sum_mem
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`c (Term.hole "_")] [])]
                            "=>"
                            («term_$__»
                             (Term.app `N.smul_mem [(Term.hole "_")])
                             "$"
                             (Term.app `this [(Term.hole "_") (Term.proj `c "." (fieldIdx "2"))]))))])]
                       "⟩"))))
                   [])])))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intro "intro" [`f `g]) [])
                  (group (Tactic.apply "apply" `Subtype.eq) [])
                  (group
                   (Tactic.change
                    "change"
                    («term_=_»
                     (Algebra.BigOperators.Basic.«term∑_in_,_»
                      "∑"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      `s.attach
                      ", "
                      (Algebra.Group.Defs.«term_•_»
                       (Init.Logic.«term_+_» (Term.app `f [`i]) "+" (Term.app `g [`i]))
                       " • "
                       (Term.hole "_")))
                     "="
                     (Term.hole "_"))
                    [])
                   [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `add_smul) "," (Tactic.simpLemma [] [] `Finset.sum_add_distrib)] "]"]
                    [])
                   [])
                  (group (Tactic.tacticRfl "rfl") [])])))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intro "intro" [`c `f]) [])
                  (group (Tactic.apply "apply" `Subtype.eq) [])
                  (group
                   (Tactic.change
                    "change"
                    («term_=_»
                     (Algebra.BigOperators.Basic.«term∑_in_,_»
                      "∑"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      `s.attach
                      ", "
                      (Algebra.Group.Defs.«term_•_»
                       (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                       " • "
                       (Term.hole "_")))
                     "="
                     (Term.hole "_"))
                    [])
                   [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `smul_eq_mul) "," (Tactic.simpLemma [] [] `mul_smul)] "]"]
                    [])
                   [])
                  (group (Tactic.exact "exact" `finset.smul_sum.symm) [])])))
              [])])))
         [])
        (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMap.range_eq_top)] "]") []) [])
        (group
         (Tactic.rintro
          "rintro"
          [(Tactic.rintroPat.one
            (Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
             "⟩"))]
          [])
         [])
        (group
         (Tactic.change
          "change"
          (Init.Core.«term_∈_» `n " ∈ " `N)
          [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule ["←"] `hs)
            ","
            (Tactic.rwRule ["←"] (Term.app `Set.image_id [(Init.Coe.«term↑_» "↑" `s)]))
            ","
            (Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)]
           "]")
          [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
         [])
        (group
         (Tactic.rcases
          "rcases"
          [(Tactic.casesTarget [] `hn)]
          ["with"
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl1)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl2)]) [])]
            "⟩")])
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.anonymousCtor
           "⟨"
           [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `l [`x])))
            ","
            (Term.app `Subtype.ext [(Term.hole "_")])]
           "⟩"))
         [])
        (group
         (Tactic.change
          "change"
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            " in "
            `s.attach
            ", "
            (Algebra.Group.Defs.«term_•_»
             (Term.app `l [`i])
             " • "
             (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
           "="
           `n)
          [])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule
             []
             (Term.app
              (Term.explicit "@" `Finset.sum_attach)
              [`M
               `M
               `s
               (Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [])]
                 "=>"
                 (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))]))
            ","
            (Tactic.rwRule ["←"] `hl2)
            ","
            (Tactic.rwRule [] `Finsupp.total_apply)
            ","
            (Tactic.rwRule [] `Finsupp.sum)
            ","
            (Tactic.rwRule [] `eq_comm)]
           "]")
          [])
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           `Finset.sum_subset
           [`hl1
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))]))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx]))
            ","
            (Tactic.rwRule [] `zero_smul)]
           "]")
          [])
         [])]))))
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
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`s "," `hs] "⟩") [] [] ":=" `hN))
   []
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`M]))))
        [])
       (group
        (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`R]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `IsNoetherian [`R `R]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
        [])
       (group
        (Tactic.have''
         "have"
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            []
            ","
            (Mathlib.ExtendedBinder.«term∀___,_»
             "∀"
             `x
             («binderTerm∈_» "∈" `s)
             ","
             (Term.forall "∀" [] "," (Init.Core.«term_∈_» `x " ∈ " `N)))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x `hx] [])]
           "=>"
           (Term.subst `hs "▸" [(Term.app `Submodule.subset_span [`hx])]))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.explicit "@" `is_noetherian_of_surjective)
          [(Term.arrow
            (Term.paren "(" [(Init.Coe.«term↑_» "↑" `s) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
            "→"
            `R)
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.app `Pi.module [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           `is_noetherian_pi]))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.fapply "fapply" `LinearMap.mk) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`f] [])]
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [(Algebra.BigOperators.Basic.«term∑_in_,_»
                        "∑"
                        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                        " in "
                        `s.attach
                        ", "
                        (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.proj `i "." (fieldIdx "1"))))
                       ","
                       (Term.app
                        `N.sum_mem
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder [`c (Term.hole "_")] [])]
                           "=>"
                           («term_$__»
                            (Term.app `N.smul_mem [(Term.hole "_")])
                            "$"
                            (Term.app `this [(Term.hole "_") (Term.proj `c "." (fieldIdx "2"))]))))])]
                      "⟩"))))
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`f `g]) [])
                 (group (Tactic.apply "apply" `Subtype.eq) [])
                 (group
                  (Tactic.change
                   "change"
                   («term_=_»
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                     " in "
                     `s.attach
                     ", "
                     (Algebra.Group.Defs.«term_•_»
                      (Init.Logic.«term_+_» (Term.app `f [`i]) "+" (Term.app `g [`i]))
                      " • "
                      (Term.hole "_")))
                    "="
                    (Term.hole "_"))
                   [])
                  [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `add_smul) "," (Tactic.simpLemma [] [] `Finset.sum_add_distrib)] "]"]
                   [])
                  [])
                 (group (Tactic.tacticRfl "rfl") [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`c `f]) [])
                 (group (Tactic.apply "apply" `Subtype.eq) [])
                 (group
                  (Tactic.change
                   "change"
                   («term_=_»
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                     " in "
                     `s.attach
                     ", "
                     (Algebra.Group.Defs.«term_•_»
                      (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                      " • "
                      (Term.hole "_")))
                    "="
                    (Term.hole "_"))
                   [])
                  [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `smul_eq_mul) "," (Tactic.simpLemma [] [] `mul_smul)] "]"]
                   [])
                  [])
                 (group (Tactic.exact "exact" `finset.smul_sum.symm) [])])))
             [])])))
        [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMap.range_eq_top)] "]") []) [])
       (group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
            "⟩"))]
         [])
        [])
       (group
        (Tactic.change
         "change"
         (Init.Core.«term_∈_» `n " ∈ " `N)
         [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] `hs)
           ","
           (Tactic.rwRule ["←"] (Term.app `Set.image_id [(Init.Coe.«term↑_» "↑" `s)]))
           ","
           (Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `hn)]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl1)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl2)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `l [`x])))
           ","
           (Term.app `Subtype.ext [(Term.hole "_")])]
          "⟩"))
        [])
       (group
        (Tactic.change
         "change"
         («term_=_»
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
           " in "
           `s.attach
           ", "
           (Algebra.Group.Defs.«term_•_»
            (Term.app `l [`i])
            " • "
            (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
          "="
          `n)
         [])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             (Term.explicit "@" `Finset.sum_attach)
             [`M
              `M
              `s
              (Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`i] [])]
                "=>"
                (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))]))
           ","
           (Tactic.rwRule ["←"] `hl2)
           ","
           (Tactic.rwRule [] `Finsupp.total_apply)
           ","
           (Tactic.rwRule [] `Finsupp.sum)
           ","
           (Tactic.rwRule [] `eq_comm)]
          "]")
         [])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `Finset.sum_subset
          [`hl1
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx]))
           ","
           (Tactic.rwRule [] `zero_smul)]
          "]")
         [])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`M]))))
       [])
      (group
       (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`R]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this'
          []
          [(Term.typeSpec ":" (Term.app `IsNoetherian [`R `R]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
       [])
      (group
       (Tactic.have''
        "have"
        []
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           []
           ","
           (Mathlib.ExtendedBinder.«term∀___,_»
            "∀"
            `x
            («binderTerm∈_» "∈" `s)
            ","
            (Term.forall "∀" [] "," (Init.Core.«term_∈_» `x " ∈ " `N)))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x `hx] [])]
          "=>"
          (Term.subst `hs "▸" [(Term.app `Submodule.subset_span [`hx])]))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.explicit "@" `is_noetherian_of_surjective)
         [(Term.arrow
           (Term.paren "(" [(Init.Coe.«term↑_» "↑" `s) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
           "→"
           `R)
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.app `Pi.module [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          `is_noetherian_pi]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.fapply "fapply" `LinearMap.mk) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`f] [])]
                    "=>"
                    (Term.anonymousCtor
                     "⟨"
                     [(Algebra.BigOperators.Basic.«term∑_in_,_»
                       "∑"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                       " in "
                       `s.attach
                       ", "
                       (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.proj `i "." (fieldIdx "1"))))
                      ","
                      (Term.app
                       `N.sum_mem
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`c (Term.hole "_")] [])]
                          "=>"
                          («term_$__»
                           (Term.app `N.smul_mem [(Term.hole "_")])
                           "$"
                           (Term.app `this [(Term.hole "_") (Term.proj `c "." (fieldIdx "2"))]))))])]
                     "⟩"))))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`f `g]) [])
                (group (Tactic.apply "apply" `Subtype.eq) [])
                (group
                 (Tactic.change
                  "change"
                  («term_=_»
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                    " in "
                    `s.attach
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (Init.Logic.«term_+_» (Term.app `f [`i]) "+" (Term.app `g [`i]))
                     " • "
                     (Term.hole "_")))
                   "="
                   (Term.hole "_"))
                  [])
                 [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `add_smul) "," (Tactic.simpLemma [] [] `Finset.sum_add_distrib)] "]"]
                  [])
                 [])
                (group (Tactic.tacticRfl "rfl") [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`c `f]) [])
                (group (Tactic.apply "apply" `Subtype.eq) [])
                (group
                 (Tactic.change
                  "change"
                  («term_=_»
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                    " in "
                    `s.attach
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                     " • "
                     (Term.hole "_")))
                   "="
                   (Term.hole "_"))
                  [])
                 [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `smul_eq_mul) "," (Tactic.simpLemma [] [] `mul_smul)] "]"]
                  [])
                 [])
                (group (Tactic.exact "exact" `finset.smul_sum.symm) [])])))
            [])])))
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMap.range_eq_top)] "]") []) [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
           "⟩"))]
        [])
       [])
      (group
       (Tactic.change "change" (Init.Core.«term_∈_» `n " ∈ " `N) [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `hs)
          ","
          (Tactic.rwRule ["←"] (Term.app `Set.image_id [(Init.Coe.«term↑_» "↑" `s)]))
          ","
          (Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)]
         "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `hn)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl1)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl2)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `l [`x])))
          ","
          (Term.app `Subtype.ext [(Term.hole "_")])]
         "⟩"))
       [])
      (group
       (Tactic.change
        "change"
        («term_=_»
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
          " in "
          `s.attach
          ", "
          (Algebra.Group.Defs.«term_•_»
           (Term.app `l [`i])
           " • "
           (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
         "="
         `n)
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app
            (Term.explicit "@" `Finset.sum_attach)
            [`M
             `M
             `s
             (Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`i] [])]
               "=>"
               (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))]))
          ","
          (Tactic.rwRule ["←"] `hl2)
          ","
          (Tactic.rwRule [] `Finsupp.total_apply)
          ","
          (Tactic.rwRule [] `Finsupp.sum)
          ","
          (Tactic.rwRule [] `eq_comm)]
         "]")
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `Finset.sum_subset
         [`hl1
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx]))
          ","
          (Tactic.rwRule [] `zero_smul)]
         "]")
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
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx]))
     ","
     (Tactic.rwRule [] `zero_smul)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Finsupp.not_mem_support_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `Finset.sum_subset
    [`hl1 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.sum_subset
   [`hl1 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `hl1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       (Term.explicit "@" `Finset.sum_attach)
       [`M
        `M
        `s
        (Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))]))
     ","
     (Tactic.rwRule ["←"] `hl2)
     ","
     (Tactic.rwRule [] `Finsupp.total_apply)
     ","
     (Tactic.rwRule [] `Finsupp.sum)
     ","
     (Tactic.rwRule [] `eq_comm)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_comm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finsupp.sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finsupp.total_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hl2
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `Finset.sum_attach)
   [`M
    `M
    `s
    (Term.hole "_")
    (Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `l [`i])
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
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `Finset.sum_attach)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_attach
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.change
   "change"
   («term_=_»
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s.attach
     ", "
     (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
    "="
    `n)
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.change', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s.attach
    ", "
    (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
   "="
   `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s.attach
   ", "
   (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `l [`i])
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
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s.attach
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  is_noetherian_of_fg_of_noetherian
  { R M } [ Ringₓ R ] [ AddCommGroupₓ M ] [ Module R M ] ( N : Submodule R M ) [ IsNoetherianRing R ] ( hN : N.fg )
    : IsNoetherian R N
  :=
    let
      ⟨ s , hs ⟩ := hN
      by
        have := Classical.decEq M
          have := Classical.decEq R
          let this' : IsNoetherian R R := by infer_instance
          have : ∀ , ∀ x ∈ s , ∀ , x ∈ N
          exact fun x hx => hs ▸ Submodule.subset_span hx
          refine' @ is_noetherian_of_surjective ( ↑ s : Set M ) → R _ _ _ Pi.module _ _ _ _ _ _ is_noetherian_pi
          ·
            fapply LinearMap.mk
              · exact fun f => ⟨ ∑ i in s.attach , f i • i . 1 , N.sum_mem fun c _ => N.smul_mem _ $ this _ c . 2 ⟩
              ·
                intro f g
                  apply Subtype.eq
                  change ∑ i in s.attach , f i + g i • _ = _
                  simp only [ add_smul , Finset.sum_add_distrib ]
                  rfl
              ·
                intro c f
                  apply Subtype.eq
                  change ∑ i in s.attach , c • f i • _ = _
                  simp only [ smul_eq_mul , mul_smul ]
                  exact finset.smul_sum.symm
          rw [ LinearMap.range_eq_top ]
          rintro ⟨ n , hn ⟩
          change n ∈ N at hn
          rw [ ← hs , ← Set.image_id ↑ s , Finsupp.mem_span_image_iff_total ] at hn
          rcases hn with ⟨ l , hl1 , hl2 ⟩
          refine' ⟨ fun x => l x , Subtype.ext _ ⟩
          change ∑ i in s.attach , l i • ( i : M ) = n
          rw [ @ Finset.sum_attach M M s _ fun i => l i • i , ← hl2 , Finsupp.total_apply , Finsupp.sum , eq_comm ]
          refine' Finset.sum_subset hl1 fun x _ hx => _
          rw [ Finsupp.not_mem_support_iff . 1 hx , zero_smul ]

theorem is_noetherian_of_fg_of_noetherian' {R M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [IsNoetherianRing R]
    (h : (⊤ : Submodule R M).Fg) : IsNoetherian R M :=
  have : IsNoetherian R (⊤ : Submodule R M) := is_noetherian_of_fg_of_noetherian _ h
  by
  exact is_noetherian_of_linear_equiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)

/--  In a module over a noetherian ring, the submodule generated by finitely many vectors is
noetherian. -/
theorem is_noetherian_span_of_finite R {M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [IsNoetherianRing R] {A : Set M}
    (hA : finite A) : IsNoetherian R (Submodule.span R A) :=
  is_noetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem is_noetherian_ring_of_surjective R [CommRingₓ R] S [CommRingₓ S] (f : R →+* S) (hf : Function.Surjective f)
    [H : IsNoetherianRing R] : IsNoetherianRing S := by
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at H⊢
  exact OrderEmbedding.well_founded (Ideal.orderEmbeddingOfSurjective f hf).dual H

instance is_noetherian_ring_range {R} [CommRingₓ R] {S} [CommRingₓ S] (f : R →+* S) [IsNoetherianRing R] :
    IsNoetherianRing f.range :=
  is_noetherian_ring_of_surjective R f.range f.range_restrict f.range_restrict_surjective

theorem is_noetherian_ring_of_ring_equiv R [CommRingₓ R] {S} [CommRingₓ S] (f : R ≃+* S) [IsNoetherianRing R] :
    IsNoetherianRing S :=
  is_noetherian_ring_of_surjective R S f.to_ring_hom f.to_equiv.surjective

namespace Submodule

variable {R : Type _} {A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable (M N : Submodule R A)

theorem fg_mul (hm : M.fg) (hn : N.fg) : (M*N).Fg :=
  let ⟨m, hfm, hm⟩ := fg_def.1 hm
  let ⟨n, hfn, hn⟩ := fg_def.1 hn
  fg_def.2 ⟨m*n, hfm.mul hfn, span_mul_span R m n ▸ hm ▸ hn ▸ rfl⟩

theorem fg_pow (h : M.fg) (n : ℕ) : (M^n).Fg :=
  Nat.recOn n
    ⟨{1}, by
      simp [one_eq_span]⟩
    fun n ih => by
    simpa [pow_succₓ] using fg_mul _ _ h ih

end Submodule

