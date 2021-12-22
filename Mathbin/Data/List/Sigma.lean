import Mathbin.Data.List.Range
import Mathbin.Data.List.Perm

/-!
# Utilities for lists of sigmas

This file includes several ways of interacting with `list (sigma β)`, treated as a key-value store.

If `α : Type*` and `β : α → Type*`, then we regard `s : sigma β` as having key `s.1 : α` and value
`s.2 : β s.1`. Hence, `list (sigma β)` behaves like a key-value store.

## Main Definitions

- `list.keys` extracts the list of keys.
- `list.nodupkeys` determines if the store has duplicate keys.
- `list.lookup`/`lookup_all` accesses the value(s) of a particular key.
- `list.kreplace` replaces the first value with a given key by a given value.
- `list.kerase` removes a value.
- `list.kinsert` inserts a value.
- `list.kunion` computes the union of two stores.
- `list.kextract` returns a value with a given key and the rest of the values.
-/


universe u v

namespace List

variable {α : Type u} {β : α → Type v}

/-! ### `keys` -/


/--  List of keys from a list of key-value pairs -/
def keys : List (Sigma β) → List α :=
  map Sigma.fst

@[simp]
theorem keys_nil : @keys α β [] = [] :=
  rfl

@[simp]
theorem keys_cons {s} {l : List (Sigma β)} : (s :: l).keys = s.1 :: l.keys :=
  rfl

theorem mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)} : s ∈ l → s.1 ∈ l.keys :=
  mem_map_of_mem Sigma.fst

theorem exists_of_mem_keys {a} {l : List (Sigma β)} (h : a ∈ l.keys) : ∃ b : β a, Sigma.mk a b ∈ l :=
  let ⟨⟨a', b'⟩, m, e⟩ := exists_of_mem_map h
  Eq.recOnₓ e (Exists.introₓ b' m)

theorem mem_keys {a} {l : List (Sigma β)} : a ∈ l.keys ↔ ∃ b : β a, Sigma.mk a b ∈ l :=
  ⟨exists_of_mem_keys, fun ⟨b, h⟩ => mem_keys_of_mem h⟩

theorem not_mem_keys {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ b : β a, Sigma.mk a b ∉ l :=
  (not_iff_not_of_iff mem_keys).trans not_exists

theorem not_eq_key {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ s : Sigma β, s ∈ l → a ≠ s.1 :=
  Iff.intro
    (fun h₁ s h₂ e =>
      absurd (mem_keys_of_mem h₂)
        (by
          rwa [e] at h₁))
    fun f h₁ =>
    let ⟨b, h₂⟩ := exists_of_mem_keys h₁
    f _ h₂ rfl

/-! ### `nodupkeys` -/


/--  Determines whether the store uses a key several times. -/
def nodupkeys (l : List (Sigma β)) : Prop :=
  l.keys.nodup

theorem nodupkeys_iff_pairwise {l} : nodupkeys l ↔ Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  pairwise_map _

theorem nodupkeys.pairwise_ne {l} (h : nodupkeys l) : Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  nodupkeys_iff_pairwise.1 h

@[simp]
theorem nodupkeys_nil : @nodupkeys α β [] :=
  pairwise.nil

@[simp]
theorem nodupkeys_cons {s : Sigma β} {l : List (Sigma β)} : nodupkeys (s :: l) ↔ s.1 ∉ l.keys ∧ nodupkeys l := by
  simp [keys, nodupkeys]

theorem nodupkeys.eq_of_fst_eq {l : List (Sigma β)} (nd : nodupkeys l) {s s' : Sigma β} (h : s ∈ l) (h' : s' ∈ l) :
    s.1 = s'.1 → s = s' :=
  @forall_of_forall_of_pairwise _ (fun s s' : Sigma β => s.1 = s'.1 → s = s') (fun s s' H h => (H h.symm).symm) _
    (fun x h _ => rfl) ((nodupkeys_iff_pairwise.1 nd).imp fun s s' h h' => (h h').elim) _ h _ h'

theorem nodupkeys.eq_of_mk_mem {a : α} {b b' : β a} {l : List (Sigma β)} (nd : nodupkeys l) (h : Sigma.mk a b ∈ l)
    (h' : Sigma.mk a b' ∈ l) : b = b' := by
  cases nd.eq_of_fst_eq h h' rfl <;> rfl

theorem nodupkeys_singleton (s : Sigma β) : nodupkeys [s] :=
  nodup_singleton _

theorem nodupkeys_of_sublist {l₁ l₂ : List (Sigma β)} (h : l₁ <+ l₂) : nodupkeys l₂ → nodupkeys l₁ :=
  nodup_of_sublist (h.map _)

theorem nodup_of_nodupkeys {l : List (Sigma β)} : nodupkeys l → nodup l :=
  nodup_of_nodup_map _

theorem perm_nodupkeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : nodupkeys l₁ ↔ nodupkeys l₂ :=
  (h.map _).nodup_iff

theorem nodupkeys_join {L : List (List (Sigma β))} :
    nodupkeys (join L) ↔ (∀, ∀ l ∈ L, ∀, nodupkeys l) ∧ Pairwise Disjoint (L.map keys) := by
  rw [nodupkeys_iff_pairwise, pairwise_join, pairwise_map]
  refine'
    and_congr
      (ball_congr $ fun l h => by
        simp [nodupkeys_iff_pairwise])
      _
  apply iff_of_eq
  congr with l₁ l₂
  simp [keys, disjoint_iff_ne]

theorem nodup_enum_map_fst (l : List α) : (l.enum.map Prod.fst).Nodup := by
  simp [List.nodup_range]

theorem mem_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.nodup) (nd₁ : l₁.nodup) (h : ∀ x, x ∈ l₀ ↔ x ∈ l₁) : l₀ ~ l₁ := by
  induction' l₀ with x xs generalizing l₁ <;> cases' l₁ with y ys
  ·
    constructor
  iterate 2 
    first |
      specialize h x|
      specialize h y
    simp at h
    cases h
  simp at nd₀ nd₁
  classical
  cases nd₀
  cases nd₁
  by_cases' h' : x = y
  ·
    subst y
    constructor
    apply l₀_ih ‹_› ‹nodup ys›
    intro a
    specialize h a
    simp at h
    by_cases' h' : a = x
    ·
      subst a
      rw [← not_iff_not]
      constructor <;> intro <;> assumption
    ·
      simp [h'] at h
      exact h
  ·
    trans x :: y :: ys.erase x
    ·
      constructor
      apply l₀_ih ‹_›
      ·
        simp
        constructor
        ·
          intro
          apply nd₁_left
          apply mem_of_mem_erase ‹_›
        apply nodup_erase_of_nodup <;> assumption
      ·
        intro a
        specialize h a
        simp at h
        by_cases' h' : a = x
        ·
          subst a
          rw [← not_iff_not]
          constructor <;> intro
          simp [mem_erase_of_nodup]
          assumption
        ·
          simp [h'] at h
          simp [h]
          apply or_congr
          rfl
          simp [mem_erase_of_ne]
    trans y :: x :: ys.erase x
    ·
      constructor
    ·
      constructor
      symm
      apply perm_cons_erase
      specialize h x
      simp [h'] at h
      exact h

variable [DecidableEq α]

/-! ### `lookup` -/


/--  `lookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
def lookup (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOnₓ h b) else lookup l

@[simp]
theorem lookup_nil (a : α) : lookup a [] = @none (β a) :=
  rfl

@[simp]
theorem lookup_cons_eq l (a : α) (b : β a) : lookup a (⟨a, b⟩ :: l) = some b :=
  dif_pos rfl

@[simp]
theorem lookup_cons_ne l {a} : ∀ s : Sigma β, a ≠ s.1 → lookup a (s :: l) = lookup a l
  | ⟨a', b⟩, h => dif_neg h.symm

theorem lookup_is_some {a : α} : ∀ {l : List (Sigma β)}, (lookup a l).isSome ↔ a ∈ l.keys
  | [] => by
    simp
  | ⟨a', b⟩ :: l => by
    by_cases' h : a = a'
    ·
      subst a'
      simp
    ·
      simp [h, lookup_is_some]

theorem lookup_eq_none {a : α} {l : List (Sigma β)} : lookup a l = none ↔ a ∉ l.keys := by
  simp [← lookup_is_some, Option.is_none_iff_eq_none]

theorem of_mem_lookup {a : α} {b : β a} : ∀ {l : List (Sigma β)}, b ∈ lookup a l → Sigma.mk a b ∈ l
  | ⟨a', b'⟩ :: l, H => by
    by_cases' h : a = a'
    ·
      subst a'
      simp at H
      simp [H]
    ·
      simp [h] at H
      exact Or.inr (of_mem_lookup H)

theorem mem_lookup {a} {b : β a} {l : List (Sigma β)} (nd : l.nodupkeys) (h : Sigma.mk a b ∈ l) : b ∈ lookup a l := by
  cases' option.is_some_iff_exists.mp (lookup_is_some.mpr (mem_keys_of_mem h)) with b' h'
  cases nd.eq_of_mk_mem h (of_mem_lookup h')
  exact h'

theorem map_lookup_eq_find (a : α) : ∀ l : List (Sigma β), (lookup a l).map (Sigma.mk a) = find (fun s => a = s.1) l
  | [] => rfl
  | ⟨a', b'⟩ :: l => by
    by_cases' h : a = a'
    ·
      subst a'
      simp
    ·
      simp [h, map_lookup_eq_find]

theorem mem_lookup_iff {a : α} {b : β a} {l : List (Sigma β)} (nd : l.nodupkeys) : b ∈ lookup a l ↔ Sigma.mk a b ∈ l :=
  ⟨of_mem_lookup, mem_lookup nd⟩

theorem perm_lookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) :
    lookup a l₁ = lookup a l₂ := by
  ext b <;> simp [mem_lookup_iff, nd₁, nd₂] <;> exact p.mem_iff

theorem lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.nodupkeys) (nd₁ : l₁.nodupkeys)
    (h : ∀ x y, y ∈ l₀.lookup x ↔ y ∈ l₁.lookup x) : l₀ ~ l₁ :=
  mem_ext (nodup_of_nodupkeys nd₀) (nodup_of_nodupkeys nd₁) fun ⟨a, b⟩ => by
    rw [← mem_lookup_iff, ← mem_lookup_iff, h] <;> assumption

/-! ### `lookup_all` -/


/--  `lookup_all a l` is the list of all values in `l` corresponding to the key `a`. -/
def lookup_all (a : α) : List (Sigma β) → List (β a)
  | [] => []
  | ⟨a', b⟩ :: l => if h : a' = a then Eq.recOnₓ h b :: lookup_all l else lookup_all l

@[simp]
theorem lookup_all_nil (a : α) : lookup_all a [] = @nil (β a) :=
  rfl

@[simp]
theorem lookup_all_cons_eq l (a : α) (b : β a) : lookup_all a (⟨a, b⟩ :: l) = b :: lookup_all a l :=
  dif_pos rfl

@[simp]
theorem lookup_all_cons_ne l {a} : ∀ s : Sigma β, a ≠ s.1 → lookup_all a (s :: l) = lookup_all a l
  | ⟨a', b⟩, h => dif_neg h.symm

theorem lookup_all_eq_nil {a : α} : ∀ {l : List (Sigma β)}, lookup_all a l = [] ↔ ∀ b : β a, Sigma.mk a b ∉ l
  | [] => by
    simp
  | ⟨a', b⟩ :: l => by
    by_cases' h : a = a'
    ·
      subst a'
      simp
    ·
      simp [h, lookup_all_eq_nil]

theorem head_lookup_all (a : α) : ∀ l : List (Sigma β), head' (lookup_all a l) = lookup a l
  | [] => by
    simp
  | ⟨a', b⟩ :: l => by
    by_cases' h : a = a' <;>
      [·
        subst h
        simp ,
      simp ]

theorem mem_lookup_all {a : α} {b : β a} : ∀ {l : List (Sigma β)}, b ∈ lookup_all a l ↔ Sigma.mk a b ∈ l
  | [] => by
    simp
  | ⟨a', b'⟩ :: l => by
    by_cases' h : a = a' <;>
      [·
        subst h
        simp ,
      simp ]

theorem lookup_all_sublist (a : α) : ∀ l : List (Sigma β), (lookup_all a l).map (Sigma.mk a) <+ l
  | [] => by
    simp
  | ⟨a', b'⟩ :: l => by
    by_cases' h : a = a'
    ·
      subst h
      simp
      exact (lookup_all_sublist l).cons2 _ _ _
    ·
      simp [h]
      exact (lookup_all_sublist l).cons _ _ _

theorem lookup_all_length_le_one (a : α) {l : List (Sigma β)} (h : l.nodupkeys) : length (lookup_all a l) ≤ 1 := by
  have := nodup_of_sublist ((lookup_all_sublist a l).map _) h <;>
    rw [map_map] at this <;> rwa [← nodup_repeat, ← map_const _ a]

theorem lookup_all_eq_lookup (a : α) {l : List (Sigma β)} (h : l.nodupkeys) : lookup_all a l = (lookup a l).toList := by
  rw [← head_lookup_all]
  have := lookup_all_length_le_one a h
  revert this
  rcases lookup_all a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;>
    intro <;>
      try
        rfl
  exact
    absurd this
      (by
        decide)

theorem lookup_all_nodup (a : α) {l : List (Sigma β)} (h : l.nodupkeys) : (lookup_all a l).Nodup := by
  rw [lookup_all_eq_lookup a h] <;> apply Option.to_list_nodup

theorem perm_lookup_all (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) :
    lookup_all a l₁ = lookup_all a l₂ := by
  simp [lookup_all_eq_lookup, nd₁, nd₂, perm_lookup a nd₁ nd₂ p]

/-! ### `kreplace` -/


/--  Replaces the first value with key `a` by `b`. -/
def kreplace (a : α) (b : β a) : List (Sigma β) → List (Sigma β) :=
  lookmap $ fun s => if a = s.1 then some ⟨a, b⟩ else none

theorem kreplace_of_forall_not (a : α) (b : β a) {l : List (Sigma β)} (H : ∀ b : β a, Sigma.mk a b ∉ l) :
    kreplace a b l = l :=
  lookmap_of_forall_not _ $ by
    rintro ⟨a', b'⟩ h
    dsimp
    split_ifs
    ·
      subst a'
      exact H _ h
    ·
      rfl

theorem kreplace_self {a : α} {b : β a} {l : List (Sigma β)} (nd : nodupkeys l) (h : Sigma.mk a b ∈ l) :
    kreplace a b l = l := by
  refine' (lookmap_congr _).trans (lookmap_id' (Option.guard fun s => a = s.1) _ _)
  ·
    rintro ⟨a', b'⟩ h'
    dsimp [Option.guard]
    split_ifs
    ·
      subst a'
      exact ⟨rfl, heq_of_eq $ nd.eq_of_mk_mem h h'⟩
    ·
      rfl
  ·
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    dsimp [Option.guard]
    split_ifs
    ·
      subst a₁
      rintro ⟨⟩
      simp
    ·
      rintro ⟨⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `keys_kreplace [])
  (Command.declSig
   [(Term.explicitBinder "(" [`a] [":" `α] [] ")") (Term.explicitBinder "(" [`b] [":" (Term.app `β [`a])] [] ")")]
   (Term.typeSpec
    ":"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`l] [(Term.typeSpec ":" (Term.app `List [(Term.app `Sigma [`β])]))])]
     ","
     («term_=_» (Term.proj (Term.app `kreplace [`a `b `l]) "." `keys) "=" `l.keys))))
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.app `lookmap_map_eq [(Term.hole "_") (Term.hole "_")])
    "$"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.«tactic_<;>_»
          (Tactic.rintro
           "rintro"
           [(Tactic.rintroPat.one
             (Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a₁)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b₂)]) [])]
              "⟩"))
            (Tactic.rintroPat.one
             (Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a₂)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b₂)]) [])]
              "⟩"))]
           [])
          "<;>"
          (Tactic.«tactic_<;>_»
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           "<;>"
           (Tactic.«tactic_<;>_»
            (Tactic.splitIfs "split_ifs" [] [])
            "<;>"
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
             ["[" [(Tactic.simpLemma [] [] `h)] "]"]
             []))))
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
  («term_$__»
   (Term.app `lookmap_map_eq [(Term.hole "_") (Term.hole "_")])
   "$"
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.«tactic_<;>_»
         (Tactic.rintro
          "rintro"
          [(Tactic.rintroPat.one
            (Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a₁)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b₂)]) [])]
             "⟩"))
           (Tactic.rintroPat.one
            (Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a₂)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b₂)]) [])]
             "⟩"))]
          [])
         "<;>"
         (Tactic.«tactic_<;>_»
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          "<;>"
          (Tactic.«tactic_<;>_»
           (Tactic.splitIfs "split_ifs" [] [])
           "<;>"
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
            ["[" [(Tactic.simpLemma [] [] `h)] "]"]
            []))))
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a₁)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b₂)]) [])]
            "⟩"))
          (Tactic.rintroPat.one
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a₂)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b₂)]) [])]
            "⟩"))]
         [])
        "<;>"
        (Tactic.«tactic_<;>_»
         (Tactic.dsimp "dsimp" [] [] [] [] [])
         "<;>"
         (Tactic.«tactic_<;>_»
          (Tactic.splitIfs "split_ifs" [] [])
          "<;>"
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
           ["[" [(Tactic.simpLemma [] [] `h)] "]"]
           []))))
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
   (Tactic.rintro
    "rintro"
    [(Tactic.rintroPat.one
      (Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a₁)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b₂)]) [])]
       "⟩"))
     (Tactic.rintroPat.one
      (Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a₂)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b₂)]) [])]
       "⟩"))]
    [])
   "<;>"
   (Tactic.«tactic_<;>_»
    (Tactic.dsimp "dsimp" [] [] [] [] [])
    "<;>"
    (Tactic.«tactic_<;>_»
     (Tactic.splitIfs "split_ifs" [] [])
     "<;>"
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
      ["[" [(Tactic.simpLemma [] [] `h)] "]"]
      []))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.dsimp "dsimp" [] [] [] [] [])
   "<;>"
   (Tactic.«tactic_<;>_»
    (Tactic.splitIfs "split_ifs" [] [])
    "<;>"
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
     ["[" [(Tactic.simpLemma [] [] `h)] "]"]
     [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.splitIfs "split_ifs" [] [])
   "<;>"
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
    ["[" [(Tactic.simpLemma [] [] `h)] "]"]
    []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
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
   ["[" [(Tactic.simpLemma [] [] `h)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
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
theorem
  keys_kreplace
  ( a : α ) ( b : β a ) : ∀ l : List Sigma β , kreplace a b l . keys = l.keys
  :=
    lookmap_map_eq _ _
      $
      by
        rintro ⟨ a₁ , b₂ ⟩ ⟨ a₂ , b₂ ⟩
          <;>
          dsimp <;> split_ifs <;> simp ( config := { contextual := Bool.true._@._internal._hyg.0 } ) [ h ]

theorem kreplace_nodupkeys (a : α) (b : β a) {l : List (Sigma β)} : (kreplace a b l).Nodupkeys ↔ l.nodupkeys := by
  simp [nodupkeys, keys_kreplace]

theorem perm.kreplace {a : α} {b : β a} {l₁ l₂ : List (Sigma β)} (nd : l₁.nodupkeys) :
    l₁ ~ l₂ → kreplace a b l₁ ~ kreplace a b l₂ :=
  perm_lookmap _ $ by
    refine' nd.pairwise_ne.imp _
    intro x y h z h₁ w h₂
    split_ifs  at h₁ h₂ <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim

/-! ### `kerase` -/


/--  Remove the first pair with the key `a`. -/
def kerase (a : α) : List (Sigma β) → List (Sigma β) :=
  erasep $ fun s => a = s.1

@[simp]
theorem kerase_nil {a} : @kerase _ β _ a [] = [] :=
  rfl

@[simp]
theorem kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β)} (h : a = s.1) : kerase a (s :: l) = l := by
  simp [kerase, h]

@[simp]
theorem kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β)} (h : a ≠ s.1) : kerase a (s :: l) = s :: kerase a l := by
  simp [kerase, h]

@[simp]
theorem kerase_of_not_mem_keys {a} {l : List (Sigma β)} (h : a ∉ l.keys) : kerase a l = l := by
  induction' l with _ _ ih <;> [rfl,
    ·
      simp [not_or_distrib] at h
      simp [h.1, ih h.2]]

theorem kerase_sublist (a : α) (l : List (Sigma β)) : kerase a l <+ l :=
  erasep_sublist _

theorem kerase_keys_subset a (l : List (Sigma β)) : (kerase a l).keys ⊆ l.keys :=
  ((kerase_sublist a l).map _).Subset

theorem mem_keys_of_mem_keys_kerase {a₁ a₂} {l : List (Sigma β)} : a₁ ∈ (kerase a₂ l).keys → a₁ ∈ l.keys :=
  @kerase_keys_subset _ _ _ _ _ _

theorem exists_of_kerase {a : α} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ (b : β a)(l₁ l₂ : List (Sigma β)), a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase a l = l₁ ++ l₂ := by
  induction l
  case list.nil =>
    cases h
  case list.cons hd tl ih =>
    by_cases' e : a = hd.1
    ·
      subst e
      exact
        ⟨hd.2, [], tl, by
          simp , by
          cases hd <;> rfl, by
          simp ⟩
    ·
      simp at h
      cases h
      case or.inl h =>
        exact absurd h e
      case or.inr h =>
        rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩
        exact
          ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem e h₁, by
            rw [h₂] <;> rfl, by
            simp [e, h₃]⟩

@[simp]
theorem mem_keys_kerase_of_ne {a₁ a₂} {l : List (Sigma β)} (h : a₁ ≠ a₂) : a₁ ∈ (kerase a₂ l).keys ↔ a₁ ∈ l.keys :=
  Iff.intro mem_keys_of_mem_keys_kerase $ fun p =>
    if q : a₂ ∈ l.keys then
      match l, kerase a₂ l, exists_of_kerase q, p with
      | _, _, ⟨_, _, _, _, rfl, rfl⟩, p => by
        simpa [keys, h] using p
    else by
      simp [q, p]

theorem keys_kerase {a} {l : List (Sigma β)} : (kerase a l).keys = l.keys.erase a := by
  rw [keys, kerase, ← erasep_map Sigma.fst l, erase_eq_erasep]

theorem kerase_kerase {a a'} {l : List (Sigma β)} : (kerase a' l).kerase a = (kerase a l).kerase a' := by
  by_cases' a = a'
  ·
    subst a'
  induction' l with x xs
  ·
    rfl
  ·
    by_cases' a' = x.1
    ·
      subst a'
      simp [kerase_cons_ne h, kerase_cons_eq rfl]
    by_cases' h' : a = x.1
    ·
      subst a
      simp [kerase_cons_eq rfl, kerase_cons_ne (Ne.symm h)]
    ·
      simp [kerase_cons_ne]

theorem kerase_nodupkeys (a : α) {l : List (Sigma β)} : nodupkeys l → (kerase a l).Nodupkeys :=
  nodupkeys_of_sublist $ kerase_sublist _ _

theorem perm.kerase {a : α} {l₁ l₂ : List (Sigma β)} (nd : l₁.nodupkeys) : l₁ ~ l₂ → kerase a l₁ ~ kerase a l₂ :=
  perm.erasep _ $
    (nodupkeys_iff_pairwise.1 nd).imp $ by
      rintro x y h rfl <;> exact h

@[simp]
theorem not_mem_keys_kerase a {l : List (Sigma β)} (nd : l.nodupkeys) : a ∉ (kerase a l).keys := by
  induction l
  case list.nil =>
    simp
  case list.cons hd tl ih =>
    simp at nd
    by_cases' h : a = hd.1
    ·
      subst h
      simp [nd.1]
    ·
      simp [h, ih nd.2]

@[simp]
theorem lookup_kerase a {l : List (Sigma β)} (nd : l.nodupkeys) : lookup a (kerase a l) = none :=
  lookup_eq_none.mpr (not_mem_keys_kerase a nd)

@[simp]
theorem lookup_kerase_ne {a a'} {l : List (Sigma β)} (h : a ≠ a') : lookup a (kerase a' l) = lookup a l := by
  induction l
  case list.nil =>
    rfl
  case list.cons hd tl ih =>
    cases' hd with ah bh
    by_cases' h₁ : a = ah <;> by_cases' h₂ : a' = ah
    ·
      substs h₁ h₂
      cases Ne.irrefl h
    ·
      subst h₁
      simp [h₂]
    ·
      subst h₂
      simp [h]
    ·
      simp [h₁, h₂, ih]

theorem kerase_append_left {a} : ∀ {l₁ l₂ : List (Sigma β)}, a ∈ l₁.keys → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂
  | [], _, h => by
    cases h
  | s :: l₁, l₂, h₁ =>
    if h₂ : a = s.1 then by
      simp [h₂]
    else by
      simp at h₁ <;> cases h₁ <;> [exact absurd h₁ h₂, simp [h₂, kerase_append_left h₁]]

theorem kerase_append_right {a} : ∀ {l₁ l₂ : List (Sigma β)}, a ∉ l₁.keys → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂
  | [], _, h => rfl
  | _ :: l₁, l₂, h => by
    simp [not_or_distrib] at h <;> simp [h.1, kerase_append_right h.2]

theorem kerase_comm a₁ a₂ (l : List (Sigma β)) : kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
  if h : a₁ = a₂ then by
    simp [h]
  else
    if ha₁ : a₁ ∈ l.keys then
      if ha₂ : a₂ ∈ l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, a₂_in_l₁_app_l₂ =>
          if h' : a₂ ∈ l₁.keys then by
            simp [kerase_append_left h', kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
          else by
            simp [kerase_append_right h', kerase_append_right a₁_nin_l₁,
              @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (Ne.symm h)]
      else by
        simp [ha₂, mt mem_keys_of_mem_keys_kerase ha₂]
    else by
      simp [ha₁, mt mem_keys_of_mem_keys_kerase ha₁]

theorem sizeof_kerase {α} {β : α → Type _} [DecidableEq α] [SizeOf (Sigma β)] (x : α) (xs : List (Sigma β)) :
    sizeof (List.kerase x xs) ≤ sizeof xs := by
  unfold_wf
  induction' xs with y ys
  ·
    simp
  ·
    by_cases' x = y.1 <;> simp [List.sizeof]

/-! ### `kinsert` -/


/--  Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
def kinsert (a : α) (b : β a) (l : List (Sigma β)) : List (Sigma β) :=
  ⟨a, b⟩ :: kerase a l

@[simp]
theorem kinsert_def {a} {b : β a} {l : List (Sigma β)} : kinsert a b l = ⟨a, b⟩ :: kerase a l :=
  rfl

theorem mem_keys_kinsert {a a'} {b' : β a'} {l : List (Sigma β)} : a ∈ (kinsert a' b' l).keys ↔ a = a' ∨ a ∈ l.keys :=
  by
  by_cases' h : a = a' <;> simp [h]

theorem kinsert_nodupkeys a (b : β a) {l : List (Sigma β)} (nd : l.nodupkeys) : (kinsert a b l).Nodupkeys :=
  nodupkeys_cons.mpr ⟨not_mem_keys_kerase a nd, kerase_nodupkeys a nd⟩

theorem perm.kinsert {a} {b : β a} {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.nodupkeys) (p : l₁ ~ l₂) :
    kinsert a b l₁ ~ kinsert a b l₂ :=
  (p.kerase nd₁).cons _

theorem lookup_kinsert {a} {b : β a} (l : List (Sigma β)) : lookup a (kinsert a b l) = some b := by
  simp only [kinsert, lookup_cons_eq]

theorem lookup_kinsert_ne {a a'} {b' : β a'} {l : List (Sigma β)} (h : a ≠ a') :
    lookup a (kinsert a' b' l) = lookup a l := by
  simp [h]

/-! ### `kextract` -/


/--  Finds the first entry with a given key `a` and returns its value (as an `option` because there
might be no entry with key `a`) alongside with the rest of the entries. -/
def kextract (a : α) : List (Sigma β) → Option (β a) × List (Sigma β)
  | [] => (none, [])
  | s :: l =>
    if h : s.1 = a then (some (Eq.recOnₓ h s.2), l)
    else
      let (b', l') := kextract l
      (b', s :: l')

@[simp]
theorem kextract_eq_lookup_kerase (a : α) : ∀ l : List (Sigma β), kextract a l = (lookup a l, kerase a l)
  | [] => rfl
  | ⟨a', b⟩ :: l => by
    simp [kextract]
    dsimp
    split_ifs
    ·
      subst a'
      simp [kerase]
    ·
      simp [kextract, Ne.symm h, kextract_eq_lookup_kerase l, kerase]

/-! ### `erase_dupkeys` -/


/--  Remove entries with duplicate keys from `l : list (sigma β)`. -/
def erase_dupkeys : List (Sigma β) → List (Sigma β) :=
  List.foldr (fun x => kinsert x.1 x.2) []

theorem erase_dupkeys_cons {x : Sigma β} (l : List (Sigma β)) :
    erase_dupkeys (x :: l) = kinsert x.1 x.2 (erase_dupkeys l) :=
  rfl

theorem nodupkeys_erase_dupkeys (l : List (Sigma β)) : nodupkeys (erase_dupkeys l) := by
  dsimp [erase_dupkeys]
  generalize hl : nil = l'
  have : nodupkeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction' l with x xs
  ·
    apply this
  ·
    cases x
    simp [erase_dupkeys]
    constructor
    ·
      simp [keys_kerase]
      apply mem_erase_of_nodup l_ih
    apply kerase_nodupkeys _ l_ih

theorem lookup_erase_dupkeys (a : α) (l : List (Sigma β)) : lookup a (erase_dupkeys l) = lookup a l := by
  induction l
  rfl
  cases' l_hd with a' b
  by_cases' a = a'
  ·
    subst a'
    rw [erase_dupkeys_cons, lookup_kinsert, lookup_cons_eq]
  ·
    rw [erase_dupkeys_cons, lookup_kinsert_ne h, l_ih, lookup_cons_ne]
    exact h

theorem sizeof_erase_dupkeys {α} {β : α → Type _} [DecidableEq α] [SizeOf (Sigma β)] (xs : List (Sigma β)) :
    sizeof (List.eraseDupkeys xs) ≤ sizeof xs := by
  unfold_wf
  induction' xs with x xs
  ·
    simp [List.eraseDupkeys]
  ·
    simp only [erase_dupkeys_cons, List.sizeof, kinsert_def, add_le_add_iff_left, Sigma.eta]
    trans
    apply sizeof_kerase
    assumption

/-! ### `kunion` -/


/--  `kunion l₁ l₂` is the append to l₁ of l₂ after, for each key in l₁, the
first matching pair in l₂ is erased. -/
def kunion : List (Sigma β) → List (Sigma β) → List (Sigma β)
  | [], l₂ => l₂
  | s :: l₁, l₂ => s :: kunion l₁ (kerase s.1 l₂)

@[simp]
theorem nil_kunion {l : List (Sigma β)} : kunion [] l = l :=
  rfl

@[simp]
theorem kunion_nil : ∀ {l : List (Sigma β)}, kunion l [] = l
  | [] => rfl
  | _ :: l => by
    rw [kunion, kerase_nil, kunion_nil]

@[simp]
theorem kunion_cons {s} {l₁ l₂ : List (Sigma β)} : kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂) :=
  rfl

@[simp]
theorem mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} : a ∈ (kunion l₁ l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys := by
  induction l₁ generalizing l₂
  case list.nil =>
    simp
  case list.cons s l₁ ih =>
    by_cases' h : a = s.1 <;> [simp [h], simp [h, ih]]

@[simp]
theorem kunion_kerase {a} : ∀ {l₁ l₂ : List (Sigma β)}, kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)
  | [], _ => rfl
  | s :: _, l => by
    by_cases' h : a = s.1 <;> simp [h, kerase_comm a s.1 l, kunion_kerase]

theorem kunion_nodupkeys {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) :
    (kunion l₁ l₂).Nodupkeys := by
  induction l₁ generalizing l₂
  case list.nil =>
    simp only [nil_kunion, nd₂]
  case list.cons s l₁ ih =>
    simp at nd₁
    simp [not_or_distrib, nd₁.1, nd₂, ih nd₁.2 (kerase_nodupkeys s.1 nd₂)]

theorem perm.kunion_right {l₁ l₂ : List (Sigma β)} (p : l₁ ~ l₂) l : kunion l₁ l ~ kunion l₂ l := by
  induction p generalizing l
  case list.perm.nil =>
    rfl
  case list.perm.cons hd tl₁ tl₂ p ih =>
    simp [ih (kerase hd.1 l), perm.cons]
  case list.perm.swap s₁ s₂ l =>
    simp [kerase_comm, perm.swap]
  case list.perm.trans l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ =>
    exact perm.trans (ih₁₂ l) (ih₂₃ l)

theorem perm.kunion_left : ∀ l {l₁ l₂ : List (Sigma β)}, l₁.nodupkeys → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂
  | [], _, _, _, p => p
  | s :: l, l₁, l₂, nd₁, p => by
    simp [((p.kerase nd₁).kunion_left l (kerase_nodupkeys s.1 nd₁)).cons s]

theorem perm.kunion {l₁ l₂ l₃ l₄ : List (Sigma β)} (nd₃ : l₃.nodupkeys) (p₁₂ : l₁ ~ l₂) (p₃₄ : l₃ ~ l₄) :
    kunion l₁ l₃ ~ kunion l₂ l₄ :=
  (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)

@[simp]
theorem lookup_kunion_left {a} {l₁ l₂ : List (Sigma β)} (h : a ∈ l₁.keys) : lookup a (kunion l₁ l₂) = lookup a l₁ := by
  induction' l₁ with s _ ih generalizing l₂ <;> simp at h <;> cases h <;> cases' s with a'
  ·
    subst h
    simp
  ·
    rw [kunion_cons]
    by_cases' h' : a = a'
    ·
      subst h'
      simp
    ·
      simp [h', ih h]

@[simp]
theorem lookup_kunion_right {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys) : lookup a (kunion l₁ l₂) = lookup a l₂ := by
  induction l₁ generalizing l₂
  case list.nil =>
    simp
  case list.cons _ _ ih =>
    simp [not_or_distrib] at h
    simp [h.1, ih h.2]

@[simp]
theorem mem_lookup_kunion {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    b ∈ lookup a (kunion l₁ l₂) ↔ b ∈ lookup a l₁ ∨ a ∉ l₁.keys ∧ b ∈ lookup a l₂ := by
  induction l₁ generalizing l₂
  case list.nil =>
    simp
  case list.cons s _ ih =>
    cases' s with a'
    by_cases' h₁ : a = a'
    ·
      subst h₁
      simp
    ·
      let h₂ := @ih (kerase a' l₂)
      simp [h₁] at h₂
      simp [h₁, h₂]

theorem mem_lookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)} (h₁ : b ∈ lookup a (kunion l₁ l₃))
    (h₂ : a ∉ keys l₂) : b ∈ lookup a (kunion (kunion l₁ l₂) l₃) :=
  match mem_lookup_kunion.mp h₁ with
  | Or.inl h => mem_lookup_kunion.mpr (Or.inl (mem_lookup_kunion.mpr (Or.inl h)))
  | Or.inr h => mem_lookup_kunion.mpr $ Or.inr ⟨mt mem_keys_kunion.mp (not_or_distrib.mpr ⟨h.1, h₂⟩), h.2⟩

end List

