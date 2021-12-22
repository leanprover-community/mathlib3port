import Mathbin.Data.Finset.Card
import Mathbin.Data.Fintype.Basic
import Mathbin.GroupTheory.Perm.Basic

/-!
# Support of a permutation

## Main definitions

In the following, `f g : equiv.perm α`.

* `equiv.perm.disjoint`: two permutations `f` and `g` are `disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `disjoint` iff their `support` are disjoint.
* `equiv.perm.is_swap`: `f = swap x y` for `x ≠ y`.
* `equiv.perm.support`: the elements `x : α` that are not fixed by `f`.

-/


open Equivₓ Finset

namespace Equivₓ.Perm

variable {α : Type _}

section Disjoint

/--  Two permutations `f` and `g` are `disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def Disjoint (f g : perm α) :=
  ∀ x, f x = x ∨ g x = x

variable {f g h : perm α}

@[symm]
theorem Disjoint.symm : Disjoint f g → Disjoint g f := by
  simp only [Disjoint, Or.comm, imp_self]

theorem disjoint.symmetric : Symmetric (@Disjoint α) := fun _ _ => Disjoint.symm

theorem disjoint_comm : Disjoint f g ↔ Disjoint g f :=
  ⟨Disjoint.symm, Disjoint.symm⟩

theorem disjoint.commute (h : Disjoint f g) : Commute f g :=
  Equivₓ.ext $ fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim
          (fun hg => by
            simp [mul_apply, hf, hg])
          fun hg => by
          simp [mul_apply, hf, g.injective hg])
      fun hg =>
      (h (f x)).elim
        (fun hf => by
          simp [mul_apply, f.injective hf, hg])
        fun hf => by
        simp [mul_apply, hf, hg]

@[simp]
theorem disjoint_one_left (f : perm α) : Disjoint 1 f := fun _ => Or.inl rfl

@[simp]
theorem disjoint_one_right (f : perm α) : Disjoint f 1 := fun _ => Or.inr rfl

theorem disjoint_iff_eq_or_eq : Disjoint f g ↔ ∀ x : α, f x = x ∨ g x = x :=
  Iff.rfl

@[simp]
theorem disjoint_refl_iff : Disjoint f f ↔ f = 1 := by
  refine' ⟨fun h => _, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  cases' h x with hx hx <;> simp [hx]

theorem disjoint.inv_left (h : Disjoint f g) : Disjoint (f⁻¹) g := by
  intro x
  rw [inv_eq_iff_eq, eq_comm]
  exact h x

theorem disjoint.inv_right (h : Disjoint f g) : Disjoint f (g⁻¹) :=
  h.symm.inv_left.symm

@[simp]
theorem disjoint_inv_left_iff : Disjoint (f⁻¹) g ↔ Disjoint f g := by
  refine' ⟨fun h => _, disjoint.inv_left⟩
  convert h.inv_left
  exact (inv_invₓ _).symm

@[simp]
theorem disjoint_inv_right_iff : Disjoint f (g⁻¹) ↔ Disjoint f g := by
  rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]

theorem disjoint.mul_left (H1 : Disjoint f h) (H2 : Disjoint g h) : Disjoint (f*g) h := fun x => by
  cases H1 x <;> cases H2 x <;> simp

theorem disjoint.mul_right (H1 : Disjoint f g) (H2 : Disjoint f h) : Disjoint f (g*h) := by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

theorem disjoint_prod_right (l : List (perm α)) (h : ∀, ∀ g ∈ l, ∀, Disjoint f g) : Disjoint f l.prod := by
  induction' l with g l ih
  ·
    exact disjoint_one_right _
  ·
    rw [List.prod_cons]
    exact (h _ (List.mem_cons_selfₓ _ _)).mul_right (ih fun g hg => h g (List.mem_cons_of_memₓ _ hg))

theorem disjoint_prod_perm {l₁ l₂ : List (perm α)} (hl : l₁.pairwise Disjoint) (hp : l₁ ~ l₂) : l₁.prod = l₂.prod :=
  hp.prod_eq' $ hl.imp $ fun f g => disjoint.commute

theorem nodup_of_pairwise_disjoint {l : List (perm α)} (h1 : (1 : perm α) ∉ l) (h2 : l.pairwise Disjoint) : l.nodup :=
  by
  refine' List.Pairwiseₓ.imp_of_mem _ h2
  rintro σ - h_mem - h_disjoint rfl
  suffices σ = 1by
    rw [this] at h_mem
    exact h1 h_mem
  exact ext fun a => (or_selfₓ _).mp (h_disjoint a)

theorem pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℕ, (f ^ n) x = x
  | 0 => rfl
  | n+1 => by
    rw [pow_succ'ₓ, mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self]

theorem zpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℤ, (f ^ n) x = x
  | (n : ℕ) => pow_apply_eq_self_of_apply_eq_self hfx n
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]

theorem pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) : ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
  | 0 => Or.inl rfl
  | n+1 =>
    (pow_apply_eq_of_apply_apply_eq_self n).elim
      (fun h =>
        Or.inr
          (by
            rw [pow_succₓ, mul_apply, h]))
      fun h =>
      Or.inl
        (by
          rw [pow_succₓ, mul_apply, h, hffx])

theorem zpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) : ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
  | (n : ℕ) => pow_apply_eq_of_apply_apply_eq_self hffx n
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply, ← pow_succₓ, eq_comm, inv_eq_iff_eq, ←
      mul_apply, ← pow_succ'ₓ, @eq_comm _ x, Or.comm]
    exact pow_apply_eq_of_apply_apply_eq_self hffx _

theorem disjoint.mul_apply_eq_iff {σ τ : perm α} (hστ : Disjoint σ τ) {a : α} : (σ*τ) a = a ↔ σ a = a ∧ τ a = a := by
  refine'
    ⟨fun h => _, fun h => by
      rw [mul_apply, h.2, h.1]⟩
  cases' hστ a with hσ hτ
  ·
    exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
  ·
    exact ⟨(congr_argₓ σ hτ).symm.trans h, hτ⟩

theorem disjoint.mul_eq_one_iff {σ τ : perm α} (hστ : Disjoint σ τ) : (σ*τ) = 1 ↔ σ = 1 ∧ τ = 1 := by
  simp_rw [ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and_distrib]

theorem disjoint.zpow_disjoint_zpow {σ τ : perm α} (hστ : Disjoint σ τ) (m n : ℤ) : Disjoint (σ ^ m) (τ ^ n) := fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m) (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)

theorem disjoint.pow_disjoint_pow {σ τ : perm α} (hστ : Disjoint σ τ) (m n : ℕ) : Disjoint (σ ^ m) (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n

end Disjoint

section IsSwap

variable [DecidableEq α]

/--  `f.is_swap` indicates that the permutation `f` is a transposition of two elements. -/
def is_swap (f : perm α) : Prop :=
  ∃ x y, x ≠ y ∧ f = swap x y

theorem is_swap.of_subtype_is_swap {p : α → Prop} [DecidablePred p] {f : perm (Subtype p)} (h : f.is_swap) :
    (of_subtype f).IsSwap :=
  let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [Ne.def] at hxy
    exact hxy.1,
    Equivₓ.ext $ fun z => by
      rw [hxy.2, of_subtype]
      simp only [swap_apply_def, coe_fn_mk, swap_inv, Subtype.mk_eq_mk, MonoidHom.coe_mk]
      split_ifs <;>
        first |
          rw [Subtype.coe_mk]|
          cc⟩

theorem ne_and_ne_of_swap_mul_apply_ne_self {f : perm α} {x y : α} (hy : (swap x (f x)*f) y ≠ y) : f y ≠ y ∧ y ≠ x := by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  by_cases' h : f y = x
  ·
    constructor <;> intro <;> simp_all only [if_true, eq_self_iff_true, not_true, Ne.def]
  ·
    split_ifs  at hy <;> cc

end IsSwap

section Support

section Set

variable (p q : perm α)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `set_support_inv_eq [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app (Init.Logic.«term_⁻¹» `p "⁻¹") [`x]) "≠" `x) "}")
     "="
     (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `Set.mem_set_of_eq) "," (Tactic.simpLemma [] [] `Ne.def)] "]"]
         [])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `inv_def) "," (Tactic.rwRule [] `symm_apply_eq) "," (Tactic.rwRule [] `eq_comm)]
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
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Set.mem_set_of_eq) "," (Tactic.simpLemma [] [] `Ne.def)] "]"]
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `inv_def) "," (Tactic.rwRule [] `symm_apply_eq) "," (Tactic.rwRule [] `eq_comm)]
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
    [(Tactic.rwRule [] `inv_def) "," (Tactic.rwRule [] `symm_apply_eq) "," (Tactic.rwRule [] `eq_comm)]
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
  `symm_apply_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inv_def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Set.mem_set_of_eq) "," (Tactic.simpLemma [] [] `Ne.def)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Ne.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app (Init.Logic.«term_⁻¹» `p "⁻¹") [`x]) "≠" `x) "}")
   "="
   (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_» (Term.app `p [`x]) "≠" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `p [`x])
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
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
  set_support_inv_eq
  : { x | p ⁻¹ x ≠ x } = { x | p x ≠ x }
  := by ext x simp only [ Set.mem_set_of_eq , Ne.def ] rw [ inv_def , symm_apply_eq , eq_comm ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `set_support_apply_mem [])
  (Command.declSig
   [(Term.implicitBinder "{" [`p] [":" (Term.app `perm [`α])] "}") (Term.implicitBinder "{" [`a] [":" `α] "}")]
   (Term.typeSpec
    ":"
    («term_↔_»
     (Init.Core.«term_∈_»
      (Term.app `p [`a])
      " ∈ "
      (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}"))
     "↔"
     (Init.Core.«term_∈_» `a " ∈ " (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}")))))
  (Command.declValSimple
   ":="
   (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
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
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_↔_»
   (Init.Core.«term_∈_» (Term.app `p [`a]) " ∈ " (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}"))
   "↔"
   (Init.Core.«term_∈_» `a " ∈ " (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_↔_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» `a " ∈ " (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_» (Term.app `p [`x]) "≠" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `p [`x])
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
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
theorem set_support_apply_mem { p : perm α } { a : α } : p a ∈ { x | p x ≠ x } ↔ a ∈ { x | p x ≠ x } := by simp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `set_support_zpow_subset [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℤ "ℤ")] [] ")")]
   (Term.typeSpec
    ":"
    (Init.Core.«term_⊆_»
     (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app («term_^_» `p "^" `n) [`x]) "≠" `x) "}")
     " ⊆ "
     (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.intro "intro" [`x]) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `Set.mem_set_of_eq) "," (Tactic.simpLemma [] [] `Ne.def)] "]"]
         [])
        [])
       (group (Tactic.intro "intro" [`hx `H]) [])
       (group
        (Tactic.simpa
         "simpa"
         []
         []
         ["[" [(Tactic.simpLemma [] [] (Term.app `zpow_apply_eq_self_of_apply_eq_self [`H]))] "]"]
         []
         ["using" `hx])
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
     [(group (Tactic.intro "intro" [`x]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Set.mem_set_of_eq) "," (Tactic.simpLemma [] [] `Ne.def)] "]"]
        [])
       [])
      (group (Tactic.intro "intro" [`hx `H]) [])
      (group
       (Tactic.simpa
        "simpa"
        []
        []
        ["[" [(Tactic.simpLemma [] [] (Term.app `zpow_apply_eq_self_of_apply_eq_self [`H]))] "]"]
        []
        ["using" `hx])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   []
   ["[" [(Tactic.simpLemma [] [] (Term.app `zpow_apply_eq_self_of_apply_eq_self [`H]))] "]"]
   []
   ["using" `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `zpow_apply_eq_self_of_apply_eq_self [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `H
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `zpow_apply_eq_self_of_apply_eq_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`hx `H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `H
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Set.mem_set_of_eq) "," (Tactic.simpLemma [] [] `Ne.def)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Ne.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Init.Core.«term_⊆_»
   (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app («term_^_» `p "^" `n) [`x]) "≠" `x) "}")
   " ⊆ "
   (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_» (Term.app `p [`x]) "≠" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `p [`x])
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
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
  set_support_zpow_subset
  ( n : ℤ ) : { x | p ^ n x ≠ x } ⊆ { x | p x ≠ x }
  :=
    by
      intro x
        simp only [ Set.mem_set_of_eq , Ne.def ]
        intro hx H
        simpa [ zpow_apply_eq_self_of_apply_eq_self H ] using hx

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `set_support_mul_subset [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    (Init.Core.«term_⊆_»
     (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app (Finset.Data.Finset.Fold.«term_*_» `p "*" `q) [`x]) "≠" `x) "}")
     " ⊆ "
     (Init.Core.«term_∪_»
      (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}")
      " ∪ "
      (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `q [`x]) "≠" `x) "}")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.intro "intro" [`x]) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `perm.coe_mul)
           ","
           (Tactic.simpLemma [] [] `Function.comp_app)
           ","
           (Tactic.simpLemma [] [] `Ne.def)
           ","
           (Tactic.simpLemma [] [] `Set.mem_union_eq)
           ","
           (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
          "]"]
         [])
        [])
       (group
        (Tactic.«tactic_<;>_»
         (Tactic.byCases' "by_cases'" [`hq ":"] («term_=_» (Term.app `q [`x]) "=" `x))
         "<;>"
         (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hq)] "]"] []))
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
     [(group (Tactic.intro "intro" [`x]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `perm.coe_mul)
          ","
          (Tactic.simpLemma [] [] `Function.comp_app)
          ","
          (Tactic.simpLemma [] [] `Ne.def)
          ","
          (Tactic.simpLemma [] [] `Set.mem_union_eq)
          ","
          (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
         "]"]
        [])
       [])
      (group
       (Tactic.«tactic_<;>_»
        (Tactic.byCases' "by_cases'" [`hq ":"] («term_=_» (Term.app `q [`x]) "=" `x))
        "<;>"
        (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hq)] "]"] []))
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
   (Tactic.byCases' "by_cases'" [`hq ":"] («term_=_» (Term.app `q [`x]) "=" `x))
   "<;>"
   (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hq)] "]"] []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hq)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.byCases' "by_cases'" [`hq ":"] («term_=_» (Term.app `q [`x]) "=" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.byCases'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `q [`x]) "=" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `q [`x])
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
  `q
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«:»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `perm.coe_mul)
     ","
     (Tactic.simpLemma [] [] `Function.comp_app)
     ","
     (Tactic.simpLemma [] [] `Ne.def)
     ","
     (Tactic.simpLemma [] [] `Set.mem_union_eq)
     ","
     (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_union_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Ne.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Function.comp_app
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `perm.coe_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Init.Core.«term_⊆_»
   (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app (Finset.Data.Finset.Fold.«term_*_» `p "*" `q) [`x]) "≠" `x) "}")
   " ⊆ "
   (Init.Core.«term_∪_»
    (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}")
    " ∪ "
    (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `q [`x]) "≠" `x) "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∪_»
   (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `p [`x]) "≠" `x) "}")
   " ∪ "
   (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `q [`x]) "≠" `x) "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∪_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `q [`x]) "≠" `x) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_» (Term.app `q [`x]) "≠" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `q [`x])
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
  `q
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
  set_support_mul_subset
  : { x | p * q x ≠ x } ⊆ { x | p x ≠ x } ∪ { x | q x ≠ x }
  :=
    by
      intro x
        simp only [ perm.coe_mul , Function.comp_app , Ne.def , Set.mem_union_eq , Set.mem_set_of_eq ]
        by_cases' hq : q x = x <;> simp [ hq ]

end Set

variable [DecidableEq α] [Fintype α] {f g : perm α}

/--  The `finset` of nonfixed points of a permutation. -/
def support (f : perm α) : Finset α :=
  univ.filter fun x => f x ≠ x

@[simp]
theorem mem_support {x : α} : x ∈ f.support ↔ f x ≠ x := by
  rw [support, mem_filter, and_iff_right (mem_univ x)]

theorem not_mem_support {x : α} : x ∉ f.support ↔ f x = x := by
  simp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `coe_support_eq_set_support [])
  (Command.declSig
   [(Term.explicitBinder "(" [`f] [":" (Term.app `perm [`α])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")")
     "="
     (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `f [`x]) "≠" `x) "}"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented [(group (Tactic.ext "ext" [] []) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
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
    (Tactic.tacticSeq1Indented [(group (Tactic.ext "ext" [] []) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")")
   "="
   (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `f [`x]) "≠" `x) "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `x "|" («term_≠_» (Term.app `f [`x]) "≠" `x) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_» (Term.app `f [`x]) "≠" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `f [`x])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
theorem coe_support_eq_set_support ( f : perm α ) : ( f.support : Set α ) = { x | f x ≠ x } := by ext simp

@[simp]
theorem support_eq_empty_iff {σ : perm α} : σ.support = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_support, Finset.not_mem_empty, iff_falseₓ, not_not, Equivₓ.Perm.ext_iff, one_apply]

@[simp]
theorem support_one : (1 : perm α).support = ∅ := by
  rw [support_eq_empty_iff]

@[simp]
theorem support_refl : support (Equivₓ.refl α) = ∅ :=
  support_one

theorem support_congr (h : f.support ⊆ g.support) (h' : ∀, ∀ x ∈ g.support, ∀, f x = g x) : f = g := by
  ext x
  by_cases' hx : x ∈ g.support
  ·
    exact h' x hx
  ·
    rw [not_mem_support.mp hx, ← not_mem_support]
    exact fun H => hx (h H)

theorem support_mul_le (f g : perm α) : (f*g).support ≤ f.support⊔g.support := fun x => by
  rw [sup_eq_union, mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_distrib, not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg, hf]

theorem exists_mem_support_of_mem_support_prod {l : List (perm α)} {x : α} (hx : x ∈ l.prod.support) :
    ∃ f : perm α, f ∈ l ∧ x ∈ f.support := by
  contrapose! hx
  simp_rw [mem_support, not_not]  at hx⊢
  induction' l with f l ih generalizing hx
  ·
    rfl
  ·
    rw [List.prod_cons, mul_apply, ih fun g hg => hx g (Or.inr hg), hx f (Or.inl rfl)]

theorem support_pow_le (σ : perm α) (n : ℕ) : (σ ^ n).support ≤ σ.support := fun x h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
theorem support_inv (σ : perm α) : support (σ⁻¹) = σ.support := by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, iff_selfₓ, imp_true_iff]

@[simp]
theorem apply_mem_support {x : α} : f x ∈ f.support ↔ x ∈ f.support := by
  rw [mem_support, mem_support, Ne.def, Ne.def, not_iff_not, apply_eq_iff_eq]

@[simp]
theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  induction' n with n ih
  ·
    rfl
  rw [pow_succₓ, perm.mul_apply, apply_mem_support, ih]

@[simp]
theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  cases n
  ·
    rw [Int.of_nat_eq_coe, zpow_coe_nat, pow_apply_mem_support]
  ·
    rw [zpow_neg_succ_of_nat, ← support_inv, ← inv_pow, pow_apply_mem_support]

theorem pow_eq_on_of_mem_support (h : ∀, ∀ x ∈ f.support ∩ g.support, ∀, f x = g x) (k : ℕ) :
    ∀, ∀ x ∈ f.support ∩ g.support, ∀, (f ^ k) x = (g ^ k) x := by
  induction' k with k hk
  ·
    simp
  ·
    intro x hx
    rw [pow_succ'ₓ, mul_apply, pow_succ'ₓ, mul_apply, h _ hx, hk]
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]

theorem disjoint_iff_disjoint_support : Disjoint f g ↔ _root_.disjoint f.support g.support := by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, Finset.ext_iff, not_and_distrib]

theorem disjoint.disjoint_support (h : Disjoint f g) : _root_.disjoint f.support g.support :=
  disjoint_iff_disjoint_support.1 h

theorem disjoint.support_mul (h : Disjoint f g) : (f*g).support = f.support ∪ g.support := by
  refine' le_antisymmₓ (support_mul_le _ _) fun a => _
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_distrib, not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_argₓ f hg).symm.trans h, hg⟩

theorem support_prod_of_pairwise_disjoint (l : List (perm α)) (h : l.pairwise Disjoint) :
    l.prod.support = (l.map support).foldr (·⊔·) ⊥ := by
  induction' l with hd tl hl
  ·
    simp
  ·
    rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.support_mul, hl h.right]

theorem support_prod_le (l : List (perm α)) : l.prod.support ≤ (l.map support).foldr (·⊔·) ⊥ := by
  induction' l with hd tl hl
  ·
    simp
  ·
    rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine' (support_mul_le hd tl.prod).trans _
    exact sup_le_sup (le_reflₓ _) hl

theorem support_zpow_le (σ : perm α) (n : ℤ) : (σ ^ n).support ≤ σ.support := fun x h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:57:31: expecting tactic arg
@[simp]
theorem support_swap {x y : α} (h : x ≠ y) : support (swap x y) = {x, y} := by
  ext z
  by_cases' hx : z = x
  any_goals {
  }
  by_cases' hy : z = y <;>
    ·
      simp [swap_apply_of_ne_of_ne, hx, hy] <;> cc

theorem support_swap_iff (x y : α) : support (swap x y) = {x, y} ↔ x ≠ y := by
  refine' ⟨fun h H => _, support_swap⟩
  subst H
  simp only [swap_self, support_refl, insert_singleton_self_eq] at h
  have : x ∈ ∅ := by
    rw [h]
    exact mem_singleton.mpr rfl
  simpa

theorem support_swap_mul_swap {x y z : α} (h : List.Nodupₓ [x, y, z]) : support (swap x y*swap y z) = {x, y, z} := by
  simp only [List.not_mem_nil, and_trueₓ, List.mem_cons_iff, not_false_iff, List.nodup_cons, List.mem_singleton,
    and_selfₓ, List.nodup_nil] at h
  push_neg  at h
  apply le_antisymmₓ
  ·
    convert support_mul_le _ _
    rw [support_swap h.left.left, support_swap h.right]
    ext
    simp [Or.comm, Or.left_comm]
  ·
    intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right, h.left.right.symm, h.right.symm]

theorem support_swap_mul_ge_support_diff (f : perm α) (x y : α) : f.support \ {x, y} ≤ (swap x y*f).support := by
  intro
  simp only [and_imp, perm.coe_mul, Function.comp_app, Ne.def, mem_support, mem_insert, mem_sdiff, mem_singleton]
  push_neg
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

theorem support_swap_mul_eq (f : perm α) (x : α) (h : f (f x) ≠ x) : (swap x (f x)*f).support = f.support \ {x} := by
  by_cases' hx : f x = x
  ·
    simp [hx, sdiff_singleton_eq_erase, not_mem_support.mpr hx, erase_eq_of_not_mem]
  ext z
  by_cases' hzx : z = x
  ·
    simp [hzx]
  by_cases' hzf : z = f x
  ·
    simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases' hzfx : f z = x
  ·
    simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  ·
    simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]

theorem mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y ∈ support (swap x (f x)*f)) : y ∈ support f ∧ y ≠ x :=
  by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  by_cases' h : f y = x
  ·
    constructor <;> intro <;> simp_all only [if_true, eq_self_iff_true, not_true, Ne.def]
  ·
    split_ifs  at hy <;> cc

theorem disjoint.mem_imp (h : Disjoint f g) {x : α} (hx : x ∈ f.support) : x ∉ g.support := fun H =>
  h.disjoint_support (mem_inter_of_mem hx H)

theorem eq_on_support_mem_disjoint {l : List (perm α)} (h : f ∈ l) (hl : l.pairwise Disjoint) :
    ∀, ∀ x ∈ f.support, ∀, f x = l.prod x := by
  induction' l with hd tl IH
  ·
    simpa using h
  ·
    intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons_iff] at h
    rcases h with (rfl | h)
    ·
      rw [List.prod_cons, mul_apply, not_mem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    ·
      rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← not_mem_support]
      refine' (hl.left _ h).symm.mem_imp _
      simpa using hx

theorem Disjoint.mono {x y : perm α} (h : Disjoint f g) (hf : x.support ≤ f.support) (hg : y.support ≤ g.support) :
    Disjoint x y := by
  rw [disjoint_iff_disjoint_support] at h⊢
  intro a ha
  exact h (mem_inter_of_mem (hf (mem_of_mem_inter_left ha)) (hg (mem_of_mem_inter_right ha)))

theorem support_le_prod_of_mem {l : List (perm α)} (h : f ∈ l) (hl : l.pairwise Disjoint) :
    f.support ≤ l.prod.support := by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]

section ExtendDomain

variable {β : Type _} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

@[simp]
theorem support_extend_domain (f : α ≃ Subtype p) {g : perm α} :
    support (g.extend_domain f) = g.support.map f.as_embedding := by
  ext b
  simp only [exists_prop, Function.Embedding.coe_fn_mk, to_embedding_apply, mem_map, Ne.def,
    Function.Embedding.trans_apply, mem_support]
  by_cases' pb : p b
  ·
    rw [extend_domain_apply_subtype _ _ pb]
    constructor
    ·
      rintro h
      refine'
        ⟨f.symm ⟨b, pb⟩, _, by
          simp ⟩
      contrapose! h
      simp [h]
    ·
      rintro ⟨a, ha, hb⟩
      contrapose! ha
      obtain rfl : a = f.symm ⟨b, pb⟩
      ·
        rw [eq_symm_apply]
        exact Subtype.coe_injective hb
      rw [eq_symm_apply]
      exact Subtype.coe_injective ha
  ·
    rw [extend_domain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iffₓ, not_and, eq_self_iff_true, not_true]
    rintro a ha rfl
    exact pb (Subtype.prop _)

theorem card_support_extend_domain (f : α ≃ Subtype p) {g : perm α} :
    (g.extend_domain f).support.card = g.support.card := by
  simp

end ExtendDomain

section Card

@[simp]
theorem card_support_eq_zero {f : perm α} : f.support.card = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, support_eq_empty_iff]

theorem one_lt_card_support_of_ne_one {f : perm α} (h : f ≠ 1) : 1 < f.support.card := by
  simp_rw [one_lt_card_iff, mem_support, ← not_or_distrib]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_selfₓ, or_selfₓ] at h

theorem card_support_ne_one (f : perm α) : f.support.card ≠ 1 := by
  by_cases' h : f = 1
  ·
    exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
  ·
    exact ne_of_gtₓ (one_lt_card_support_of_ne_one h)

@[simp]
theorem card_support_le_one {f : perm α} : f.support.card ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eqₓ, Nat.lt_succ_iffₓ, Nat.le_zero_iffₓ, card_support_eq_zero, or_iff_not_imp_right,
    imp_iff_right f.card_support_ne_one]

theorem two_le_card_support_of_ne_one {f : perm α} (h : f ≠ 1) : 2 ≤ f.support.card :=
  one_lt_card_support_of_ne_one h

theorem card_support_swap_mul {f : perm α} {x : α} (hx : f x ≠ x) : (swap x (f x)*f).support.card < f.support.card :=
  Finset.card_lt_card
    ⟨fun z hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx))
        (mt mem_support.1
          (by
            simp ))⟩

theorem card_support_swap {x y : α} (hxy : x ≠ y) : (swap x y).support.card = 2 :=
  show
    (swap x y).support.card =
      Finset.card
        ⟨x ::ₘ y ::ₘ 0, by
          simp [hxy]⟩ from
    congr_argₓ card $ by
      simp [support_swap hxy, Finset.ext_iff]

@[simp]
theorem card_support_eq_two {f : perm α} : f.support.card = 2 ↔ is_swap f := by
  constructor <;> intro h
  ·
    obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine' ⟨x, y, hmem, _⟩
    ext a
    have key : ∀ b, f b ≠ b ↔ _ := fun b => by
      rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases' ha : f a = a
    ·
      have ha' := not_or_distrib.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
    ·
      have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      ·
        rw [Or.resolve_left ha' ha, swap_apply_left]
      ·
        rw [Or.resolve_right ha' ha, swap_apply_right]
  ·
    obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy

theorem disjoint.card_support_mul (h : Disjoint f g) : (f*g).support.card = f.support.card+g.support.card := by
  rw [← Finset.card_disjoint_union]
  ·
    congr
    ext
    simp [h.support_mul]
  ·
    simpa using h.disjoint_support

theorem card_support_prod_list_of_pairwise_disjoint {l : List (perm α)} (h : l.pairwise Disjoint) :
    l.prod.support.card = (l.map (Finset.card ∘ support)).Sum := by
  induction' l with a t ih
  ·
    exact card_support_eq_zero.mpr rfl
  ·
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul

end Card

end Support

end Equivₓ.Perm

