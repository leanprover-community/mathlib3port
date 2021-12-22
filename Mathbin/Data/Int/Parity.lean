import Mathbin.Data.Nat.Parity

/-!
# Parity of integers

This file contains theorems about the `even` and `odd` predicates on the integers.

## Tags

even, odd
-/


namespace Int

variable {m n : ℤ}

@[simp]
theorem mod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]

@[local simp]
theorem mod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]

theorem even_iff : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨m, hm⟩ => by
    simp [hm], fun h =>
    ⟨n / 2,
      (mod_add_div n 2).symm.trans
        (by
          simp [h])⟩⟩

theorem odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ => by
    rw [hm, add_mod]
    norm_num, fun h =>
    ⟨n / 2,
      (mod_add_div n 2).symm.trans
        (by
          rw [h]
          abel)⟩⟩

theorem not_even_iff : ¬Even n ↔ n % 2 = 1 := by
  rw [even_iff, mod_two_ne_zero]

theorem not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by
  rw [odd_iff, mod_two_ne_one]

theorem even_iff_not_odd : Even n ↔ ¬Odd n := by
  rw [not_odd_iff, even_iff]

@[simp]
theorem odd_iff_not_even : Odd n ↔ ¬Even n := by
  rw [not_even_iff, odd_iff]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `is_compl_even_odd [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    (Term.app
     `IsCompl
     [(Set.«term{_|_}» "{" (Mathlib.ExtendedBinder.extBinder `n [":" (termℤ "ℤ")]) "|" (Term.app `Even [`n]) "}")
      (Set.«term{_|_}» "{" `n "|" (Term.app `Odd [`n]) "}")])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         []
         ["[" [(Tactic.simpLemma [] ["←"] `Set.compl_set_of) "," (Tactic.simpLemma [] [] `is_compl_compl)] "]"]
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
     [(group
       (Tactic.simp
        "simp"
        []
        []
        ["[" [(Tactic.simpLemma [] ["←"] `Set.compl_set_of) "," (Tactic.simpLemma [] [] `is_compl_compl)] "]"]
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
   []
   []
   ["[" [(Tactic.simpLemma [] ["←"] `Set.compl_set_of) "," (Tactic.simpLemma [] [] `is_compl_compl)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_compl_compl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.compl_set_of
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `IsCompl
   [(Set.«term{_|_}» "{" (Mathlib.ExtendedBinder.extBinder `n [":" (termℤ "ℤ")]) "|" (Term.app `Even [`n]) "}")
    (Set.«term{_|_}» "{" `n "|" (Term.app `Odd [`n]) "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `n "|" (Term.app `Odd [`n]) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Odd [`n])
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
  `Odd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
theorem is_compl_even_odd : IsCompl { n : ℤ | Even n } { n | Odd n } := by simp [ ← Set.compl_set_of , is_compl_compl ]

theorem even_or_odd (n : ℤ) : Even n ∨ Odd n :=
  Or.imp_rightₓ odd_iff_not_even.2 $ em $ Even n

theorem even_or_odd' (n : ℤ) : ∃ k, (n = 2*k) ∨ n = (2*k)+1 := by
  simpa only [exists_or_distrib, ← Odd, ← Even] using even_or_odd n

theorem even_xor_odd (n : ℤ) : Xorₓ (Even n) (Odd n) := by
  cases' even_or_odd n with h
  ·
    exact Or.inl ⟨h, even_iff_not_odd.mp h⟩
  ·
    exact Or.inr ⟨h, odd_iff_not_even.mp h⟩

theorem even_xor_odd' (n : ℤ) : ∃ k, Xorₓ (n = 2*k) (n = (2*k)+1) := by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> use k
  ·
    simpa only [Xorₓ, true_andₓ, eq_self_iff_true, not_true, or_falseₓ, and_falseₓ] using (succ_ne_self (2*k)).symm
  ·
    simp only [Xorₓ, add_right_eq_selfₓ, false_orₓ, eq_self_iff_true, not_true, not_false_iff, one_ne_zero, and_selfₓ]

@[simp]
theorem two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 :=
  not_even_iff

instance : DecidablePred (Even : ℤ → Prop) := fun n =>
  decidableOfDecidableOfIff
    (by
      infer_instance)
    even_iff.symm

instance decidable_pred_odd : DecidablePred (Odd : ℤ → Prop) := fun n =>
  decidableOfDecidableOfIff
    (by
      infer_instance)
    odd_iff_not_even.symm

@[simp]
theorem even_zero : Even (0 : ℤ) :=
  ⟨0, by
    decide⟩

@[simp]
theorem not_even_one : ¬Even (1 : ℤ) := by
  rw [even_iff] <;> norm_num

@[simp]
theorem even_bit0 (n : ℤ) : Even (bit0 n) :=
  ⟨n, by
    rw [bit0, two_mul]⟩

@[parity_simps]
theorem even_add : Even (m+n) ↔ (Even m ↔ Even n) := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;>
    cases' mod_two_eq_zero_or_one n with h₂ h₂ <;> simp [even_iff, h₁, h₂, Int.add_mod] <;> norm_num

theorem even.add_even (hm : Even m) (hn : Even n) : Even (m+n) :=
  even_add.2 $ iff_of_true hm hn

theorem even_add' : Even (m+n) ↔ (Odd m ↔ Odd n) := by
  rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]

theorem odd.add_odd (hm : Odd m) (hn : Odd n) : Even (m+n) :=
  even_add'.2 $ iff_of_true hm hn

@[simp]
theorem not_even_bit1 (n : ℤ) : ¬Even (bit1 n) := by
  simp' [bit1] with parity_simps

theorem two_not_dvd_two_mul_add_one (n : ℤ) : ¬2 ∣ (2*n)+1 := by
  convert not_even_bit1 n <;> exact two_mul n

@[parity_simps]
theorem even_sub : Even (m - n) ↔ (Even m ↔ Even n) := by
  simp' [sub_eq_add_neg] with parity_simps

theorem even.sub_even (hm : Even m) (hn : Even n) : Even (m - n) :=
  even_sub.2 $ iff_of_true hm hn

theorem even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub, even_iff_not_odd, even_iff_not_odd, not_iff_not]

theorem odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) :=
  even_sub'.2 $ iff_of_true hm hn

@[parity_simps]
theorem even_add_one : Even (n+1) ↔ ¬Even n := by
  simp [even_add]

@[parity_simps]
theorem even_mul : Even (m*n) ↔ Even m ∨ Even n := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;>
    cases' mod_two_eq_zero_or_one n with h₂ h₂ <;> simp [even_iff, h₁, h₂, Int.mul_mod] <;> norm_num

theorem odd_mul : Odd (m*n) ↔ Odd m ∧ Odd n := by
  simp' [not_or_distrib] with parity_simps

theorem even.mul_left (hm : Even m) (n : ℤ) : Even (m*n) :=
  even_mul.mpr $ Or.inl hm

theorem even.mul_right (m : ℤ) (hn : Even n) : Even (m*n) :=
  even_mul.mpr $ Or.inr hn

theorem odd.mul (hm : Odd m) (hn : Odd n) : Odd (m*n) :=
  odd_mul.mpr ⟨hm, hn⟩

theorem odd.of_mul_left (h : Odd (m*n)) : Odd m :=
  (odd_mul.mp h).1

theorem odd.of_mul_right (h : Odd (m*n)) : Odd n :=
  (odd_mul.mp h).2

@[parity_simps]
theorem even_pow {n : ℕ} : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction' n with n ih <;> simp [even_mul, pow_succₓ]
  tauto

theorem even_pow' {n : ℕ} (h : n ≠ 0) : Even (m ^ n) ↔ Even m :=
  even_pow.trans $ and_iff_left h

@[parity_simps]
theorem odd_add : Odd (m+n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]

theorem odd.add_even (hm : Odd m) (hn : Even n) : Odd (m+n) :=
  odd_add.2 $ iff_of_true hm hn

theorem odd_add' : Odd (m+n) ↔ (Odd n ↔ Even m) := by
  rw [add_commₓ, odd_add]

theorem even.add_odd (hm : Even m) (hn : Odd n) : Odd (m+n) :=
  odd_add'.2 $ iff_of_true hn hm

theorem ne_of_odd_add (h : Odd (m+n)) : m ≠ n := fun hnot => by
  simpa [hnot] with parity_simps using h

@[parity_simps]
theorem odd_sub : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_sub, not_iff, odd_iff_not_even]

theorem odd.sub_even (hm : Odd m) (hn : Even n) : Odd (m - n) :=
  odd_sub.2 $ iff_of_true hm hn

theorem odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by
  rw [odd_iff_not_even, even_sub, not_iff, not_iff_comm, odd_iff_not_even]

theorem even.sub_odd (hm : Even m) (hn : Odd n) : Odd (m - n) :=
  odd_sub'.2 $ iff_of_true hn hm

theorem even_mul_succ_self (n : ℤ) : Even (n*n+1) := by
  rw [even_mul]
  convert n.even_or_odd
  simp' with parity_simps

@[simp, norm_cast]
theorem even_coe_nat (n : ℕ) : Even (n : ℤ) ↔ Even n := by
  rw_mod_cast [even_iff, Nat.even_iff]

@[simp, norm_cast]
theorem odd_coe_nat (n : ℕ) : Odd (n : ℤ) ↔ Odd n := by
  rw [odd_iff_not_even, Nat.odd_iff_not_even, even_coe_nat]

@[simp]
theorem nat_abs_even : Even n.nat_abs ↔ Even n :=
  coe_nat_dvd_left.symm

@[simp]
theorem nat_abs_odd : Odd n.nat_abs ↔ Odd n := by
  rw [odd_iff_not_even, Nat.odd_iff_not_even, nat_abs_even]

theorem four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) : (4 ∣ a+b) ∨ 4 ∣ a - b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  obtain h | h := Int.even_or_odd (m+n)
  ·
    right
    rw [Int.even_add, ← Int.even_sub] at h
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 k
    rw [eq_add_of_sub_eq hk, mul_addₓ, add_assocₓ, add_sub_cancel, ← mul_assocₓ]
    norm_num
  ·
    left
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 (k+1)
    rw [eq_sub_of_add_eq hk, add_right_commₓ, ← add_sub, mul_addₓ, mul_sub, add_assocₓ, add_assocₓ, sub_add, add_assocₓ,
      ← sub_sub (2*n), sub_self, zero_sub, sub_neg_eq_add, ← mul_assocₓ, mul_addₓ]
    norm_num

example (m n : ℤ) (h : Even m) : ¬Even (n+3) ↔ Even (((m ^ 2)+m)+n) := by
  simp' [(by
      decide : ¬2 = 0)] with
    parity_simps

example : ¬Even (25394535 : ℤ) := by
  simp

end Int

