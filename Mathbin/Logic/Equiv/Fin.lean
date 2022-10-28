/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Data.Fin.VecNotation
import Mathbin.Logic.Equiv.Defs

/-!
# Equivalences for `fin n`
-/


universe u

variable {m n : ℕ}

/-- Equivalence between `fin 0` and `empty`. -/
def finZeroEquiv : Fin 0 ≃ Empty :=
  Equiv.equivEmpty _

/-- Equivalence between `fin 0` and `pempty`. -/
def finZeroEquiv' : Fin 0 ≃ Pempty.{u} :=
  Equiv.equivPempty _

/-- Equivalence between `fin 1` and `unit`. -/
def finOneEquiv : Fin 1 ≃ Unit :=
  Equiv.equivPunit _

/-- Equivalence between `fin 2` and `bool`. -/
def finTwoEquiv : Fin 2 ≃ Bool where
  toFun := ![false, true]
  invFun b := cond b 1 0
  left_inv := Fin.forall_fin_two.2 <| by simp
  right_inv := Bool.forall_bool.2 <| by simp

/-- `Π i : fin 2, α i` is equivalent to `α 0 × α 1`. See also `fin_two_arrow_equiv` for a
non-dependent version and `prod_equiv_pi_fin_two` for a version with inputs `α β : Type u`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwoEquiv (α : Fin 2 → Type u) : (∀ i, α i) ≃ α 0 × α 1 where
  toFun f := (f 0, f 1)
  invFun p := Fin.cons p.1 <| Fin.cons p.2 finZeroElim
  left_inv f := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  right_inv := fun ⟨x, y⟩ => rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Fin.preimage_apply_01_prod {α : Fin 2 → Type u} (s : Set (α 0)) (t : Set (α 1)) :
    (fun f : ∀ i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.Pi Set.Univ (Fin.cons s <| Fin.cons t Fin.elim0) := by
  ext f
  have : (Fin.cons s (Fin.cons t Fin.elim0) : ∀ i, Set (α i)) 1 = t := rfl
  simp [Fin.forall_fin_two, this]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) :
    (fun f : Fin 2 → α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.Pi Set.Univ ![s, t] :=
  Fin.preimage_apply_01_prod s t

/-- A product space `α × β` is equivalent to the space `Π i : fin 2, γ i`, where
`γ = fin.cons α (fin.cons β fin_zero_elim)`. See also `pi_fin_two_equiv` and
`fin_two_arrow_equiv`. -/
@[simps (config := { fullyApplied := false })]
def prodEquivPiFinTwo (α β : Type u) : α × β ≃ ∀ i : Fin 2, ![α, β] i :=
  (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm

/-- The space of functions `fin 2 → α` is equivalent to `α × α`. See also `pi_fin_two_equiv` and
`prod_equiv_pi_fin_two`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrowEquiv (α : Type _) : (Fin 2 → α) ≃ α × α :=
  { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }

/-- `Π i : fin 2, α i` is order equivalent to `α 0 × α 1`. See also `order_iso.fin_two_arrow_equiv`
for a non-dependent version. -/
def OrderIso.piFinTwoIso (α : Fin 2 → Type u) [∀ i, Preorder (α i)] : (∀ i, α i) ≃o α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' f g := Iff.symm Fin.forall_fin_two

/-- The space of functions `fin 2 → α` is order equivalent to `α × α`. See also
`order_iso.pi_fin_two_iso`. -/
def OrderIso.finTwoArrowIso (α : Type _) [Preorder α] : (Fin 2 → α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }

/-- The 'identity' equivalence between `fin n` and `fin m` when `n = m`. -/
def finCongr {n m : ℕ} (h : n = m) : Fin n ≃ Fin m :=
  (Fin.cast h).toEquiv

@[simp]
theorem fin_congr_apply_mk {n m : ℕ} (h : n = m) (k : ℕ) (w : k < n) :
    finCongr h ⟨k, w⟩ =
      ⟨k, by
        subst h
        exact w⟩ :=
  rfl

@[simp]
theorem fin_congr_symm {n m : ℕ} (h : n = m) : (finCongr h).symm = finCongr h.symm :=
  rfl

@[simp]
theorem fin_congr_apply_coe {n m : ℕ} (h : n = m) (k : Fin n) : (finCongr h k : ℕ) = k := by
  cases k
  rfl

theorem fin_congr_symm_apply_coe {n m : ℕ} (h : n = m) (k : Fin m) : ((finCongr h).symm k : ℕ) = k := by
  cases k
  rfl

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `fin.pred_above` that produces `option (fin n)` instead of
mapping both `i.cast_succ` and `i.succ` to `i`. -/
def finSuccEquiv' {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n) where
  toFun := i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> dsimp <;> simp

@[simp]
theorem fin_succ_equiv'_at {n : ℕ} (i : Fin (n + 1)) : (finSuccEquiv' i) i = none := by simp [finSuccEquiv']

@[simp]
theorem fin_succ_equiv'_succ_above {n : ℕ} (i : Fin (n + 1)) (j : Fin n) : finSuccEquiv' i (i.succAbove j) = some j :=
  @Fin.insert_nth_apply_succ_above n (fun _ => Option (Fin n)) i _ _ _

theorem fin_succ_equiv'_below {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : m.cast_succ < i) :
    (finSuccEquiv' i) m.cast_succ = some m := by rw [← Fin.succ_above_below _ _ h, fin_succ_equiv'_succ_above]

theorem fin_succ_equiv'_above {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : i ≤ m.cast_succ) :
    (finSuccEquiv' i) m.succ = some m := by rw [← Fin.succ_above_above _ _ h, fin_succ_equiv'_succ_above]

@[simp]
theorem fin_succ_equiv'_symm_none {n : ℕ} (i : Fin (n + 1)) : (finSuccEquiv' i).symm none = i :=
  rfl

@[simp]
theorem fin_succ_equiv'_symm_some {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (finSuccEquiv' i).symm (some j) = i.succAbove j :=
  rfl

theorem fin_succ_equiv'_symm_some_below {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : m.cast_succ < i) :
    (finSuccEquiv' i).symm (some m) = m.cast_succ :=
  Fin.succ_above_below i m h

theorem fin_succ_equiv'_symm_some_above {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : i ≤ m.cast_succ) :
    (finSuccEquiv' i).symm (some m) = m.succ :=
  Fin.succ_above_above i m h

theorem fin_succ_equiv'_symm_coe_below {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : m.cast_succ < i) :
    (finSuccEquiv' i).symm m = m.cast_succ :=
  fin_succ_equiv'_symm_some_below h

theorem fin_succ_equiv'_symm_coe_above {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : i ≤ m.cast_succ) :
    (finSuccEquiv' i).symm m = m.succ :=
  fin_succ_equiv'_symm_some_above h

/-- Equivalence between `fin (n + 1)` and `option (fin n)`.
This is a version of `fin.pred` that produces `option (fin n)` instead of
requiring a proof that the input is not `0`. -/
def finSuccEquiv (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' 0

@[simp]
theorem fin_succ_equiv_zero {n : ℕ} : (finSuccEquiv n) 0 = none :=
  rfl

@[simp]
theorem fin_succ_equiv_succ {n : ℕ} (m : Fin n) : (finSuccEquiv n) m.succ = some m :=
  fin_succ_equiv'_above (Fin.zero_le _)

@[simp]
theorem fin_succ_equiv_symm_none {n : ℕ} : (finSuccEquiv n).symm none = 0 :=
  fin_succ_equiv'_symm_none _

@[simp]
theorem fin_succ_equiv_symm_some {n : ℕ} (m : Fin n) : (finSuccEquiv n).symm (some m) = m.succ :=
  congr_fun Fin.succ_above_zero m

@[simp]
theorem fin_succ_equiv_symm_coe {n : ℕ} (m : Fin n) : (finSuccEquiv n).symm m = m.succ :=
  fin_succ_equiv_symm_some m

/-- The equiv version of `fin.pred_above_zero`. -/
theorem fin_succ_equiv'_zero {n : ℕ} : finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n :=
  rfl

theorem fin_succ_equiv'_last_apply {n : ℕ} {i : Fin (n + 1)} (h : i ≠ Fin.last n) :
    finSuccEquiv' (Fin.last n) i =
      Fin.castLt i (lt_of_le_of_ne (Fin.le_last _) (Fin.coe_injective.ne_iff.2 h) : ↑i < n) :=
  by
  have h' : ↑i < n := lt_of_le_of_ne (Fin.le_last _) (fin.coe_injective.ne_iff.2 h)
  conv_lhs => rw [← Fin.cast_succ_cast_lt i h']
  convert fin_succ_equiv'_below _
  rw [Fin.cast_succ_cast_lt i h']
  exact h'

theorem fin_succ_equiv'_ne_last_apply {i j : Fin (n + 1)} (hi : i ≠ Fin.last n) (hj : j ≠ i) :
    finSuccEquiv' i j =
      (i.cast_lt (lt_of_le_of_ne (Fin.le_last _) (Fin.coe_injective.ne_iff.2 hi) : ↑i < n)).predAbove j :=
  by
  rw [Fin.predAbove]
  have hi' : ↑i < n := lt_of_le_of_ne (Fin.le_last _) (fin.coe_injective.ne_iff.2 hi)
  rcases hj.lt_or_lt with (hij | hij)
  · simp only [hij.not_lt, Fin.cast_succ_cast_lt, not_false_iff, dif_neg]
    convert fin_succ_equiv'_below _
    · simp
      
    · exact hij
      
    
  · simp only [hij, Fin.cast_succ_cast_lt, dif_pos]
    convert fin_succ_equiv'_above _
    · simp
      
    · simp [Fin.le_cast_succ_iff, hij]
      
    

/-- `succ_above` as an order isomorphism between `fin n` and `{x : fin (n + 1) // x ≠ p}`. -/
def finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x ≠ p } :=
  { Equiv.optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩ with map_rel_iff' := fun _ _ => p.succAbove.map_rel_iff' }

theorem fin_succ_above_equiv_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveEquiv p i = ⟨p.succAbove i, p.succ_above_ne i⟩ :=
  rfl

theorem fin_succ_above_equiv_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveEquiv (Fin.last n)).symm x =
      Fin.castLt (x : Fin (n + 1)) (lt_of_le_of_ne (Fin.le_last _) (Fin.coe_injective.ne_iff.2 x.property)) :=
  by
  rw [← Option.some_inj, ← Option.coe_def]
  simpa [finSuccAboveEquiv, OrderIso.symm] using fin_succ_equiv'_last_apply x.property

theorem fin_succ_above_equiv_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x =
      (p.cast_lt (lt_of_le_of_ne (Fin.le_last _) (Fin.coe_injective.ne_iff.2 h))).predAbove x :=
  by
  rw [← Option.some_inj, ← Option.coe_def]
  simpa [finSuccAboveEquiv, OrderIso.symm] using fin_succ_equiv'_ne_last_apply h x.property

/-- `equiv` between `fin (n + 1)` and `option (fin n)` sending `fin.last n` to `none` -/
def finSuccEquivLast {n : ℕ} : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' (Fin.last n)

@[simp]
theorem fin_succ_equiv_last_cast_succ {n : ℕ} (i : Fin n) : finSuccEquivLast i.cast_succ = some i :=
  fin_succ_equiv'_below i.2

@[simp]
theorem fin_succ_equiv_last_last {n : ℕ} : finSuccEquivLast (Fin.last n) = none := by simp [finSuccEquivLast]

@[simp]
theorem fin_succ_equiv_last_symm_some {n : ℕ} (i : Fin n) : finSuccEquivLast.symm (some i) = i.cast_succ :=
  fin_succ_equiv'_symm_some_below i.2

@[simp]
theorem fin_succ_equiv_last_symm_coe {n : ℕ} (i : Fin n) : finSuccEquivLast.symm ↑i = i.cast_succ :=
  fin_succ_equiv'_symm_some_below i.2

@[simp]
theorem fin_succ_equiv_last_symm_none {n : ℕ} : finSuccEquivLast.symm none = Fin.last n :=
  fin_succ_equiv'_symm_none _

/-- Equivalence between `Π j : fin (n + 1), α j` and `α i × Π j : fin n, α (fin.succ_above i j)`. -/
@[simps (config := { fullyApplied := false })]
def Equiv.piFinSuccAboveEquiv {n : ℕ} (α : Fin (n + 1) → Type u) (i : Fin (n + 1)) :
    (∀ j, α j) ≃ α i × ∀ j, α (i.succAbove j) where
  toFun f := (f i, fun j => f (i.succAbove j))
  invFun f := i.insertNth f.1 f.2
  left_inv f := by simp [Fin.insert_nth_eq_iff]
  right_inv f := by simp

/-- Order isomorphism between `Π j : fin (n + 1), α j` and
`α i × Π j : fin n, α (fin.succ_above i j)`. -/
def OrderIso.piFinSuccAboveIso {n : ℕ} (α : Fin (n + 1) → Type u) [∀ i, LE (α i)] (i : Fin (n + 1)) :
    (∀ j, α j) ≃o α i × ∀ j, α (i.succAbove j) where
  toEquiv := Equiv.piFinSuccAboveEquiv α i
  map_rel_iff' f g := i.forall_iff_succ_above.symm

/-- Equivalence between `fin (n + 1) → β` and `β × (fin n → β)`. -/
@[simps (config := { fullyApplied := false })]
def Equiv.piFinSucc (n : ℕ) (β : Type u) : (Fin (n + 1) → β) ≃ β × (Fin n → β) :=
  Equiv.piFinSuccAboveEquiv (fun _ => β) 0

/-- Equivalence between `fin m ⊕ fin n` and `fin (m + n)` -/
def finSumFinEquiv : Sum (Fin m) (Fin n) ≃ Fin (m + n) where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Sum (Fin m) (Fin n)) Sum.inl Sum.inr i
  left_inv x := by cases' x with y y <;> dsimp <;> simp
  right_inv x := by refine' Fin.addCases (fun i => _) (fun i => _) x <;> simp

@[simp]
theorem fin_sum_fin_equiv_apply_left (i : Fin m) : (finSumFinEquiv (Sum.inl i) : Fin (m + n)) = Fin.castAdd n i :=
  rfl

@[simp]
theorem fin_sum_fin_equiv_apply_right (i : Fin n) : (finSumFinEquiv (Sum.inr i) : Fin (m + n)) = Fin.natAdd m i :=
  rfl

@[simp]
theorem fin_sum_fin_equiv_symm_apply_cast_add (x : Fin m) : finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x :=
  finSumFinEquiv.symm_apply_apply (Sum.inl x)

@[simp]
theorem fin_sum_fin_equiv_symm_apply_nat_add (x : Fin n) : finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x :=
  finSumFinEquiv.symm_apply_apply (Sum.inr x)

@[simp]
theorem fin_sum_fin_equiv_symm_last : finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 :=
  fin_sum_fin_equiv_symm_apply_nat_add 0

/-- The equivalence between `fin (m + n)` and `fin (n + m)` which rotates by `n`. -/
def finAddFlip : Fin (m + n) ≃ Fin (n + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv

@[simp]
theorem fin_add_flip_apply_cast_add (k : Fin m) (n : ℕ) : finAddFlip (Fin.castAdd n k) = Fin.natAdd n k := by
  simp [finAddFlip]

@[simp]
theorem fin_add_flip_apply_nat_add (k : Fin n) (m : ℕ) : finAddFlip (Fin.natAdd m k) = Fin.castAdd m k := by
  simp [finAddFlip]

@[simp]
theorem fin_add_flip_apply_mk_left {k : ℕ} (h : k < m) (hk : k < m + n := Nat.lt_add_right k m n h)
    (hnk : n + k < n + m := add_lt_add_left h n) : finAddFlip (⟨k, hk⟩ : Fin (m + n)) = ⟨n + k, hnk⟩ := by
  convert fin_add_flip_apply_cast_add ⟨k, h⟩ n

@[simp]
theorem fin_add_flip_apply_mk_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m + n) :
    finAddFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, tsub_le_self.trans_lt <| add_comm m n ▸ h₂⟩ := by
  convert fin_add_flip_apply_nat_add ⟨k - m, (tsub_lt_iff_right h₁).2 _⟩ m
  · simp [add_tsub_cancel_of_le h₁]
    
  · rwa [add_comm]
    

/-- Rotate `fin n` one step to the right. -/
def finRotate : ∀ n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (add_comm _ _))

theorem fin_rotate_of_lt {k : ℕ} (h : k < n) :
    finRotate (n + 1) ⟨k, lt_of_lt_of_le h (Nat.le_succ _)⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩ := by
  dsimp [finRotate]
  simp [h, add_comm]

theorem fin_rotate_last' : finRotate (n + 1) ⟨n, lt_add_one _⟩ = ⟨0, Nat.zero_lt_succ _⟩ := by
  dsimp [finRotate]
  rw [fin_add_flip_apply_mk_right]
  simp

theorem fin_rotate_last : finRotate (n + 1) (Fin.last _) = 0 :=
  fin_rotate_last'

theorem Fin.snoc_eq_cons_rotate {α : Type _} (v : Fin n → α) (a : α) :
    @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α) a v (finRotate _ i) := by
  ext ⟨i, h⟩
  by_cases h':i < n
  · rw [fin_rotate_of_lt h', Fin.snoc, Fin.cons, dif_pos h']
    rfl
    
  · have h'' : n = i := by
      simp only [not_lt] at h'
      exact (Nat.eq_of_le_of_lt_succ h' h).symm
    subst h''
    rw [fin_rotate_last', Fin.snoc, Fin.cons, dif_neg (lt_irrefl _)]
    rfl
    

@[simp]
theorem fin_rotate_zero : finRotate 0 = Equiv.refl _ :=
  rfl

@[simp]
theorem fin_rotate_one : finRotate 1 = Equiv.refl _ :=
  Subsingleton.elim _ _

@[simp]
theorem fin_rotate_succ_apply {n : ℕ} (i : Fin n.succ) : finRotate n.succ i = i + 1 := by
  cases n
  · simp
    
  rcases i.le_last.eq_or_lt with (rfl | h)
  · simp [fin_rotate_last]
    
  · cases i
    simp only [Fin.lt_iff_coe_lt_coe, Fin.coe_last, Fin.coe_mk] at h
    simp [fin_rotate_of_lt h, Fin.eq_iff_veq, Fin.add_def, Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]
    

@[simp]
theorem fin_rotate_apply_zero {n : ℕ} : finRotate n.succ 0 = 1 := by rw [fin_rotate_succ_apply, zero_add]

theorem coe_fin_rotate_of_ne_last {n : ℕ} {i : Fin n.succ} (h : i ≠ Fin.last n) : (finRotate n.succ i : ℕ) = i + 1 := by
  rw [fin_rotate_succ_apply]
  have : (i : ℕ) < n := lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (fin.coe_injective.ne h)
  exact Fin.coe_add_one_of_lt this

theorem coe_fin_rotate {n : ℕ} (i : Fin n.succ) : (finRotate n.succ i : ℕ) = if i = Fin.last n then 0 else i + 1 := by
  rw [fin_rotate_succ_apply, Fin.coe_add_one i]

/-- Equivalence between `fin m × fin n` and `fin (m * n)` -/
@[simps]
def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n) where
  toFun x :=
    ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ ≤ x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
        _ = (x.1.1 + 1) * n := Eq.symm <| Nat.succ_mul _ _
        _ ≤ m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  left_inv := fun ⟨x, y⟩ =>
    have H : 0 < n := Nat.pos_of_ne_zero fun H => Nat.not_lt_zero y.1 <| H ▸ y.2
    Prod.ext
      (Fin.eq_of_veq <|
        calc
          (y.1 + n * x.1) / n = y.1 / n + x.1 := Nat.add_mul_div_left _ _ H
          _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
          _ = x.1 := Nat.zero_add x.1
          )
      (Fin.eq_of_veq <|
        calc
          (y.1 + n * x.1) % n = y.1 % n := Nat.add_mul_mod_self_left _ _ _
          _ = y.1 := Nat.mod_eq_of_lt y.2
          )
  right_inv x := Fin.eq_of_veq <| Nat.mod_add_div _ _

/-- Promote a `fin n` into a larger `fin m`, as a subtype where the underlying
values are retained. This is the `order_iso` version of `fin.cast_le`. -/
@[simps apply symmApply]
def Fin.castLeOrderIso {n m : ℕ} (h : n ≤ m) : Fin n ≃o { i : Fin m // (i : ℕ) < n } where
  toFun i := ⟨Fin.castLe h i, by simp⟩
  invFun i := ⟨i, i.Prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' _ _ := by simp

/-- `fin 0` is a subsingleton. -/
instance subsingleton_fin_zero : Subsingleton (Fin 0) :=
  finZeroEquiv.Subsingleton

/-- `fin 1` is a subsingleton. -/
instance subsingleton_fin_one : Subsingleton (Fin 1) :=
  finOneEquiv.Subsingleton

