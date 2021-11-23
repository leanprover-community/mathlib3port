import Mathbin.Data.Fin.VecNotation 
import Mathbin.Data.Equiv.Basic 
import Mathbin.Tactic.NormNum

/-!
# Equivalences for `fin n`
-/


universe u

variable{m n : ℕ}

/-- Equivalence between `fin 0` and `empty`. -/
def finZeroEquiv : Finₓ 0 ≃ Empty :=
  Equiv.equivEmpty _

/-- Equivalence between `fin 0` and `pempty`. -/
def finZeroEquiv' : Finₓ 0 ≃ Pempty.{u} :=
  Equiv.equivPempty _

/-- Equivalence between `fin 1` and `unit`. -/
def finOneEquiv : Finₓ 1 ≃ Unit :=
  equivPunitOfUnique

/-- Equivalence between `fin 2` and `bool`. -/
def finTwoEquiv : Finₓ 2 ≃ Bool :=
  ⟨@Finₓ.cases 1 (fun _ => Bool) ff fun _ => tt, fun b => cond b 1 0,
    by 
      refine' Finₓ.cases _ _
      ·
        normNum 
      refine' Finₓ.cases _ _
      ·
        normNum 
      exact fun i => finZeroElim i,
    by 
      rintro ⟨_ | _⟩
      ·
        rfl
      ·
        rw [←Finₓ.succ_zero_eq_one]
        rfl⟩

/-- `Π i : fin 2, α i` is equivalent to `α 0 × α 1`. See also `fin_two_arrow_equiv` for a
non-dependent version and `prod_equiv_pi_fin_two` for a version with inputs `α β : Type u`. -/
@[simps (config := { fullyApplied := ff })]
def piFinTwoEquiv (α : Finₓ 2 → Type u) : (∀ i, α i) ≃ α 0 × α 1 :=
  { toFun := fun f => (f 0, f 1), invFun := fun p => Finₓ.cons p.1$ Finₓ.cons p.2 finZeroElim,
    left_inv := fun f => funext$ Finₓ.forall_fin_two.2 ⟨rfl, rfl⟩, right_inv := fun ⟨x, y⟩ => rfl }

-- error in Data.Equiv.Fin: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fin.preimage_apply_01_prod
{α : fin 2 → Type u}
(s : set (α 0))
(t : set (α 1)) : «expr = »(«expr ⁻¹' »(λ
  f : ∀ i, α i, (f 0, f 1), s.prod t), set.pi set.univ «expr $ »(fin.cons s, fin.cons t fin.elim0)) :=
begin
  ext [] [ident f] [],
  have [] [":", expr «expr = »((fin.cons s (fin.cons t fin.elim0) : ∀ i, set (α i)) 1, t)] [":=", expr rfl],
  simp [] [] [] ["[", expr fin.forall_fin_two, ",", expr this, "]"] [] []
end

-- error in Data.Equiv.Fin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
theorem fin.preimage_apply_01_prod'
{α : Type u}
(s t : set α) : «expr = »(«expr ⁻¹' »(λ f : fin 2 → α, (f 0, f 1), s.prod t), set.pi set.univ «expr![ , ]»([s, t])) :=
fin.preimage_apply_01_prod s t

-- error in Data.Equiv.Fin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
/-- A product space `α × β` is equivalent to the space `Π i : fin 2, γ i`, where
`γ = fin.cons α (fin.cons β fin_zero_elim)`. See also `pi_fin_two_equiv` and
`fin_two_arrow_equiv`. -/
@[simps #[expr { fully_applied := ff }]]
def prod_equiv_pi_fin_two (α β : Type u) : «expr ≃ »(«expr × »(α, β), ∀ i : fin 2, «expr![ , ]»([α, β]) i) :=
(pi_fin_two_equiv (fin.cons α (fin.cons β fin_zero_elim))).symm

-- error in Data.Equiv.Fin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
/-- The space of functions `fin 2 → α` is equivalent to `α × α`. See also `pi_fin_two_equiv` and
`prod_equiv_pi_fin_two`. -/
@[simps #[expr { fully_applied := ff }]]
def fin_two_arrow_equiv (α : Type*) : «expr ≃ »(fin 2 → α, «expr × »(α, α)) :=
{ inv_fun := λ x, «expr![ , ]»([x.1, x.2]), ..pi_fin_two_equiv (λ _, α) }

/-- `Π i : fin 2, α i` is order equivalent to `α 0 × α 1`. See also `order_iso.fin_two_arrow_equiv`
for a non-dependent version. -/
def OrderIso.piFinTwoIso (α : Finₓ 2 → Type u) [∀ i, Preorderₓ (α i)] : (∀ i, α i) ≃o α 0 × α 1 :=
  { toEquiv := piFinTwoEquiv α, map_rel_iff' := fun f g => Iff.symm Finₓ.forall_fin_two }

/-- The space of functions `fin 2 → α` is order equivalent to `α × α`. See also
`order_iso.pi_fin_two_iso`. -/
def OrderIso.finTwoArrowIso (α : Type _) [Preorderₓ α] : (Finₓ 2 → α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }

/-- The 'identity' equivalence between `fin n` and `fin m` when `n = m`. -/
def finCongr {n m : ℕ} (h : n = m) : Finₓ n ≃ Finₓ m :=
  (Finₓ.cast h).toEquiv

@[simp]
theorem fin_congr_apply_mk {n m : ℕ} (h : n = m) (k : ℕ) (w : k < n) :
  finCongr h ⟨k, w⟩ =
    ⟨k,
      by 
        subst h 
        exact w⟩ :=
  rfl

@[simp]
theorem fin_congr_symm {n m : ℕ} (h : n = m) : (finCongr h).symm = finCongr h.symm :=
  rfl

@[simp]
theorem fin_congr_apply_coe {n m : ℕ} (h : n = m) (k : Finₓ n) : (finCongr h k : ℕ) = k :=
  by 
    cases k 
    rfl

theorem fin_congr_symm_apply_coe {n m : ℕ} (h : n = m) (k : Finₓ m) : ((finCongr h).symm k : ℕ) = k :=
  by 
    cases k 
    rfl

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `fin.pred_above` that produces `option (fin n)` instead of
mapping both `i.cast_succ` and `i.succ` to `i`. -/
def finSuccEquiv' {n : ℕ} (i : Finₓ (n+1)) : Finₓ (n+1) ≃ Option (Finₓ n) :=
  { toFun := i.insert_nth none some, invFun := fun x => x.cases_on' i (Finₓ.succAbove i),
    left_inv :=
      fun x =>
        Finₓ.succAboveCases i
          (by 
            simp )
          (fun j =>
            by 
              simp )
          x,
    right_inv :=
      fun x =>
        by 
          cases x <;> dsimp <;> simp  }

@[simp]
theorem fin_succ_equiv'_at {n : ℕ} (i : Finₓ (n+1)) : (finSuccEquiv' i) i = none :=
  by 
    simp [finSuccEquiv']

@[simp]
theorem fin_succ_equiv'_succ_above {n : ℕ} (i : Finₓ (n+1)) (j : Finₓ n) : finSuccEquiv' i (i.succ_above j) = some j :=
  @Finₓ.insert_nth_apply_succ_above n (fun _ => Option (Finₓ n)) i _ _ _

theorem fin_succ_equiv'_below {n : ℕ} {i : Finₓ (n+1)} {m : Finₓ n} (h : m.cast_succ < i) :
  (finSuccEquiv' i) m.cast_succ = some m :=
  by 
    rw [←Finₓ.succ_above_below _ _ h, fin_succ_equiv'_succ_above]

theorem fin_succ_equiv'_above {n : ℕ} {i : Finₓ (n+1)} {m : Finₓ n} (h : i ≤ m.cast_succ) :
  (finSuccEquiv' i) m.succ = some m :=
  by 
    rw [←Finₓ.succ_above_above _ _ h, fin_succ_equiv'_succ_above]

@[simp]
theorem fin_succ_equiv'_symm_none {n : ℕ} (i : Finₓ (n+1)) : (finSuccEquiv' i).symm none = i :=
  rfl

@[simp]
theorem fin_succ_equiv'_symm_some {n : ℕ} (i : Finₓ (n+1)) (j : Finₓ n) :
  (finSuccEquiv' i).symm (some j) = i.succ_above j :=
  rfl

theorem fin_succ_equiv'_symm_some_below {n : ℕ} {i : Finₓ (n+1)} {m : Finₓ n} (h : m.cast_succ < i) :
  (finSuccEquiv' i).symm (some m) = m.cast_succ :=
  Finₓ.succ_above_below i m h

theorem fin_succ_equiv'_symm_some_above {n : ℕ} {i : Finₓ (n+1)} {m : Finₓ n} (h : i ≤ m.cast_succ) :
  (finSuccEquiv' i).symm (some m) = m.succ :=
  Finₓ.succ_above_above i m h

theorem fin_succ_equiv'_symm_coe_below {n : ℕ} {i : Finₓ (n+1)} {m : Finₓ n} (h : m.cast_succ < i) :
  (finSuccEquiv' i).symm m = m.cast_succ :=
  fin_succ_equiv'_symm_some_below h

theorem fin_succ_equiv'_symm_coe_above {n : ℕ} {i : Finₓ (n+1)} {m : Finₓ n} (h : i ≤ m.cast_succ) :
  (finSuccEquiv' i).symm m = m.succ :=
  fin_succ_equiv'_symm_some_above h

/-- Equivalence between `fin (n + 1)` and `option (fin n)`.
This is a version of `fin.pred` that produces `option (fin n)` instead of
requiring a proof that the input is not `0`. -/
def finSuccEquiv (n : ℕ) : Finₓ (n+1) ≃ Option (Finₓ n) :=
  finSuccEquiv' 0

@[simp]
theorem fin_succ_equiv_zero {n : ℕ} : (finSuccEquiv n) 0 = none :=
  by 
    cases n <;> rfl

@[simp]
theorem fin_succ_equiv_succ {n : ℕ} (m : Finₓ n) : (finSuccEquiv n) m.succ = some m :=
  fin_succ_equiv'_above (Finₓ.zero_le _)

@[simp]
theorem fin_succ_equiv_symm_none {n : ℕ} : (finSuccEquiv n).symm none = 0 :=
  fin_succ_equiv'_symm_none _

@[simp]
theorem fin_succ_equiv_symm_some {n : ℕ} (m : Finₓ n) : (finSuccEquiv n).symm (some m) = m.succ :=
  congr_funₓ Finₓ.succ_above_zero m

@[simp]
theorem fin_succ_equiv_symm_coe {n : ℕ} (m : Finₓ n) : (finSuccEquiv n).symm m = m.succ :=
  fin_succ_equiv_symm_some m

/-- The equiv version of `fin.pred_above_zero`. -/
theorem fin_succ_equiv'_zero {n : ℕ} : finSuccEquiv' (0 : Finₓ (n+1)) = finSuccEquiv n :=
  rfl

/-- `equiv` between `fin (n + 1)` and `option (fin n)` sending `fin.last n` to `none` -/
def finSuccEquivLast {n : ℕ} : Finₓ (n+1) ≃ Option (Finₓ n) :=
  finSuccEquiv' (Finₓ.last n)

@[simp]
theorem fin_succ_equiv_last_cast_succ {n : ℕ} (i : Finₓ n) : finSuccEquivLast i.cast_succ = some i :=
  fin_succ_equiv'_below i.2

@[simp]
theorem fin_succ_equiv_last_last {n : ℕ} : finSuccEquivLast (Finₓ.last n) = none :=
  by 
    simp [finSuccEquivLast]

@[simp]
theorem fin_succ_equiv_last_symm_some {n : ℕ} (i : Finₓ n) : finSuccEquivLast.symm (some i) = i.cast_succ :=
  fin_succ_equiv'_symm_some_below i.2

@[simp]
theorem fin_succ_equiv_last_symm_coe {n : ℕ} (i : Finₓ n) : finSuccEquivLast.symm («expr↑ » i) = i.cast_succ :=
  fin_succ_equiv'_symm_some_below i.2

@[simp]
theorem fin_succ_equiv_last_symm_none {n : ℕ} : finSuccEquivLast.symm none = Finₓ.last n :=
  fin_succ_equiv'_symm_none _

/-- Equivalence between `fin m ⊕ fin n` and `fin (m + n)` -/
def finSumFinEquiv : Sum (Finₓ m) (Finₓ n) ≃ Finₓ (m+n) :=
  { toFun := Sum.elim (Finₓ.castAdd n) (Finₓ.natAdd m),
    invFun := fun i => @Finₓ.addCases m n (fun _ => Sum (Finₓ m) (Finₓ n)) Sum.inl Sum.inr i,
    left_inv :=
      fun x =>
        by 
          cases' x with y y <;> dsimp <;> simp ,
    right_inv :=
      fun x =>
        by 
          refine' Finₓ.addCases (fun i => _) (fun i => _) x <;> simp  }

@[simp]
theorem fin_sum_fin_equiv_apply_left (i : Finₓ m) : (finSumFinEquiv (Sum.inl i) : Finₓ (m+n)) = Finₓ.castAdd n i :=
  rfl

@[simp]
theorem fin_sum_fin_equiv_apply_right (i : Finₓ n) : (finSumFinEquiv (Sum.inr i) : Finₓ (m+n)) = Finₓ.natAdd m i :=
  rfl

@[simp]
theorem fin_sum_fin_equiv_symm_apply_cast_add (x : Finₓ m) : finSumFinEquiv.symm (Finₓ.castAdd n x) = Sum.inl x :=
  finSumFinEquiv.symm_apply_apply (Sum.inl x)

@[simp]
theorem fin_sum_fin_equiv_symm_apply_nat_add (x : Finₓ n) : finSumFinEquiv.symm (Finₓ.natAdd m x) = Sum.inr x :=
  finSumFinEquiv.symm_apply_apply (Sum.inr x)

/-- The equivalence between `fin (m + n)` and `fin (n + m)` which rotates by `n`. -/
def finAddFlip : Finₓ (m+n) ≃ Finₓ (n+m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv

@[simp]
theorem fin_add_flip_apply_cast_add (k : Finₓ m) (n : ℕ) : finAddFlip (Finₓ.castAdd n k) = Finₓ.natAdd n k :=
  by 
    simp [finAddFlip]

@[simp]
theorem fin_add_flip_apply_nat_add (k : Finₓ n) (m : ℕ) : finAddFlip (Finₓ.natAdd m k) = Finₓ.castAdd m k :=
  by 
    simp [finAddFlip]

@[simp]
theorem fin_add_flip_apply_mk_left {k : ℕ} (h : k < m) (hk : k < m+n := Nat.lt_add_rightₓ k m n h)
  (hnk : (n+k) < n+m := add_lt_add_left h n) : finAddFlip (⟨k, hk⟩ : Finₓ (m+n)) = ⟨n+k, hnk⟩ :=
  by 
    convert fin_add_flip_apply_cast_add ⟨k, h⟩ n

@[simp]
theorem fin_add_flip_apply_mk_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m+n) :
  finAddFlip (⟨k, h₂⟩ : Finₓ (m+n)) = ⟨k - m, tsub_le_self.trans_lt$ add_commₓ m n ▸ h₂⟩ :=
  by 
    convert fin_add_flip_apply_nat_add ⟨k - m, (tsub_lt_iff_right h₁).2 _⟩ m
    ·
      simp [add_tsub_cancel_of_le h₁]
    ·
      rwa [add_commₓ]

/-- Rotate `fin n` one step to the right. -/
def finRotate : ∀ n, Equiv.Perm (Finₓ n)
| 0 => Equiv.refl _
| n+1 => finAddFlip.trans (finCongr (add_commₓ _ _))

theorem fin_rotate_of_lt {k : ℕ} (h : k < n) :
  finRotate (n+1) ⟨k, lt_of_lt_of_leₓ h (Nat.le_succₓ _)⟩ = ⟨k+1, Nat.succ_lt_succₓ h⟩ :=
  by 
    dsimp [finRotate]
    simp [h, add_commₓ]

theorem fin_rotate_last' : finRotate (n+1) ⟨n, lt_add_one _⟩ = ⟨0, Nat.zero_lt_succₓ _⟩ :=
  by 
    dsimp [finRotate]
    rw [fin_add_flip_apply_mk_right]
    simp 

theorem fin_rotate_last : finRotate (n+1) (Finₓ.last _) = 0 :=
  fin_rotate_last'

-- error in Data.Equiv.Fin: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fin.snoc_eq_cons_rotate
{α : Type*}
(v : fin n → α)
(a : α) : «expr = »(@fin.snoc _ (λ _, α) v a, λ i, @fin.cons _ (λ _, α) a v (fin_rotate _ i)) :=
begin
  ext [] ["⟨", ident i, ",", ident h, "⟩"] [],
  by_cases [expr h', ":", expr «expr < »(i, n)],
  { rw ["[", expr fin_rotate_of_lt h', ",", expr fin.snoc, ",", expr fin.cons, ",", expr dif_pos h', "]"] [],
    refl },
  { have [ident h''] [":", expr «expr = »(n, i)] [],
    { simp [] [] ["only"] ["[", expr not_lt, "]"] [] ["at", ident h'],
      exact [expr (nat.eq_of_le_of_lt_succ h' h).symm] },
    subst [expr h''],
    rw ["[", expr fin_rotate_last', ",", expr fin.snoc, ",", expr fin.cons, ",", expr dif_neg (lt_irrefl _), "]"] [],
    refl }
end

@[simp]
theorem fin_rotate_zero : finRotate 0 = Equiv.refl _ :=
  rfl

@[simp]
theorem fin_rotate_one : finRotate 1 = Equiv.refl _ :=
  Subsingleton.elimₓ _ _

@[simp]
theorem fin_rotate_succ_apply {n : ℕ} (i : Finₓ n.succ) : finRotate n.succ i = i+1 :=
  by 
    cases n
    ·
      simp 
    rcases i.le_last.eq_or_lt with (rfl | h)
    ·
      simp [fin_rotate_last]
    ·
      cases i 
      simp only [Finₓ.lt_iff_coe_lt_coe, Finₓ.coe_last, Finₓ.coe_mk] at h 
      simp [fin_rotate_of_lt h, Finₓ.eq_iff_veq, Finₓ.add_def, Nat.mod_eq_of_ltₓ (Nat.succ_lt_succₓ h)]

@[simp]
theorem fin_rotate_apply_zero {n : ℕ} : finRotate n.succ 0 = 1 :=
  by 
    rw [fin_rotate_succ_apply, zero_addₓ]

-- error in Data.Equiv.Fin: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coe_fin_rotate_of_ne_last
{n : exprℕ()}
{i : fin n.succ}
(h : «expr ≠ »(i, fin.last n)) : «expr = »((fin_rotate n.succ i : exprℕ()), «expr + »(i, 1)) :=
begin
  rw [expr fin_rotate_succ_apply] [],
  have [] [":", expr «expr < »((i : exprℕ()), n)] [":=", expr lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (fin.coe_injective.ne h)],
  exact [expr fin.coe_add_one_of_lt this]
end

theorem coe_fin_rotate {n : ℕ} (i : Finₓ n.succ) : (finRotate n.succ i : ℕ) = if i = Finₓ.last n then 0 else i+1 :=
  by 
    rw [fin_rotate_succ_apply, Finₓ.coe_add_one i]

/-- Equivalence between `fin m × fin n` and `fin (m * n)` -/
@[simps]
def finProdFinEquiv : Finₓ m × Finₓ n ≃ Finₓ (m*n) :=
  { toFun :=
      fun x =>
        ⟨x.2+n*x.1,
          calc ((x.2.1+n*x.1.1)+1) = ((x.1.1*n)+x.2.1)+1 :=
            by 
              acRfl 
            _ ≤ (x.1.1*n)+n := Nat.add_le_add_leftₓ x.2.2 _ 
            _ = (x.1.1+1)*n := Eq.symm$ Nat.succ_mul _ _ 
            _ ≤ m*n := Nat.mul_le_mul_rightₓ _ x.1.2
            ⟩,
    invFun := fun x => (x.div_nat, x.mod_nat),
    left_inv :=
      fun ⟨x, y⟩ =>
        have H : 0 < n := Nat.pos_of_ne_zeroₓ$ fun H => Nat.not_lt_zeroₓ y.1$ H ▸ y.2
        Prod.extₓ
          (Finₓ.eq_of_veq$
            calc (y.1+n*x.1) / n = (y.1 / n)+x.1 := Nat.add_mul_div_leftₓ _ _ H 
              _ = 0+x.1 :=
              by 
                rw [Nat.div_eq_of_ltₓ y.2]
              _ = x.1 := Nat.zero_add x.1
              )
          (Finₓ.eq_of_veq$
            calc (y.1+n*x.1) % n = y.1 % n := Nat.add_mul_mod_self_leftₓ _ _ _ 
              _ = y.1 := Nat.mod_eq_of_ltₓ y.2
              ),
    right_inv := fun x => Finₓ.eq_of_veq$ Nat.mod_add_divₓ _ _ }

/-- Promote a `fin n` into a larger `fin m`, as a subtype where the underlying
values are retained. This is the `order_iso` version of `fin.cast_le`. -/
@[simps apply symmApply]
def Finₓ.castLeOrderIso {n m : ℕ} (h : n ≤ m) : Finₓ n ≃o { i : Finₓ m // (i : ℕ) < n } :=
  { toFun :=
      fun i =>
        ⟨Finₓ.castLe h i,
          by 
            simpa using i.is_lt⟩,
    invFun := fun i => ⟨i, i.prop⟩,
    left_inv :=
      fun _ =>
        by 
          simp ,
    right_inv :=
      fun _ =>
        by 
          simp ,
    map_rel_iff' :=
      fun _ _ =>
        by 
          simp  }

/-- `fin 0` is a subsingleton. -/
instance subsingleton_fin_zero : Subsingleton (Finₓ 0) :=
  finZeroEquiv.Subsingleton

/-- `fin 1` is a subsingleton. -/
instance subsingleton_fin_one : Subsingleton (Finₓ 1) :=
  finOneEquiv.Subsingleton

