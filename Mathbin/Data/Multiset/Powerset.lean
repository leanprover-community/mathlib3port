import Mathbin.Data.Multiset.Basic

/-!
# The powerset of a multiset
-/


namespace Multiset

open List

variable{α : Type _}

/-! ### powerset -/


/-- A helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists_aux`), as multisets. -/
def powerset_aux (l : List α) : List (Multiset α) :=
  0 :: sublists_aux l fun x y => x :: y

theorem powerset_aux_eq_map_coe {l : List α} : powerset_aux l = (sublists l).map coeₓ :=
  by 
    simp [powerset_aux, sublists] <;>
      rw
          [←show
            (@sublists_aux₁ α (Multiset α) l fun x => [«expr↑ » x]) =
              sublists_aux l fun x => List.cons («expr↑ » x) from
            sublists_aux₁_eq_sublists_aux _ _,
          sublists_aux_cons_eq_sublists_aux₁, ←bind_ret_eq_map, sublists_aux₁_bind] <;>
        rfl

@[simp]
theorem mem_powerset_aux {l : List α} {s} : s ∈ powerset_aux l ↔ s ≤ «expr↑ » l :=
  Quotientₓ.induction_on s$
    by 
      simp [powerset_aux_eq_map_coe, subperm, And.comm]

/-- Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets. -/
def powerset_aux' (l : List α) : List (Multiset α) :=
  (sublists' l).map coeₓ

theorem powerset_aux_perm_powerset_aux' {l : List α} : powerset_aux l ~ powerset_aux' l :=
  by 
    rw [powerset_aux_eq_map_coe] <;> exact (sublists_perm_sublists' _).map _

@[simp]
theorem powerset_aux'_nil : powerset_aux' (@nil α) = [0] :=
  rfl

@[simp]
theorem powerset_aux'_cons (a : α) (l : List α) :
  powerset_aux' (a :: l) = powerset_aux' l ++ List.map (cons a) (powerset_aux' l) :=
  by 
    simp [powerset_aux'] <;> rfl

theorem powerset_aux'_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powerset_aux' l₁ ~ powerset_aux' l₂ :=
  by 
    induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂
    ·
      simp 
    ·
      simp 
      exact IH.append (IH.map _)
    ·
      simp 
      apply perm.append_left 
      rw [←append_assoc, ←append_assoc,
        (by 
          funext s <;> simp [cons_swap] :
        cons b ∘ cons a = cons a ∘ cons b)]
      exact perm_append_comm.append_right _
    ·
      exact IH₁.trans IH₂

theorem powerset_aux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powerset_aux l₁ ~ powerset_aux l₂ :=
  powerset_aux_perm_powerset_aux'.trans$ (powerset_aux'_perm p).trans powerset_aux_perm_powerset_aux'.symm

/-- The power set of a multiset. -/
def powerset (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powerset_aux l : Multiset (Multiset α))) fun l₁ l₂ h => Quot.sound (powerset_aux_perm h)

theorem powerset_coe (l : List α) : @powerset α l = ((sublists l).map coeₓ : List (Multiset α)) :=
  congr_argₓ coeₓ powerset_aux_eq_map_coe

@[simp]
theorem powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map coeₓ : List (Multiset α)) :=
  Quot.sound powerset_aux_perm_powerset_aux'

@[simp]
theorem powerset_zero : @powerset α 0 = {0} :=
  rfl

@[simp]
theorem powerset_cons (a : α) s : powerset (a ::ₘ s) = powerset s+map (cons a) (powerset s) :=
  Quotientₓ.induction_on s$
    fun l =>
      by 
        simp  <;> rfl

@[simp]
theorem mem_powerset {s t : Multiset α} : s ∈ powerset t ↔ s ≤ t :=
  Quotientₓ.induction_on₂ s t$
    by 
      simp [subperm, And.comm]

theorem map_single_le_powerset (s : Multiset α) : s.map singleton ≤ powerset s :=
  Quotientₓ.induction_on s$
    fun l =>
      by 
        simp only [powerset_coe, quot_mk_to_coe, coe_le, coe_map]
        show l.map (coeₓ ∘ List.ret) <+~ (sublists l).map coeₓ 
        rw [←List.map_mapₓ]
        exact ((map_ret_sublist_sublists _).map _).Subperm

@[simp]
theorem card_powerset (s : Multiset α) : card (powerset s) = 2 ^ card s :=
  Quotientₓ.induction_on s$
    by 
      simp 

theorem revzip_powerset_aux {l : List α} ⦃x⦄ (h : x ∈ revzip (powerset_aux l)) : (x.1+x.2) = «expr↑ » l :=
  by 
    rw [revzip, powerset_aux_eq_map_coe, ←map_reverse, zip_map, ←revzip] at h 
    simp  at h 
    rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
    exact Quot.sound (revzip_sublists _ _ _ h)

theorem revzip_powerset_aux' {l : List α} ⦃x⦄ (h : x ∈ revzip (powerset_aux' l)) : (x.1+x.2) = «expr↑ » l :=
  by 
    rw [revzip, powerset_aux', ←map_reverse, zip_map, ←revzip] at h 
    simp  at h 
    rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
    exact Quot.sound (revzip_sublists' _ _ _ h)

-- error in Data.Multiset.Powerset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem revzip_powerset_aux_lemma
[decidable_eq α]
(l : list α)
{l' : list (multiset α)}
(H : ∀
 {{x : «expr × »(_, _)}}, «expr ∈ »(x, revzip l') → «expr = »(«expr + »(x.1, x.2), «expr↑ »(l))) : «expr = »(revzip l', l'.map (λ
  x, (x, «expr - »(«expr↑ »(l), x)))) :=
begin
  have [] [":", expr forall₂ (λ
    (p : «expr × »(multiset α, multiset α))
    (s : multiset α), «expr = »(p, (s, «expr - »(«expr↑ »(l), s)))) (revzip l') ((revzip l').map prod.fst)] [],
  { rw [expr forall₂_map_right_iff] [],
    apply [expr forall₂_same],
    rintro ["⟨", ident s, ",", ident t, "⟩", ident h],
    dsimp [] [] [] [],
    rw ["[", "<-", expr H h, ",", expr add_tsub_cancel_left, "]"] [] },
  rw ["[", "<-", expr forall₂_eq_eq_eq, ",", expr forall₂_map_right_iff, "]"] [],
  simpa [] [] [] [] [] []
end

-- error in Data.Multiset.Powerset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem revzip_powerset_aux_perm_aux' {l : list α} : «expr ~ »(revzip (powerset_aux l), revzip (powerset_aux' l)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq α],
  rw ["[", expr revzip_powerset_aux_lemma l revzip_powerset_aux, ",", expr revzip_powerset_aux_lemma l revzip_powerset_aux', "]"] [],
  exact [expr powerset_aux_perm_powerset_aux'.map _]
end

-- error in Data.Multiset.Powerset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem revzip_powerset_aux_perm
{l₁ l₂ : list α}
(p : «expr ~ »(l₁, l₂)) : «expr ~ »(revzip (powerset_aux l₁), revzip (powerset_aux l₂)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq α],
  simp [] [] [] ["[", expr λ
   l : list α, revzip_powerset_aux_lemma l revzip_powerset_aux, ",", expr coe_eq_coe.2 p, "]"] [] [],
  exact [expr (powerset_aux_perm p).map _]
end

/-! ### powerset_len -/


/-- Helper function for `powerset_len`. Given a list `l`, `powerset_len_aux n l` is the list
of sublists of length `n`, as multisets. -/
def powerset_len_aux (n : ℕ) (l : List α) : List (Multiset α) :=
  sublists_len_aux n l coeₓ []

theorem powerset_len_aux_eq_map_coe {n} {l : List α} : powerset_len_aux n l = (sublists_len n l).map coeₓ :=
  by 
    rw [powerset_len_aux, sublists_len_aux_eq, append_nil]

@[simp]
theorem mem_powerset_len_aux {n} {l : List α} {s} : s ∈ powerset_len_aux n l ↔ s ≤ «expr↑ » l ∧ card s = n :=
  Quotientₓ.induction_on s$
    by 
      simp [powerset_len_aux_eq_map_coe, subperm] <;>
        exact
          fun l₁ =>
            ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
              fun ⟨⟨l₂, p, s⟩, e⟩ => ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩

@[simp]
theorem powerset_len_aux_zero (l : List α) : powerset_len_aux 0 l = [0] :=
  by 
    simp [powerset_len_aux_eq_map_coe]

@[simp]
theorem powerset_len_aux_nil (n : ℕ) : powerset_len_aux (n+1) (@nil α) = [] :=
  rfl

@[simp]
theorem powerset_len_aux_cons (n : ℕ) (a : α) (l : List α) :
  powerset_len_aux (n+1) (a :: l) = powerset_len_aux (n+1) l ++ List.map (cons a) (powerset_len_aux n l) :=
  by 
    simp [powerset_len_aux_eq_map_coe] <;> rfl

theorem powerset_len_aux_perm {n} {l₁ l₂ : List α} (p : l₁ ~ l₂) : powerset_len_aux n l₁ ~ powerset_len_aux n l₂ :=
  by 
    induction' n with n IHn generalizing l₁ l₂
    ·
      simp 
    induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂
    ·
      rfl
    ·
      simp 
      exact IH.append ((IHn p).map _)
    ·
      simp 
      apply perm.append_left 
      cases n
      ·
        simp 
        apply perm.swap 
      simp 
      rw [←append_assoc, ←append_assoc,
        (by 
          funext s <;> simp [cons_swap] :
        cons b ∘ cons a = cons a ∘ cons b)]
      exact perm_append_comm.append_right _
    ·
      exact IH₁.trans IH₂

/-- `powerset_len n s` is the multiset of all submultisets of `s` of length `n`. -/
def powerset_len (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powerset_len_aux n l : Multiset (Multiset α)))
    fun l₁ l₂ h => Quot.sound (powerset_len_aux_perm h)

theorem powerset_len_coe' n (l : List α) : @powerset_len α n l = powerset_len_aux n l :=
  rfl

theorem powerset_len_coe n (l : List α) : @powerset_len α n l = ((sublists_len n l).map coeₓ : List (Multiset α)) :=
  congr_argₓ coeₓ powerset_len_aux_eq_map_coe

@[simp]
theorem powerset_len_zero_left (s : Multiset α) : powerset_len 0 s = {0} :=
  Quotientₓ.induction_on s$
    fun l =>
      by 
        simp [powerset_len_coe'] <;> rfl

@[simp]
theorem powerset_len_zero_right (n : ℕ) : @powerset_len α (n+1) 0 = 0 :=
  rfl

@[simp]
theorem powerset_len_cons (n : ℕ) (a : α) s :
  powerset_len (n+1) (a ::ₘ s) = powerset_len (n+1) s+map (cons a) (powerset_len n s) :=
  Quotientₓ.induction_on s$
    fun l =>
      by 
        simp [powerset_len_coe'] <;> rfl

@[simp]
theorem mem_powerset_len {n : ℕ} {s t : Multiset α} : s ∈ powerset_len n t ↔ s ≤ t ∧ card s = n :=
  Quotientₓ.induction_on t$
    fun l =>
      by 
        simp [powerset_len_coe']

@[simp]
theorem card_powerset_len (n : ℕ) (s : Multiset α) : card (powerset_len n s) = Nat.choose (card s) n :=
  Quotientₓ.induction_on s$
    by 
      simp [powerset_len_coe]

theorem powerset_len_le_powerset (n : ℕ) (s : Multiset α) : powerset_len n s ≤ powerset s :=
  Quotientₓ.induction_on s$
    fun l =>
      by 
        simp [powerset_len_coe] <;> exact ((sublists_len_sublist_sublists' _ _).map _).Subperm

theorem powerset_len_mono (n : ℕ) {s t : Multiset α} (h : s ≤ t) : powerset_len n s ≤ powerset_len n t :=
  le_induction_on h$
    fun l₁ l₂ h =>
      by 
        simp [powerset_len_coe] <;> exact ((sublists_len_sublist_of_sublist _ h).map _).Subperm

end Multiset

