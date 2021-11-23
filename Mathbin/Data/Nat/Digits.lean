import Mathbin.Data.Int.Modeq 
import Mathbin.Data.List.Indexes 
import Mathbin.Tactic.IntervalCases 
import Mathbin.Tactic.Linarith.Default

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

A basic `norm_digits` tactic is also provided for proving goals of the form
`nat.digits a b = l` where `a` and `b` are numerals.
-/


namespace Nat

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux_0 : ℕ → List ℕ
| 0 => []
| n+1 => [n+1]

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux_1 (n : ℕ) : List ℕ :=
  List.repeat 1 n

/-- (Impl.) An auxiliary definition for `digits`, to help get the desired definitional unfolding. -/
def digits_aux (b : ℕ) (h : 2 ≤ b) : ℕ → List ℕ
| 0 => []
| n+1 =>
  have  : (n+1) / b < n+1 := Nat.div_lt_selfₓ (Nat.succ_posₓ _) h
  (n+1) % b :: digits_aux ((n+1) / b)

@[simp]
theorem digits_aux_zero (b : ℕ) (h : 2 ≤ b) : digits_aux b h 0 = [] :=
  by 
    rw [digits_aux]

theorem digits_aux_def (b : ℕ) (h : 2 ≤ b) (n : ℕ) (w : 0 < n) : digits_aux b h n = n % b :: digits_aux b h (n / b) :=
  by 
    cases n
    ·
      cases w
    ·
      rw [digits_aux]

/--
`digits b n` gives the digits, in little-endian order,
of a natural number `n` in a specified base `b`.

In any base, we have `of_digits b L = L.foldr (λ x y, x + b * y) 0`.
* For any `2 ≤ b`, we have `l < b` for any `l ∈ digits b n`,
  and the last digit is not zero.
  This uniquely specifies the behaviour of `digits b`.
* For `b = 1`, we define `digits 1 n = list.repeat 1 n`.
* For `b = 0`, we define `digits 0 n = [n]`, except `digits 0 0 = []`.

Note this differs from the existing `nat.to_digits` in core, which is used for printing numerals.
In particular, `nat.to_digits b 0 = [0]`, while `digits b 0 = []`.
-/
def digits : ℕ → ℕ → List ℕ
| 0 => digits_aux_0
| 1 => digits_aux_1
| b+2 =>
  digits_aux (b+2)
    (by 
      normNum)

@[simp]
theorem digits_zero (b : ℕ) : digits b 0 = [] :=
  by 
    rcases b with (_ | ⟨_ | ⟨_⟩⟩) <;> simp [digits, digits_aux_0, digits_aux_1]

@[simp]
theorem digits_zero_zero : digits 0 0 = [] :=
  rfl

@[simp]
theorem digits_zero_succ (n : ℕ) : digits 0 n.succ = [n+1] :=
  rfl

theorem digits_zero_succ' : ∀ {n : ℕ} w : 0 < n, digits 0 n = [n]
| 0, h =>
  absurd h
    (by 
      decide)
| n+1, _ => rfl

@[simp]
theorem digits_one (n : ℕ) : digits 1 n = List.repeat 1 n :=
  rfl

@[simp]
theorem digits_one_succ (n : ℕ) : digits 1 (n+1) = 1 :: digits 1 n :=
  rfl

@[simp]
theorem digits_add_two_add_one (b n : ℕ) : digits (b+2) (n+1) = ((n+1) % b+2) :: digits (b+2) ((n+1) / b+2) :=
  by 
    rw [digits, digits_aux_def]
    exact succ_pos n

theorem digits_def' : ∀ {b : ℕ} h : 2 ≤ b {n : ℕ} w : 0 < n, digits b n = n % b :: digits b (n / b)
| 0, h =>
  absurd h
    (by 
      decide)
| 1, h =>
  absurd h
    (by 
      decide)
| b+2, h => digits_aux_def _ _

@[simp]
theorem digits_of_lt (b x : ℕ) (w₁ : 0 < x) (w₂ : x < b) : digits b x = [x] :=
  by 
    cases b
    ·
      cases w₂
    ·
      cases b
      ·
        intervalCases x
      ·
        cases x
        ·
          cases w₁
        ·
          rw [digits_add_two_add_one, Nat.div_eq_of_ltₓ w₂, digits_zero, Nat.mod_eq_of_ltₓ w₂]

theorem digits_add (b : ℕ) (h : 2 ≤ b) (x y : ℕ) (w : x < b) (w' : 0 < x ∨ 0 < y) :
  digits b (x+b*y) = x :: digits b y :=
  by 
    cases b
    ·
      cases h
    ·
      cases b
      ·
        normNum  at h
      ·
        cases y
        ·
          normNum  at w' 
          simp [w, w']
        dsimp [digits]
        rw [digits_aux_def]
        ·
          congr
          ·
            simp [Nat.add_modₓ, Nat.mod_eq_of_ltₓ w]
          ·
            simp [mul_commₓ (b+2), Nat.add_mul_div_rightₓ, Nat.div_eq_of_ltₓ w]
        ·
          apply Nat.succ_posₓ

/--
`of_digits b L` takes a list `L` of natural numbers, and interprets them
as a number in semiring, as the little-endian digits in base `b`.
-/
def of_digits {α : Type _} [Semiringₓ α] (b : α) : List ℕ → α
| [] => 0
| h :: t => h+b*of_digits t

theorem of_digits_eq_foldr {α : Type _} [Semiringₓ α] (b : α) (L : List ℕ) :
  of_digits b L = L.foldr (fun x y => x+b*y) 0 :=
  by 
    induction' L with d L ih
    ·
      rfl
    ·
      dsimp [of_digits]
      rw [ih]

theorem of_digits_eq_sum_map_with_index_aux (b : ℕ) (l : List ℕ) :
  ((List.range l.length).zipWith ((fun i a : ℕ => a*b ^ i) ∘ succ) l).Sum =
    b*((List.range l.length).zipWith (fun i a => a*b ^ i) l).Sum :=
  by 
    suffices  :
      (List.range l.length).zipWith ((fun i a : ℕ => a*b ^ i) ∘ succ) l =
        (List.range l.length).zipWith (fun i a => b*a*b ^ i) l
    ·
      simp [this]
    congr 
    ext 
    simp [pow_succₓ]
    ring

theorem of_digits_eq_sum_map_with_index (b : ℕ) (L : List ℕ) :
  of_digits b L = (L.map_with_index fun i a => a*b ^ i).Sum :=
  by 
    rw [List.map_with_index_eq_enum_map, List.enum_eq_zip_range, List.map_uncurry_zip_eq_zip_with, of_digits_eq_foldr]
    induction' L with hd tl hl
    ·
      simp 
    ·
      simpa [List.range_succ_eq_map, List.zip_with_map_left, of_digits_eq_sum_map_with_index_aux] using Or.inl hl

@[simp]
theorem of_digits_singleton {b n : ℕ} : of_digits b [n] = n :=
  by 
    simp [of_digits]

@[simp]
theorem of_digits_one_cons {α : Type _} [Semiringₓ α] (h : ℕ) (L : List ℕ) :
  of_digits (1 : α) (h :: L) = h+of_digits 1 L :=
  by 
    simp [of_digits]

theorem of_digits_append {b : ℕ} {l1 l2 : List ℕ} :
  of_digits b (l1 ++ l2) = of_digits b l1+(b ^ l1.length)*of_digits b l2 :=
  by 
    induction' l1 with hd tl IH
    ·
      simp [of_digits]
    ·
      rw [of_digits, List.cons_append, of_digits, IH, List.length_cons, pow_succ'ₓ]
      ring

@[normCast]
theorem coe_of_digits (α : Type _) [Semiringₓ α] (b : ℕ) (L : List ℕ) :
  ((of_digits b L : ℕ) : α) = of_digits (b : α) L :=
  by 
    induction' L with d L ih
    ·
      rfl
    ·
      dsimp [of_digits]
      pushCast 
      rw [ih]

@[normCast]
theorem coe_int_of_digits (b : ℕ) (L : List ℕ) : ((of_digits b L : ℕ) : ℤ) = of_digits (b : ℤ) L :=
  by 
    induction' L with d L ih
    ·
      rfl
    ·
      dsimp [of_digits]
      pushCast 
      rw [ih]

theorem digits_zero_of_eq_zero {b : ℕ} (h : 1 ≤ b) {L : List ℕ} (w : of_digits b L = 0) : ∀ l _ : l ∈ L, l = 0 :=
  by 
    induction' L with d L ih
    ·
      intro l m 
      cases m
    ·
      intro l m 
      dsimp [of_digits]  at w 
      rcases m with ⟨rfl⟩
      ·
        convert Nat.eq_zero_of_add_eq_zero_right w 
        simp 
      ·
        exact ih ((Nat.mul_right_inj h).mp (Nat.eq_zero_of_add_eq_zero_left w)) _ m

theorem digits_of_digits (b : ℕ) (h : 2 ≤ b) (L : List ℕ) (w₁ : ∀ l _ : l ∈ L, l < b)
  (w₂ : ∀ h : L ≠ [], L.last h ≠ 0) : digits b (of_digits b L) = L :=
  by 
    induction' L with d L ih
    ·
      dsimp [of_digits]
      simp 
    ·
      dsimp [of_digits]
      replace w₂ :=
        w₂
          (by 
            simp )
      rw [digits_add b h]
      ·
        rw [ih]
        ·
          simp 
        ·
          intro l m 
          apply w₁ 
          exact List.mem_cons_of_memₓ _ m
        ·
          intro h
          ·
            rw [List.last_cons _ h] at w₂ 
            convert w₂
      ·
        convert w₁ d (List.mem_cons_selfₓ _ _)
        simp 
      ·
        byCases' h' : L = []
        ·
          rcases h' with rfl 
          simp  at w₂ 
          left 
          apply Nat.pos_of_ne_zeroₓ 
          convert w₂ 
          simp 
        ·
          right 
          apply Nat.pos_of_ne_zeroₓ 
          contrapose! w₂ 
          apply digits_zero_of_eq_zero _ w₂
          ·
            rw [List.last_cons _ h']
            exact List.last_mem h'
          ·
            exact le_of_ltₓ h

theorem of_digits_digits (b n : ℕ) : of_digits b (digits b n) = n :=
  by 
    cases' b with b
    ·
      cases' n with n
      ·
        rfl
      ·
        change of_digits 0 [n+1] = n+1
        dsimp [of_digits]
        simp 
    ·
      cases' b with b
      ·
        induction' n with n ih
        ·
          rfl
        ·
          simp only [ih, add_commₓ 1, of_digits_one_cons, Nat.cast_id, digits_one_succ]
      ·
        apply Nat.strong_induction_onₓ n _ 
        clear n 
        intro n h 
        cases n
        ·
          rw [digits_zero]
          rfl
        ·
          simp only [Nat.succ_eq_add_one, digits_add_two_add_one]
          dsimp [of_digits]
          rw [h _ (Nat.div_lt_self' n b)]
          rw [Nat.cast_id, Nat.mod_add_divₓ]

theorem of_digits_one (L : List ℕ) : of_digits 1 L = L.sum :=
  by 
    induction' L with d L ih
    ·
      rfl
    ·
      simp [of_digits, List.sum_cons, ih]

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `of_digits`.
-/


-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem digits_eq_nil_iff_eq_zero
{b n : exprℕ()} : «expr ↔ »(«expr = »(digits b n, «expr[ , ]»([])), «expr = »(n, 0)) :=
begin
  split,
  { intro [ident h],
    have [] [":", expr «expr = »(of_digits b (digits b n), of_digits b «expr[ , ]»([]))] [],
    by rw [expr h] [],
    convert [] [expr this] [],
    rw [expr of_digits_digits] [] },
  { rintro [ident rfl],
    simp [] [] [] [] [] [] }
end

theorem digits_ne_nil_iff_ne_zero {b n : ℕ} : digits b n ≠ [] ↔ n ≠ 0 :=
  not_congr digits_eq_nil_iff_eq_zero

private theorem digits_last_aux {b n : ℕ} (h : 2 ≤ b) (w : 0 < n) : digits b n = n % b :: digits b (n / b) :=
  by 
    rcases b with (_ | _ | b)
    ·
      finish
    ·
      normNum  at h 
    rcases n with (_ | n)
    ·
      normNum  at w 
    simp 

theorem digits_last {b m : ℕ} (h : 2 ≤ b) (hm : 0 < m) p q : (digits b m).last p = (digits b (m / b)).last q :=
  by 
    simp only [digits_last_aux h hm]
    rw [List.last_cons]

theorem digits.injective (b : ℕ) : Function.Injective b.digits :=
  Function.LeftInverse.injective (of_digits_digits b)

@[simp]
theorem digits_inj_iff {b n m : ℕ} : b.digits n = b.digits m ↔ n = m :=
  (digits.injective b).eq_iff

-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem last_digit_ne_zero
(b : exprℕ())
{m : exprℕ()}
(hm : «expr ≠ »(m, 0)) : «expr ≠ »((digits b m).last (digits_ne_nil_iff_ne_zero.mpr hm), 0) :=
begin
  rcases [expr b, "with", "_", "|", "_", "|", ident b],
  { cases [expr m] []; finish [] [] },
  { cases [expr m] [],
    { finish [] [] },
    simp_rw ["[", expr digits_one, ",", expr list.last_repeat_succ 1 m, "]"] [],
    norm_num [] [] },
  revert [ident hm],
  apply [expr nat.strong_induction_on m],
  intros [ident n, ident IH, ident hn],
  have [ident hnpos] [":", expr «expr < »(0, n)] [":=", expr nat.pos_of_ne_zero hn],
  by_cases [expr hnb, ":", expr «expr < »(n, «expr + »(b, 2))],
  { simp_rw ["[", expr digits_of_lt b.succ.succ n hnpos hnb, "]"] [],
    exact [expr pos_iff_ne_zero.mp hnpos] },
  { rw [expr digits_last (show «expr ≤ »(2, «expr + »(b, 2)), from exprdec_trivial()) hnpos] [],
    refine [expr IH _ (nat.div_lt_self hnpos exprdec_trivial()) _],
    { rw ["<-", expr pos_iff_ne_zero] [],
      exact [expr nat.div_pos (le_of_not_lt hnb) exprdec_trivial()] } }
end

/-- The digits in the base b+2 expansion of n are all less than b+2 -/
theorem digits_lt_base' {b m : ℕ} : ∀ {d}, d ∈ digits (b+2) m → d < b+2 :=
  by 
    apply Nat.strong_induction_onₓ m 
    intro n IH d hd 
    cases' n with n
    ·
      rw [digits_zero] at hd 
      cases hd 
    rw [digits_add_two_add_one] at hd 
    cases hd
    ·
      rw [hd]
      exact
        n.succ.mod_lt
          (by 
            linarith)
    ·
      exact
        IH _
          (Nat.div_lt_selfₓ (Nat.succ_posₓ _)
            (by 
              linarith))
          hd

/-- The digits in the base b expansion of n are all less than b, if b ≥ 2 -/
theorem digits_lt_base {b m d : ℕ} (hb : 2 ≤ b) (hd : d ∈ digits b m) : d < b :=
  by 
    rcases b with (_ | _ | b) <;>
      try 
        linarith 
    exact digits_lt_base' hd

-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- an n-digit number in base b + 2 is less than (b + 2)^n -/
theorem of_digits_lt_base_pow_length'
{b : exprℕ()}
{l : list exprℕ()}
(hl : ∀
 x «expr ∈ » l, «expr < »(x, «expr + »(b, 2))) : «expr < »(of_digits «expr + »(b, 2) l, «expr ^ »(«expr + »(b, 2), l.length)) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident IH] [],
  { simp [] [] [] ["[", expr of_digits, "]"] [] [] },
  { rw ["[", expr of_digits, ",", expr list.length_cons, ",", expr pow_succ, "]"] [],
    have [] [":", expr «expr ≤ »(«expr * »(«expr + »(of_digits «expr + »(b, 2) tl, 1), «expr + »(b, 2)), «expr * »(«expr ^ »(«expr + »(b, 2), tl.length), «expr + »(b, 2)))] [":=", expr mul_le_mul (IH (λ
       x hx, hl _ (list.mem_cons_of_mem _ hx))) (by refl) exprdec_trivial() (nat.zero_le _)],
    suffices [] [":", expr «expr < »(«expr↑ »(hd), «expr + »(b, 2))],
    { linarith [] [] [] },
    norm_cast [],
    exact [expr hl hd (list.mem_cons_self _ _)] }
end

/-- an n-digit number in base b is less than b^n if b ≥ 2 -/
theorem of_digits_lt_base_pow_length {b : ℕ} {l : List ℕ} (hb : 2 ≤ b) (hl : ∀ x _ : x ∈ l, x < b) :
  of_digits b l < b ^ l.length :=
  by 
    rcases b with (_ | _ | b) <;>
      try 
        linarith 
    exact of_digits_lt_base_pow_length' hl

/-- Any number m is less than (b+2)^(number of digits in the base b + 2 representation of m) -/
theorem lt_base_pow_length_digits' {b m : ℕ} : m < (b+2) ^ (digits (b+2) m).length :=
  by 
    convert of_digits_lt_base_pow_length' fun _ => digits_lt_base' 
    rw [of_digits_digits (b+2) m]

/-- Any number m is less than b^(number of digits in the base b representation of m) -/
theorem lt_base_pow_length_digits {b m : ℕ} (hb : 2 ≤ b) : m < b ^ (digits b m).length :=
  by 
    rcases b with (_ | _ | b) <;>
      try 
        linarith 
    exact lt_base_pow_length_digits'

theorem of_digits_digits_append_digits {b m n : ℕ} :
  of_digits b (digits b n ++ digits b m) = n+(b ^ (digits b n).length)*m :=
  by 
    rw [of_digits_append, of_digits_digits, of_digits_digits]

theorem digits_len_le_digits_len_succ (b n : ℕ) : (digits b n).length ≤ (digits b (n+1)).length :=
  by 
    cases b
    ·
      cases n <;> simp 
    ·
      cases b
      ·
        simp 
      ·
        apply Nat.strong_induction_onₓ n 
        clear n 
        intro n IH 
        cases n
        ·
          simp 
        ·
          rw [digits_add_two_add_one, digits_add_two_add_one]
          byCases' hdvd : b.succ.succ ∣ n.succ+1
          ·
            rw [Nat.succ_div_of_dvd hdvd, List.length_cons, List.length_cons, Nat.succ_le_succ_iff]
            apply IH 
            exact
              Nat.div_lt_selfₓ
                (by 
                  linarith)
                (by 
                  linarith)
          ·
            rw [Nat.succ_div_of_not_dvd hdvd]
            rfl

theorem le_digits_len_le (b n m : ℕ) (h : n ≤ m) : (digits b n).length ≤ (digits b m).length :=
  monotone_nat_of_le_succ (digits_len_le_digits_len_succ b) h

-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pow_length_le_mul_of_digits
{b : exprℕ()}
{l : list exprℕ()}
(hl : «expr ≠ »(l, «expr[ , ]»([])))
(hl2 : «expr ≠ »(l.last hl, 0)) : «expr ≤ »(«expr ^ »(«expr + »(b, 2), l.length), «expr * »(«expr + »(b, 2), of_digits «expr + »(b, 2) l)) :=
begin
  rw ["[", "<-", expr list.init_append_last hl, "]"] [],
  simp [] [] ["only"] ["[", expr list.length_append, ",", expr list.length, ",", expr zero_add, ",", expr list.length_init, ",", expr of_digits_append, ",", expr list.length_init, ",", expr of_digits_singleton, ",", expr add_comm «expr - »(l.length, 1), ",", expr pow_add, ",", expr pow_one, "]"] [] [],
  apply [expr nat.mul_le_mul_left],
  refine [expr le_trans _ (nat.le_add_left _ _)],
  have [] [":", expr «expr < »(0, l.last hl)] [],
  { rwa ["[", expr pos_iff_ne_zero, "]"] [] },
  convert [] [expr nat.mul_le_mul_left _ this] [],
  rw ["[", expr mul_one, "]"] []
end

-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Any non-zero natural number `m` is greater than
(b+2)^((number of digits in the base (b+2) representation of m) - 1)
-/
theorem base_pow_length_digits_le'
(b m : exprℕ())
(hm : «expr ≠ »(m, 0)) : «expr ≤ »(«expr ^ »(«expr + »(b, 2), (digits «expr + »(b, 2) m).length), «expr * »(«expr + »(b, 2), m)) :=
begin
  have [] [":", expr «expr ≠ »(digits «expr + »(b, 2) m, «expr[ , ]»([]))] [],
  from [expr digits_ne_nil_iff_ne_zero.mpr hm],
  convert [] [expr pow_length_le_mul_of_digits this (last_digit_ne_zero _ hm)] [],
  rwa [expr of_digits_digits] []
end

/--
Any non-zero natural number `m` is greater than
b^((number of digits in the base b representation of m) - 1)
-/
theorem base_pow_length_digits_le (b m : ℕ) (hb : 2 ≤ b) : m ≠ 0 → b ^ (digits b m).length ≤ b*m :=
  by 
    rcases b with (_ | _ | b) <;>
      try 
        linarith 
    exact base_pow_length_digits_le' b m

/-! ### Modular Arithmetic -/


theorem dvd_of_digits_sub_of_digits {α : Type _} [CommRingₓ α] {a b k : α} (h : k ∣ a - b) (L : List ℕ) :
  k ∣ of_digits a L - of_digits b L :=
  by 
    induction' L with d L ih
    ·
      change k ∣ 0 - 0
      simp 
    ·
      simp only [of_digits, add_sub_add_left_eq_sub]
      exact dvd_mul_sub_mul h ih

theorem of_digits_modeq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : List ℕ) :
  of_digits b L ≡ of_digits b' L [MOD k] :=
  by 
    induction' L with d L ih
    ·
      rfl
    ·
      dsimp [of_digits]
      dsimp [Nat.Modeq]  at *
      convLHS => rw [Nat.add_modₓ, Nat.mul_modₓ, h, ih]
      convRHS => rw [Nat.add_modₓ, Nat.mul_modₓ]

theorem of_digits_modeq (b k : ℕ) (L : List ℕ) : of_digits b L ≡ of_digits (b % k) L [MOD k] :=
  of_digits_modeq' b (b % k) k (b.mod_modeq k).symm L

theorem of_digits_mod (b k : ℕ) (L : List ℕ) : of_digits b L % k = of_digits (b % k) L % k :=
  of_digits_modeq b k L

theorem of_digits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : List ℕ) :
  of_digits b L ≡ of_digits b' L [ZMOD k] :=
  by 
    induction' L with d L ih
    ·
      rfl
    ·
      dsimp [of_digits]
      dsimp [Int.Modeq]  at *
      convLHS => rw [Int.add_mod, Int.mul_mod, h, ih]
      convRHS => rw [Int.add_mod, Int.mul_mod]

theorem of_digits_zmodeq (b : ℤ) (k : ℕ) (L : List ℕ) : of_digits b L ≡ of_digits (b % k) L [ZMOD k] :=
  of_digits_zmodeq' b (b % k) k (b.mod_modeq («expr↑ » k)).symm L

theorem of_digits_zmod (b : ℤ) (k : ℕ) (L : List ℕ) : of_digits b L % k = of_digits (b % k) L % k :=
  of_digits_zmodeq b k L

theorem modeq_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : n ≡ (digits b' n).Sum [MOD b] :=
  by 
    rw [←of_digits_one]
    conv  => congr skip rw [←of_digits_digits b' n]
    convert of_digits_modeq _ _ _ 
    exact h.symm

theorem modeq_three_digits_sum (n : ℕ) : n ≡ (digits 10 n).Sum [MOD 3] :=
  modeq_digits_sum 3 10
    (by 
      normNum)
    n

theorem modeq_nine_digits_sum (n : ℕ) : n ≡ (digits 10 n).Sum [MOD 9] :=
  modeq_digits_sum 9 10
    (by 
      normNum)
    n

theorem zmodeq_of_digits_digits (b b' : ℕ) (c : ℤ) (h : b' ≡ c [ZMOD b]) (n : ℕ) :
  n ≡ of_digits c (digits b' n) [ZMOD b] :=
  by 
    conv  => congr skip rw [←of_digits_digits b' n]
    rw [coe_int_of_digits]
    apply of_digits_zmodeq' _ _ _ h

theorem of_digits_neg_one : ∀ L : List ℕ, of_digits (-1 : ℤ) L = (L.map fun n : ℕ => (n : ℤ)).alternatingSum
| [] => rfl
| [n] =>
  by 
    simp [of_digits, List.alternatingSum]
| a :: b :: t =>
  by 
    simp only [of_digits, List.alternatingSum, List.map_consₓ, of_digits_neg_one t]
    pushCast 
    ring

-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem modeq_eleven_digits_sum
(n : exprℕ()) : «expr ≡ [ZMOD ]»(n, ((digits 10 n).map (λ n : exprℕ(), (n : exprℤ()))).alternating_sum, 11) :=
begin
  have [ident t] [] [":=", expr zmodeq_of_digits_digits 11 10 («expr- »(1) : exprℤ()) (by unfold [ident int.modeq] []; norm_num [] []) n],
  rwa [expr of_digits_neg_one] ["at", ident t]
end

/-! ## Divisibility  -/


theorem dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : b ∣ n ↔ b ∣ (digits b' n).Sum :=
  by 
    rw [←of_digits_one]
    convLHS => rw [←of_digits_digits b' n]
    rw [Nat.dvd_iff_mod_eq_zeroₓ, Nat.dvd_iff_mod_eq_zeroₓ, of_digits_mod, h]

/-- **Divisibility by 3 Rule** -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).Sum :=
  dvd_iff_dvd_digits_sum 3 10
    (by 
      normNum)
    n

theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (digits 10 n).Sum :=
  dvd_iff_dvd_digits_sum 9 10
    (by 
      normNum)
    n

theorem dvd_iff_dvd_of_digits (b b' : ℕ) (c : ℤ) (h : (b : ℤ) ∣ (b' : ℤ) - c) (n : ℕ) :
  b ∣ n ↔ (b : ℤ) ∣ of_digits c (digits b' n) :=
  by 
    rw [←Int.coe_nat_dvd]
    exact dvd_iff_dvd_of_dvd_sub (zmodeq_of_digits_digits b b' c (Int.modeq_iff_dvd.2 h).symm _).symm.Dvd

-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eleven_dvd_iff
(n : exprℕ()) : «expr ↔ »(«expr ∣ »(11, n), «expr ∣ »((11 : exprℤ()), ((digits 10 n).map (λ
    n : exprℕ(), (n : exprℤ()))).alternating_sum)) :=
begin
  have [ident t] [] [":=", expr dvd_iff_dvd_of_digits 11 10 («expr- »(1) : exprℤ()) (by norm_num [] []) n],
  rw [expr of_digits_neg_one] ["at", ident t],
  exact [expr t]
end

/-! ### `norm_digits` tactic -/


namespace NormDigits

-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem digits_succ
(b n m r l)
(e : «expr = »(«expr + »(r, «expr * »(b, m)), n))
(hr : «expr < »(r, b))
(h : «expr ∧ »(«expr = »(nat.digits b m, l), «expr ∧ »(«expr ≤ »(2, b), «expr < »(0, m)))) : «expr ∧ »(«expr = »(nat.digits b n, [«expr :: »/«expr :: »/«expr :: »](r, l)), «expr ∧ »(«expr ≤ »(2, b), «expr < »(0, n))) :=
begin
  rcases [expr h, "with", "⟨", ident h, ",", ident b2, ",", ident m0, "⟩"],
  have [ident b0] [":", expr «expr < »(0, b)] [":=", expr by linarith [] [] []],
  have [ident n0] [":", expr «expr < »(0, n)] [":=", expr by linarith [] [] ["[", expr mul_pos b0 m0, "]"]],
  refine [expr ⟨_, b2, n0⟩],
  obtain ["⟨", ident rfl, ",", ident rfl, "⟩", ":=", expr (nat.div_mod_unique b0).2 ⟨e, hr⟩],
  subst [expr h],
  exact [expr nat.digits_def' b2 n0]
end

-- error in Data.Nat.Digits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem digits_one
(b n)
(n0 : «expr < »(0, n))
(nb : «expr < »(n, b)) : «expr ∧ »(«expr = »(nat.digits b n, «expr[ , ]»([n])), «expr ∧ »(«expr ≤ »(2, b), «expr < »(0, n))) :=
begin
  have [ident b2] [":", expr «expr ≤ »(2, b)] [":=", expr by linarith [] [] []],
  refine [expr ⟨_, b2, n0⟩],
  rw ["[", expr nat.digits_def' b2 n0, ",", expr nat.mod_eq_of_lt nb, ",", expr (nat.div_eq_zero_iff (by linarith [] [] [] : «expr < »(0, b))).2 nb, ",", expr nat.digits_zero, "]"] []
end

open Tactic

/-- Helper function for the `norm_digits` tactic. -/
unsafe def eval_aux (eb : expr) (b : ℕ) : expr → ℕ → instance_cache → tactic (instance_cache × expr × expr)
| en, n, ic =>
  do 
    let m := n / b 
    let r := n % b 
    let (ic, er) ← ic.of_nat r 
    let (ic, pr) ← norm_num.prove_lt_nat ic er eb 
    if m = 0 then
        do 
          let (_, pn0) ← norm_num.prove_pos ic en 
          return (ic, quote.1 ([%%ₓen] : List Nat), quote.1 (digits_one (%%ₓeb) (%%ₓen) (%%ₓpn0) (%%ₓpr)))
      else
        do 
          let em ← expr.of_nat (quote.1 ℕ) m 
          let (_, pe) ← norm_num.derive (quote.1 ((%%ₓer)+(%%ₓeb)*%%ₓem : ℕ))
          let (ic, el, p) ← eval_aux em m ic 
          return
              (ic, quote.1 (@List.cons ℕ (%%ₓer) (%%ₓel)),
              quote.1 (digits_succ (%%ₓeb) (%%ₓen) (%%ₓem) (%%ₓer) (%%ₓel) (%%ₓpe) (%%ₓpr) (%%ₓp)))

/--
A tactic for normalizing expressions of the form `nat.digits a b = l` where
`a` and `b` are numerals.

```
example : nat.digits 10 123 = [3,2,1] := by norm_num
```
-/
@[normNum]
unsafe def eval : expr → tactic (expr × expr)
| quote.1 (Nat.digits (%%ₓeb) (%%ₓen)) =>
  do 
    let b ← expr.to_nat eb 
    let n ← expr.to_nat en 
    if n = 0 then return (quote.1 ([] : List ℕ), quote.1 (Nat.digits_zero (%%ₓeb))) else
        if b = 0 then
          do 
            let ic ← mk_instance_cache (quote.1 ℕ)
            let (_, pn0) ← norm_num.prove_pos ic en 
            return (quote.1 ([%%ₓen] : List ℕ), quote.1 (@Nat.digits_zero_succ' (%%ₓen) (%%ₓpn0)))
        else
          if b = 1 then
            do 
              let ic ← mk_instance_cache (quote.1 ℕ)
              let (_, pn0) ← norm_num.prove_pos ic en 
              let s ← simp_lemmas.add_simp simp_lemmas.mk `list.repeat 
              let (rhs, p2, _) ← simplify s [] (quote.1 (List.repeat 1 (%%ₓen)))
              let p ← mk_eq_trans (quote.1 (Nat.digits_one (%%ₓen))) p2 
              return (rhs, p)
          else
            do 
              let ic ← mk_instance_cache (quote.1 ℕ)
              let (_, l, p) ← eval_aux eb b en n ic 
              let p ← mk_app `` And.left [p]
              return (l, p)
| _ => failed

end NormDigits

end Nat

