import Mathbin.Data.List.Func 
import Mathbin.Tactic.Ring 
import Mathbin.Tactic.Omega.Misc

namespace Omega

namespace Coeffs

open List.Func

variable {v : Nat → Int}

/-- `val_between v as l o` is the value (under valuation `v`) of the term
    obtained taking the term represented by `(0, as)` and dropping all
    subterms that include variables outside the range `[l,l+o)` -/
@[simp]
def val_between (v : Nat → Int) (as : List Int) (l : Nat) : Nat → Int
| 0 => 0
| o+1 => val_between o+get (l+o) as*v (l+o)

@[simp]
theorem val_between_nil {l : Nat} : ∀ m, val_between v [] l m = 0
| 0 =>
  by 
    simp only [val_between]
| m+1 =>
  by 
    simp only [val_between_nil m, Omega.Coeffs.valBetween, get_nil, zero_addₓ, zero_mul, Int.default_eq_zero]

/-- Evaluation of the nonconstant component of a normalized linear arithmetic term. -/
def val (v : Nat → Int) (as : List Int) : Int :=
  val_between v as 0 as.length

@[simp]
theorem val_nil : val v [] = 0 :=
  rfl

-- error in Tactic.Omega.Coeffs: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem val_between_eq_of_le
{as : list int}
{l : nat} : ∀
m, «expr ≤ »(as.length, «expr + »(l, m)) → «expr = »(val_between v as l m, val_between v as l «expr - »(as.length, l))
| 0, h1 := by { rw [expr add_zero] ["at", ident h1],
  rw [expr tsub_eq_zero_iff_le.mpr h1] [] }
| «expr + »(m, 1), h1 := begin
  rw [expr le_iff_eq_or_lt] ["at", ident h1],
  cases [expr h1] [],
  { rw ["[", expr h1, ",", expr add_comm l, ",", expr add_tsub_cancel_right, "]"] [] },
  have [ident h2] [":", expr «expr ≤ »(list.length as, «expr + »(l, m))] [],
  { rw ["<-", expr nat.lt_succ_iff] [],
    apply [expr h1] },
  simpa [] [] [] ["[", expr get_eq_default_of_le _ h2, ",", expr zero_mul, ",", expr add_zero, ",", expr val_between, "]"] [] ["using", expr val_between_eq_of_le _ h2]
end

theorem val_eq_of_le {as : List Int} {k : Nat} : as.length ≤ k → val v as = val_between v as 0 k :=
  by 
    intro h1 
    unfold val 
    rw [val_between_eq_of_le k _]
    rfl 
    rw [zero_addₓ]
    exact h1

-- error in Tactic.Omega.Coeffs: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem val_between_eq_val_between
{v w : nat → int}
{as bs : list int}
{l : nat} : ∀
{m}, ∀
x, «expr ≤ »(l, x) → «expr < »(x, «expr + »(l, m)) → «expr = »(v x, w x) → ∀
x, «expr ≤ »(l, x) → «expr < »(x, «expr + »(l, m)) → «expr = »(get x as, get x bs) → «expr = »(val_between v as l m, val_between w bs l m)
| 0, h1, h2 := rfl
| «expr + »(m, 1), h1, h2 := begin
  unfold [ident val_between] [],
  have [ident h3] [":", expr «expr < »(«expr + »(l, m), «expr + »(l, «expr + »(m, 1)))] [],
  { rw ["<-", expr add_assoc] [],
    apply [expr lt_add_one] },
  apply [expr fun_mono_2],
  apply [expr val_between_eq_val_between]; intros [ident x, ident h4, ident h5],
  { apply [expr h1 _ h4 (lt_trans h5 h3)] },
  { apply [expr h2 _ h4 (lt_trans h5 h3)] },
  rw ["[", expr h1 _ _ h3, ",", expr h2 _ _ h3, "]"] []; apply [expr nat.le_add_right]
end

open_locale List.Func

-- error in Tactic.Omega.Coeffs: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem val_between_set
{a : int}
{l
 n : nat} : ∀
{m}, «expr ≤ »(l, n) → «expr < »(n, «expr + »(l, m)) → «expr = »(val_between v «expr { ↦ }»(«expr[ , ]»([]), n, a) l m, «expr * »(a, v n))
| 0, h1, h2 := begin
  exfalso,
  apply [expr lt_irrefl l (lt_of_le_of_lt h1 h2)]
end
| «expr + »(m, 1), h1, h2 := begin
  rw ["[", "<-", expr add_assoc, ",", expr nat.lt_succ_iff, ",", expr le_iff_eq_or_lt, "]"] ["at", ident h2],
  cases [expr h2] []; unfold [ident val_between] [],
  { have [ident h3] [":", expr «expr = »(val_between v «expr { ↦ }»(«expr[ , ]»([]), «expr + »(l, m), a) l m, 0)] [],
    { apply [expr @eq.trans _ _ (val_between v «expr[ , ]»([]) l m)],
      { apply [expr val_between_eq_val_between],
        { intros [],
          refl },
        { intros [ident x, ident h4, ident h5],
          rw ["[", expr get_nil, ",", expr get_set_eq_of_ne, ",", expr get_nil, "]"] [],
          apply [expr ne_of_lt h5] } },
      apply [expr val_between_nil] },
    rw [expr h2] [],
    simp [] [] ["only"] ["[", expr h3, ",", expr zero_add, ",", expr list.func.get_set, "]"] [] [] },
  { have [ident h3] [":", expr «expr ≠ »(«expr + »(l, m), n)] [],
    { apply [expr ne_of_gt h2] },
    rw ["[", expr @val_between_set m h1 h2, ",", expr get_set_eq_of_ne _ _ h3, "]"] [],
    simp [] [] ["only"] ["[", expr h3, ",", expr get_nil, ",", expr add_zero, ",", expr zero_mul, ",", expr int.default_eq_zero, "]"] [] [] }
end

@[simp]
theorem val_set {m : Nat} {a : Int} : val v ([] {m ↦ a}) = a*v m :=
  by 
    apply val_between_set 
    apply zero_le 
    apply lt_of_lt_of_leₓ (lt_add_one _)
    simp only [length_set, zero_addₓ, le_max_rightₓ]
    infer_instance

theorem val_between_neg {as : List Int} {l : Nat} : ∀ {o}, val_between v (neg as) l o = -val_between v as l o
| 0 => rfl
| o+1 =>
  by 
    unfold val_between 
    rw [neg_add, neg_mul_eq_neg_mul]
    apply fun_mono_2 
    apply val_between_neg 
    apply fun_mono_2 _ rfl 
    apply get_neg

@[simp]
theorem val_neg {as : List Int} : val v (neg as) = -val v as :=
  by 
    simpa only [val, length_neg] using val_between_neg

theorem val_between_add {is js : List Int} {l : Nat} :
  ∀ m, val_between v (add is js) l m = val_between v is l m+val_between v js l m
| 0 => rfl
| m+1 =>
  by 
    simp only [val_between, val_between_add m, List.Func.get, get_add]
    ring

@[simp]
theorem val_add {is js : List Int} : val v (add is js) = val v is+val v js :=
  by 
    unfold val 
    rw [val_between_add]
    apply fun_mono_2 <;> apply val_between_eq_of_le <;> rw [zero_addₓ, length_add]
    apply le_max_leftₓ 
    apply le_max_rightₓ

theorem val_between_sub {is js : List Int} {l : Nat} :
  ∀ m, val_between v (sub is js) l m = val_between v is l m - val_between v js l m
| 0 => rfl
| m+1 =>
  by 
    simp only [val_between, val_between_sub m, List.Func.get, get_sub]
    ring

@[simp]
theorem val_sub {is js : List Int} : val v (sub is js) = val v is - val v js :=
  by 
    unfold val 
    rw [val_between_sub]
    apply fun_mono_2 <;> apply val_between_eq_of_le <;> rw [zero_addₓ, length_sub]
    apply le_max_leftₓ 
    apply le_max_rightₓ

/-- `val_except k v as` is the value (under valuation `v`) of the term
    obtained taking the term represented by `(0, as)` and dropping the
    subterm that includes the `k`th variable. -/
def val_except (k : Nat) (v : Nat → Int) as :=
  val_between v as 0 k+val_between v as (k+1) (as.length - k+1)

theorem val_except_eq_val_except {k : Nat} {is js : List Int} {v w : Nat → Int} :
  (∀ x _ : x ≠ k, v x = w x) → (∀ x _ : x ≠ k, get x is = get x js) → val_except k v is = val_except k w js :=
  by 
    intro h1 h2 
    unfold val_except 
    apply fun_mono_2
    ·
      apply val_between_eq_val_between <;>
        intro x h3 h4 <;>
            [·
              apply h1,
            ·
              apply h2] <;>
          apply ne_of_ltₓ <;> rw [zero_addₓ] at h4 <;> apply h4
    ·
      repeat' 
        rw [←val_between_eq_of_le (max is.length js.length - k+1)]
      ·
        apply val_between_eq_val_between <;>
          intro x h3 h4 <;>
              [·
                apply h1,
              ·
                apply h2] <;>
            apply Ne.symm <;> apply ne_of_ltₓ <;> rw [Nat.lt_iff_add_one_le] <;> exact h3
      ·
        refine' le_transₓ (le_max_rightₓ _ _) le_add_tsub
      ·
        refine' le_transₓ (le_max_leftₓ _ _) le_add_tsub

open_locale Omega

theorem val_except_update_set {n : Nat} {as : List Int} {i j : Int} :
  val_except n (v ⟨n ↦ i⟩) (as {n ↦ j}) = val_except n v as :=
  by 
    apply val_except_eq_val_except update_eq_of_ne (get_set_eq_of_ne _)

theorem val_between_add_val_between {as : List Int} {l m : Nat} :
  ∀ {n}, (val_between v as l m+val_between v as (l+m) n) = val_between v as l (m+n)
| 0 =>
  by 
    simp only [val_between, add_zeroₓ]
| n+1 =>
  by 
    rw [←add_assocₓ]
    unfold val_between 
    rw [add_assocₓ]
    rw [←@val_between_add_val_between n]
    ring

-- error in Tactic.Omega.Coeffs: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem val_except_add_eq
(n : nat)
{as : list int} : «expr = »(«expr + »(val_except n v as, «expr * »(get n as, v n)), val v as) :=
begin
  unfold [ident val_except] [],
  unfold [ident val] [],
  cases [expr le_total «expr + »(n, 1) as.length] ["with", ident h1, ident h1],
  { have [ident h4] [] [":=", expr @val_between_add_val_between v as 0 «expr + »(n, 1) «expr - »(as.length, «expr + »(n, 1))],
    have [ident h5] [":", expr «expr = »(«expr + »(«expr + »(n, 1), «expr - »(as.length, «expr + »(n, 1))), as.length)] [],
    { rw ["[", expr add_comm, ",", expr tsub_add_cancel_of_le h1, "]"] [] },
    rw [expr h5] ["at", ident h4],
    apply [expr eq.trans _ h4],
    simp [] [] ["only"] ["[", expr val_between, ",", expr zero_add, "]"] [] [],
    ring [] },
  have [ident h2] [":", expr «expr = »(«expr - »(list.length as, «expr + »(n, 1)), 0)] [],
  { exact [expr tsub_eq_zero_iff_le.mpr h1] },
  have [ident h3] [":", expr «expr = »(val_between v as 0 (list.length as), val_between v as 0 «expr + »(n, 1))] [],
  { simpa [] [] ["only"] ["[", expr val, "]"] [] ["using", expr @val_eq_of_le v as «expr + »(n, 1) h1] },
  simp [] [] ["only"] ["[", expr add_zero, ",", expr val_between, ",", expr zero_add, ",", expr h2, ",", expr h3, "]"] [] []
end

@[simp]
theorem val_between_map_mul {i : Int} {as : List Int} {l : Nat} :
  ∀ {m}, val_between v (List.map ((·*·) i) as) l m = i*val_between v as l m
| 0 =>
  by 
    simp only [val_between, mul_zero, List.map]
| m+1 =>
  by 
    unfold val_between 
    rw [@val_between_map_mul m, mul_addₓ]
    apply fun_mono_2 rfl 
    byCases' h1 : (l+m) < as.length
    ·
      rw [get_map h1, mul_assocₓ]
    rw [not_ltₓ] at h1 
    rw [get_eq_default_of_le, get_eq_default_of_le] <;>
      try 
          simp  <;>
        apply h1

theorem forall_val_dvd_of_forall_mem_dvd {i : Int} {as : List Int} : (∀ x _ : x ∈ as, i ∣ x) → ∀ n, i ∣ get n as
| h1, n =>
  by 
    apply forall_val_of_forall_mem _ h1 
    apply dvd_zero

theorem dvd_val_between {i} {as : List Int} {l : Nat} : ∀ {m}, (∀ x _ : x ∈ as, i ∣ x) → i ∣ val_between v as l m
| 0, h1 => dvd_zero _
| m+1, h1 =>
  by 
    unfold val_between 
    apply dvd_add 
    apply dvd_val_between h1 
    apply dvd_mul_of_dvd_left 
    byCases' h2 : get (l+m) as = 0
    ·
      rw [h2]
      apply dvd_zero 
    apply h1 
    apply mem_get_of_ne_zero h2

theorem dvd_val {as : List Int} {i : Int} : (∀ x _ : x ∈ as, i ∣ x) → i ∣ val v as :=
  by 
    apply dvd_val_between

@[simp]
theorem val_between_map_div {as : List Int} {i : Int} {l : Nat} (h1 : ∀ x _ : x ∈ as, i ∣ x) :
  ∀ {m}, val_between v (List.map (fun x => x / i) as) l m = val_between v as l m / i
| 0 =>
  by 
    simp only [Int.zero_div, val_between, List.map]
| m+1 =>
  by 
    unfold val_between 
    rw [@val_between_map_div m, Int.add_div_of_dvd_right]
    apply fun_mono_2 rfl
    ·
      apply
        calc (get (l+m) (List.map (fun x : ℤ => x / i) as)*v (l+m)) = (get (l+m) as / i)*v (l+m) :=
          by 
            apply fun_mono_2 _ rfl 
            rw [get_map']
            apply Int.zero_div 
          _ = (get (l+m) as*v (l+m)) / i :=
          by 
            repeat' 
              rw [mul_commₓ _ (v (l+m))]
            rw [Int.mul_div_assoc]
            apply forall_val_dvd_of_forall_mem_dvd h1 
          
    apply dvd_mul_of_dvd_left 
    apply forall_val_dvd_of_forall_mem_dvd h1

@[simp]
theorem val_map_div {as : List Int} {i : Int} :
  (∀ x _ : x ∈ as, i ∣ x) → val v (List.map (fun x => x / i) as) = val v as / i :=
  by 
    intro h1 
    simpa only [val, List.length_map] using val_between_map_div h1

-- error in Tactic.Omega.Coeffs: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem val_between_eq_zero
{is : list int}
{l : nat} : ∀ {m}, ∀ x : int, «expr ∈ »(x, is) → «expr = »(x, 0) → «expr = »(val_between v is l m, 0)
| 0, h1 := rfl
| «expr + »(m, 1), h1 := begin
  have [ident h2] [] [":=", expr @forall_val_of_forall_mem _ _ is (λ x, «expr = »(x, 0)) rfl h1],
  simpa [] [] ["only"] ["[", expr val_between, ",", expr h2 «expr + »(l, m), ",", expr zero_mul, ",", expr add_zero, "]"] [] ["using", expr @val_between_eq_zero m h1]
end

theorem val_eq_zero {is : List Int} : (∀ x : Int, x ∈ is → x = 0) → val v is = 0 :=
  by 
    apply val_between_eq_zero

end Coeffs

end Omega

