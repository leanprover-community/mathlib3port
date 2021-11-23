import Mathbin.Data.Nat.Modeq 
import Mathbin.NumberTheory.Zsqrtd.Basic

/-!
# Pell's equation and Matiyasevic's theorem

This file solves Pell's equation, i.e. integer solutions to `x ^ 2 - d * y ^ 2 = 1` in the special
case that `d = a ^ 2 - 1`. This is then applied to prove Matiyasevic's theorem that the power
function is Diophantine, which is the last key ingredient in the solution to Hilbert's tenth
problem. For the definition of Diophantine function, see `dioph.lean`.

## Main definition

* `pell` is a function assigning to a natural number `n` the `n`-th solution to Pell's equation
  constructed recursively from the initial solution `(0, 1)`.

## Main statements

* `eq_pell` shows that every solution to Pell's equation is recursively obtained using `pell`
* `matiyasevic` shows that a certain system of Diophantine equations has a solution if and only if
  the first variable is the `x`-component in a solution to Pell's equation - the key step towards
  Hilbert's tenth problem in Davis' version of Matiyasevic's theorem.
* `eq_pow_of_pell` shows that the power function is Diophantine.

## Implementation notes

The proof of Matiyasevic's theorem doesn't follow Matiyasevic's original account of using Fibonacci
numbers but instead Davis' variant of using solutions to Pell's equation.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevič's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Pell's equation, Matiyasevic's theorem, Hilbert's tenth problem

## TODO

* Provide solutions to Pell's equation for the case of arbitrary `d` (not just `d = a ^ 2 - 1` like
  in the current version) and furthermore also for `x ^ 2 - d * y ^ 2 = -1`.
* Connect solutions to the continued fraction expansion of `√d`.
-/


namespace Pell

open Nat

section 

parameter {a : ℕ}(a1 : 1 < a)

include a1

private def d :=
  (a*a) - 1

@[simp]
theorem d_pos : 0 < d :=
  tsub_pos_of_lt
    (mul_lt_mul a1 (le_of_ltₓ a1)
      (by 
        decide)
      (by 
        decide) :
    (1*1) < a*a)

/-- The Pell sequences, i.e. the sequence of integer solutions to `x ^ 2 - d * y ^ 2 = 1`, where
`d = a ^ 2 - 1`, defined together in mutual recursion. -/
@[nolint dup_namespace]
def pell : ℕ → ℕ × ℕ :=
  fun n => Nat.recOn n (1, 0) fun n xy => ((xy.1*a)+d*xy.2, xy.1+xy.2*a)

/-- The Pell `x` sequence. -/
def xn (n : ℕ) : ℕ :=
  (pell n).1

/-- The Pell `y` sequence. -/
def yn (n : ℕ) : ℕ :=
  (pell n).2

@[simp]
theorem pell_val (n : ℕ) : pell n = (xn n, yn n) :=
  show pell n = ((pell n).1, (pell n).2) from
    match pell n with 
    | (a, b) => rfl

@[simp]
theorem xn_zero : xn 0 = 1 :=
  rfl

@[simp]
theorem yn_zero : yn 0 = 0 :=
  rfl

@[simp]
theorem xn_succ (n : ℕ) : xn (n+1) = (xn n*a)+d*yn n :=
  rfl

@[simp]
theorem yn_succ (n : ℕ) : yn (n+1) = xn n+yn n*a :=
  rfl

@[simp]
theorem xn_one : xn 1 = a :=
  by 
    simp 

@[simp]
theorem yn_one : yn 1 = 1 :=
  by 
    simp 

/-- The Pell `x` sequence, considered as an integer sequence.-/
def xz (n : ℕ) : ℤ :=
  xn n

/-- The Pell `y` sequence, considered as an integer sequence.-/
def yz (n : ℕ) : ℤ :=
  yn n

section 

omit a1

/-- The element `a` such that `d = a ^ 2 - 1`, considered as an integer.-/
def az : ℤ :=
  a

end 

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem asq_pos : «expr < »(0, «expr * »(a, a)) :=
le_trans (le_of_lt a1) (by have [] [] [":=", expr @nat.mul_le_mul_left 1 a a (le_of_lt a1)]; rwa [expr mul_one] ["at", ident this])

theorem dz_val : «expr↑ » d = (az*az) - 1 :=
  have  : 1 ≤ a*a := asq_pos 
  show «expr↑ » ((a*a) - 1) = _ by 
    rw [Int.coe_nat_subₓ this] <;> rfl

@[simp]
theorem xz_succ (n : ℕ) : xz (n+1) = (xz n*az)+«expr↑ » d*yz n :=
  rfl

@[simp]
theorem yz_succ (n : ℕ) : yz (n+1) = xz n+yz n*az :=
  rfl

/-- The Pell sequence can also be viewed as an element of `ℤ√d` -/
def pell_zd (n : ℕ) : ℤ√d :=
  ⟨xn n, yn n⟩

@[simp]
theorem pell_zd_re (n : ℕ) : (pell_zd n).re = xn n :=
  rfl

@[simp]
theorem pell_zd_im (n : ℕ) : (pell_zd n).im = yn n :=
  rfl

/-- The property of being a solution to the Pell equation, expressed
  as a property of elements of `ℤ√d`. -/
def is_pell : ℤ√d → Prop
| ⟨x, y⟩ => ((x*x) - (d*y)*y) = 1

theorem is_pell_nat {x y : ℕ} : is_pell ⟨x, y⟩ ↔ ((x*x) - (d*y)*y) = 1 :=
  ⟨fun h =>
      Int.coe_nat_inj
        (by 
          rw [Int.coe_nat_subₓ (Int.le_of_coe_nat_le_coe_nat$ Int.Le.intro_sub h)] <;> exact h),
    fun h =>
      show ((x*x : ℕ) - ((d*y)*y : ℕ) : ℤ) = 1by 
        rw [←Int.coe_nat_subₓ$ le_of_ltₓ$ Nat.lt_of_sub_eq_succₓ h, h] <;> rfl⟩

theorem is_pell_norm : ∀ {b : ℤ√d}, is_pell b ↔ (b*b.conj) = 1
| ⟨x, y⟩ =>
  by 
    simp [Zsqrtd.ext, is_pell, mul_commₓ] <;> ringNF

theorem is_pell_mul {b c : ℤ√d} (hb : is_pell b) (hc : is_pell c) : is_pell (b*c) :=
  is_pell_norm.2
    (by 
      simp [mul_commₓ, mul_left_commₓ, Zsqrtd.conj_mul, Pell.is_pell_norm.1 hb, Pell.is_pell_norm.1 hc])

theorem is_pell_conj : ∀ {b : ℤ√d}, is_pell b ↔ is_pell b.conj
| ⟨x, y⟩ =>
  by 
    simp [is_pell, Zsqrtd.conj]

@[simp]
theorem pell_zd_succ (n : ℕ) : pell_zd (n+1) = pell_zd n*⟨a, 1⟩ :=
  by 
    simp [Zsqrtd.ext]

theorem is_pell_one : is_pell ⟨a, 1⟩ :=
  show ((az*az) - (d*1)*1) = 1by 
    simp [dz_val] <;> ring

theorem is_pell_pell_zd : ∀ n : ℕ, is_pell (pell_zd n)
| 0 => rfl
| n+1 =>
  let o := is_pell_one 
  by 
    simp  <;> exact Pell.is_pell_mul (is_pell_pell_zd n) o

@[simp]
theorem pell_eqz (n : ℕ) : ((xz n*xz n) - (d*yz n)*yz n) = 1 :=
  is_pell_pell_zd n

@[simp]
theorem pell_eq (n : ℕ) : ((xn n*xn n) - (d*yn n)*yn n) = 1 :=
  let pn := pell_eqz n 
  have h : («expr↑ » (xn n*xn n) : ℤ) - «expr↑ » ((d*yn n)*yn n) = 1 :=
    by 
      repeat' 
          rw [Int.coe_nat_mul] <;>
        exact pn 
  have hl : ((d*yn n)*yn n) ≤ xn n*xn n := Int.le_of_coe_nat_le_coe_nat$ Int.Le.intro$ add_eq_of_eq_sub'$ Eq.symm h 
  Int.coe_nat_inj
    (by 
      rw [Int.coe_nat_subₓ hl] <;> exact h)

instance dnsq : Zsqrtd.Nonsquare d :=
  ⟨fun n h =>
      have  : ((n*n)+1) = a*a :=
        by 
          rw [←h] <;> exact Nat.succ_pred_eq_of_posₓ (asq_pos a1)
      have na : n < a :=
        Nat.mul_self_lt_mul_self_iff.2
          (by 
            rw [←this] <;> exact Nat.lt_succ_selfₓ _)
      have  : ((n+1)*n+1) ≤ (n*n)+1 :=
        by 
          rw [this] <;> exact Nat.mul_self_le_mul_self na 
      have  : (n+n) ≤ 0 :=
        @Nat.le_of_add_le_add_rightₓ ((n*n)+1) _ _
          (by 
            ringNF  at this⊢ <;> assumption)
      ne_of_gtₓ d_pos$
        by 
          rwa [Nat.eq_zero_of_le_zeroₓ ((Nat.le_add_leftₓ _ _).trans this)] at h⟩

theorem xn_ge_a_pow : ∀ n : ℕ, a ^ n ≤ xn n
| 0 => le_reflₓ 1
| n+1 =>
  by 
    simp [pow_succ'ₓ] <;> exact le_transₓ (Nat.mul_le_mul_rightₓ _ (xn_ge_a_pow n)) (Nat.le_add_rightₓ _ _)

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem n_lt_a_pow : ∀ n : exprℕ(), «expr < »(n, «expr ^ »(a, n))
| 0 := nat.le_refl 1
| «expr + »(n, 1) := begin
  have [ident IH] [] [":=", expr n_lt_a_pow n],
  have [] [":", expr «expr ≤ »(«expr + »(«expr ^ »(a, n), «expr ^ »(a, n)), «expr * »(«expr ^ »(a, n), a))] [],
  { rw ["<-", expr mul_two] [],
    exact [expr nat.mul_le_mul_left _ a1] },
  simp [] [] [] ["[", expr pow_succ', "]"] [] [],
  refine [expr lt_of_lt_of_le _ this],
  exact [expr add_lt_add_of_lt_of_le IH (lt_of_le_of_lt (nat.zero_le _) IH)]
end

theorem n_lt_xn n : n < xn n :=
  lt_of_lt_of_leₓ (n_lt_a_pow n) (xn_ge_a_pow n)

theorem x_pos n : 0 < xn n :=
  lt_of_le_of_ltₓ (Nat.zero_leₓ n) (n_lt_xn n)

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_pell_lem : ∀
(n)
(b : «exprℤ√ »(d)), «expr ≤ »(1, b) → is_pell b → «expr ≤ »(b, pell_zd n) → «expr∃ , »((n), «expr = »(b, pell_zd n))
| 0, b := λ h1 hp hl, ⟨0, @zsqrtd.le_antisymm _ dnsq _ _ hl h1⟩
| «expr + »(n, 1), b := λ h1 hp h, have a1p : «expr ≤ »((0 : «exprℤ√ »(d)), ⟨a, 1⟩), from trivial,
have am1p : «expr ≤ »((0 : «exprℤ√ »(d)), ⟨a, «expr- »(1)⟩), from show «expr ≤ »((_ : nat), _), by simp [] [] [] [] [] []; exact [expr nat.pred_le _],
have a1m : «expr = »((«expr * »(⟨a, 1⟩, ⟨a, «expr- »(1)⟩) : «exprℤ√ »(d)), 1), from is_pell_norm.1 is_pell_one,
if ha : «expr ≤ »((⟨«expr↑ »(a), 1⟩ : «exprℤ√ »(d)), b) then let ⟨m, e⟩ := eq_pell_lem n «expr * »(b, ⟨a, «expr- »(1)⟩) (by rw ["<-", expr a1m] []; exact [expr mul_le_mul_of_nonneg_right ha am1p]) (is_pell_mul hp (is_pell_conj.1 is_pell_one)) (by have [ident t] [] [":=", expr mul_le_mul_of_nonneg_right h am1p]; rwa ["[", expr pell_zd_succ, ",", expr mul_assoc, ",", expr a1m, ",", expr mul_one, "]"] ["at", ident t]) in
⟨«expr + »(m, 1), by rw ["[", expr show «expr = »(b, «expr * »(«expr * »(b, ⟨a, «expr- »(1)⟩), ⟨a, 1⟩)), by rw ["[", expr mul_assoc, ",", expr eq.trans (mul_comm _ _) a1m, "]"] []; simp [] [] [] [] [] [], ",", expr pell_zd_succ, ",", expr e, "]"] []⟩ else suffices «expr¬ »(«expr < »(1, b)), from ⟨0, show «expr = »(b, 1), from (or.resolve_left (lt_or_eq_of_le h1) this).symm⟩,
λ
h1l, by cases [expr b] ["with", ident x, ident y]; exact [expr have bm : «expr = »((«expr * »(_, ⟨_, _⟩) : «exprℤ√ »(d a1)), 1), from pell.is_pell_norm.1 hp,
 have y0l : «expr < »((0 : «exprℤ√ »(d a1)), ⟨«expr - »(x, x), «expr - »(y, «expr- »(y))⟩), from «expr $ »(sub_lt_sub h1l, λ
  hn : «expr ≤ »((1 : «exprℤ√ »(d a1)), ⟨x, «expr- »(y)⟩), by have [ident t] [] [":=", expr mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)]; rw ["[", expr bm, ",", expr mul_one, "]"] ["at", ident t]; exact [expr h1l t]),
 have yl2 : «expr < »((⟨_, _⟩ : «exprℤ√ »(_)), ⟨_, _⟩), from show «expr < »((«expr - »(⟨x, y⟩, ⟨x, «expr- »(y)⟩) : «exprℤ√ »(d a1)), «expr - »(⟨a, 1⟩, ⟨a, «expr- »(1)⟩)), from «expr $ »(sub_lt_sub (by exact [expr ha]), λ
  hn : «expr ≤ »((⟨x, «expr- »(y)⟩ : «exprℤ√ »(d a1)), ⟨a, «expr- »(1)⟩), by have [ident t] [] [":=", expr mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)) a1p]; rw ["[", expr bm, ",", expr one_mul, ",", expr mul_assoc, ",", expr eq.trans (mul_comm _ _) a1m, ",", expr mul_one, "]"] ["at", ident t]; exact [expr ha t]),
 by simp [] [] [] [] [] ["at", ident y0l]; simp [] [] [] [] [] ["at", ident yl2]; exact [expr match y, y0l, (yl2 : «expr < »((⟨_, _⟩ : «exprℤ√ »(_)), ⟨_, _⟩)) with
  | 0, y0l, yl2 := y0l (le_refl 0)
  | («expr + »(y, 1) : exprℕ()), y0l, yl2 := yl2 (zsqrtd.le_of_le_le (le_refl 0) (let t := int.coe_nat_le_coe_nat_of_le (nat.succ_pos y) in
    add_le_add t t))
  | «expr-[1+ ]»(y), y0l, yl2 := y0l trivial end]]

theorem eq_pell_zd (b : ℤ√d) (b1 : 1 ≤ b) (hp : is_pell b) : ∃ n, b = pell_zd n :=
  let ⟨n, h⟩ := @Zsqrtd.le_arch d b 
  eq_pell_lem n b b1 hp$
    Zsqrtd.le_trans h$
      by 
        rw [Zsqrtd.coe_nat_val] <;>
          exact Zsqrtd.le_of_le_le (Int.coe_nat_le_coe_nat_of_le$ le_of_ltₓ$ n_lt_xn _ _) (Int.coe_zero_le _)

/-- Every solution to **Pell's equation** is recursively obtained from the initial solution
`(1,0)` using the recursion `pell`. -/
theorem eq_pell {x y : ℕ} (hp : ((x*x) - (d*y)*y) = 1) : ∃ n, x = xn n ∧ y = yn n :=
  have  : (1 : ℤ√d) ≤ ⟨x, y⟩ :=
    match x, hp with 
    | 0, (hp : 0 - _ = 1) =>
      by 
        rw [zero_tsub] at hp <;> contradiction
    | x+1, hp => Zsqrtd.le_of_le_le (Int.coe_nat_le_coe_nat_of_le$ Nat.succ_posₓ x) (Int.coe_zero_le _)
  let ⟨m, e⟩ := eq_pell_zd ⟨x, y⟩ this (is_pell_nat.2 hp)
  ⟨m,
    match x, y, e with 
    | _, _, rfl => ⟨rfl, rfl⟩⟩

theorem pell_zd_add m : ∀ n, pell_zd (m+n) = pell_zd m*pell_zd n
| 0 => (mul_oneₓ _).symm
| n+1 =>
  by 
    rw [←add_assocₓ, pell_zd_succ, pell_zd_succ, pell_zd_add n, ←mul_assocₓ]

theorem xn_add m n : xn (m+n) = (xn m*xn n)+(d*yn m)*yn n :=
  by 
    injection pell_zd_add _ m n with h _ <;>
      repeat' 
          first |
            rw [←Int.coe_nat_add] at h|
            rw [←Int.coe_nat_mul] at h <;>
        exact Int.coe_nat_inj h

theorem yn_add m n : yn (m+n) = (xn m*yn n)+yn m*xn n :=
  by 
    injection pell_zd_add _ m n with _ h <;>
      repeat' 
          first |
            rw [←Int.coe_nat_add] at h|
            rw [←Int.coe_nat_mul] at h <;>
        exact Int.coe_nat_inj h

theorem pell_zd_sub {m n} (h : n ≤ m) : pell_zd (m - n) = pell_zd m*(pell_zd n).conj :=
  let t := pell_zd_add n (m - n)
  by 
    rw [add_tsub_cancel_of_le h] at t <;>
      rw [t, mul_commₓ (pell_zd _ n) _, mul_assocₓ, (is_pell_norm _).1 (is_pell_pell_zd _ _), mul_oneₓ]

theorem xz_sub {m n} (h : n ≤ m) : xz (m - n) = (xz m*xz n) - (d*yz m)*yz n :=
  by 
    injection pell_zd_sub _ h with h _ <;>
      repeat' 
          rw [←neg_mul_eq_mul_neg] at h <;>
        exact h

theorem yz_sub {m n} (h : n ≤ m) : yz (m - n) = (xz n*yz m) - xz m*yz n :=
  by 
    injection pell_zd_sub a1 h with _ h <;>
      repeat' 
          rw [←neg_mul_eq_mul_neg] at h <;>
        rw [add_commₓ, mul_commₓ] at h <;> exact h

theorem xy_coprime n : (xn n).Coprime (yn n) :=
  Nat.coprime_of_dvd'$
    fun k kp kx ky =>
      let p := pell_eq n 
      by 
        rw [←p] <;> exact Nat.dvd_subₓ (le_of_ltₓ$ Nat.lt_of_sub_eq_succₓ p) (kx.mul_left _) (ky.mul_left _)

theorem strict_mono_y : StrictMono yn
| m, 0, h => absurd h$ Nat.not_lt_zeroₓ _
| m, n+1, h =>
  have  : yn m ≤ yn n :=
    Or.elim (lt_or_eq_of_leₓ$ Nat.le_of_succ_le_succₓ h) (fun hl => le_of_ltₓ$ strict_mono_y hl)
      fun e =>
        by 
          rw [e]
  by 
    simp  <;>
      refine' lt_of_le_of_ltₓ _ (Nat.lt_add_of_pos_leftₓ$ x_pos a1 n) <;>
        rw [←mul_oneₓ (yn a1 m)] <;> exact mul_le_mul this (le_of_ltₓ a1) (Nat.zero_leₓ _) (Nat.zero_leₓ _)

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem strict_mono_x : strict_mono xn
| m, 0, h := «expr $ »(absurd h, nat.not_lt_zero _)
| m, «expr + »(n, 1), h := have «expr ≤ »(xn m, xn n), from or.elim «expr $ »(lt_or_eq_of_le, nat.le_of_succ_le_succ h) (λ
 hl, «expr $ »(le_of_lt, strict_mono_x hl)) (λ e, by rw [expr e] []),
by simp [] [] [] [] [] []; refine [expr lt_of_lt_of_le (lt_of_le_of_lt this _) (nat.le_add_right _ _)]; have [ident t] [] [":=", expr nat.mul_lt_mul_of_pos_left a1 (x_pos a1 n)]; rwa [expr mul_one] ["at", ident t]

theorem yn_ge_n : ∀ n, n ≤ yn n
| 0 => Nat.zero_leₓ _
| n+1 => show n < yn (n+1) from lt_of_le_of_ltₓ (yn_ge_n n) (strict_mono_y$ Nat.lt_succ_selfₓ n)

theorem y_mul_dvd n : ∀ k, yn n ∣ yn (n*k)
| 0 => dvd_zero _
| k+1 =>
  by 
    rw [Nat.mul_succ, yn_add] <;> exact dvd_add (dvd_mul_left _ _) ((y_mul_dvd k).mul_right _)

theorem y_dvd_iff m n : yn m ∣ yn n ↔ m ∣ n :=
  ⟨fun h =>
      Nat.dvd_of_mod_eq_zeroₓ$
        (Nat.eq_zero_or_posₓ _).resolve_right$
          fun hp =>
            have co : Nat.Coprime (yn m) (xn (m*n / m)) :=
              Nat.Coprime.symm$ (xy_coprime _).coprime_dvd_right (y_mul_dvd m (n / m))
            have m0 : 0 < m :=
              m.eq_zero_or_pos.resolve_left$
                fun e =>
                  by 
                    rw [e, Nat.mod_zeroₓ] at hp <;>
                      rw [e] at h <;> exact ne_of_ltₓ (strict_mono_y a1 hp) (eq_zero_of_zero_dvd h).symm 
            by 
              rw [←Nat.mod_add_divₓ n m, yn_add] at h <;>
                exact
                  not_le_of_gtₓ (strict_mono_y _$ Nat.mod_ltₓ n m0)
                    (Nat.le_of_dvdₓ (strict_mono_y _ hp)$
                      co.dvd_of_dvd_mul_right$ (Nat.dvd_add_iff_right$ (y_mul_dvd _ _ _).mul_left _).2 h),
    fun ⟨k, e⟩ =>
      by 
        rw [e] <;> apply y_mul_dvd⟩

theorem xy_modeq_yn n : ∀ k, xn (n*k) ≡ xn n ^ k [MOD yn n ^ 2] ∧ yn (n*k) ≡ (k*xn n ^ (k - 1))*yn n [MOD yn n ^ 3]
| 0 =>
  by 
    constructor <;> simp 
| k+1 =>
  let ⟨hx, hy⟩ := xy_modeq_yn k 
  have L : ((xn (n*k)*xn n)+(d*yn (n*k))*yn n) ≡ ((xn n ^ k)*xn n)+0 [MOD yn n ^ 2] :=
    (hx.mul_right _).add$
      modeq_zero_iff_dvd.2$
        by 
          rw [pow_succ'ₓ] <;>
            exact
              mul_dvd_mul_right
                (dvd_mul_of_dvd_right
                  (modeq_zero_iff_dvd.1$
                    (hy.modeq_of_dvd$
                          by 
                            simp [pow_succ'ₓ]).trans$
                      modeq_zero_iff_dvd.2$
                        by 
                          simp [-mul_commₓ, -mul_assocₓ])
                  _)
                _ 
  have R : ((xn (n*k)*yn n)+yn (n*k)*xn n) ≡ ((xn n ^ k)*yn n)+(k*xn n ^ k)*yn n [MOD yn n ^ 3] :=
    modeq.add
        (by 
          rw [pow_succ'ₓ]
          exact hx.mul_right' _)$
      have  : (((k*xn n ^ (k - 1))*yn n)*xn n) = (k*xn n ^ k)*yn n :=
        by 
          clear _let_match <;> cases' k with k <;> simp [pow_succ'ₓ, mul_commₓ, mul_left_commₓ]
      by 
        rw [←this]
        exact hy.mul_right _ 
  by 
    rw [add_tsub_cancel_right, Nat.mul_succ, xn_add, yn_add, pow_succ'ₓ (xn _ n), Nat.succ_mul,
      add_commₓ (k*xn _ n ^ k) (xn _ n ^ k), right_distrib]
    exact ⟨L, R⟩

theorem ysq_dvd_yy n : (yn n*yn n) ∣ yn (n*yn n) :=
  modeq_zero_iff_dvd.1$
    ((xy_modeq_yn n (yn n)).right.modeq_of_dvd$
          by 
            simp [pow_succₓ]).trans
      (modeq_zero_iff_dvd.2$
        by 
          simp [mul_dvd_mul_left, mul_assocₓ])

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dvd_of_ysq_dvd {n t} (h : «expr ∣ »(«expr * »(yn n, yn n), yn t)) : «expr ∣ »(yn n, t) :=
have nt : «expr ∣ »(n, t), from «expr $ »((y_dvd_iff n t).1, dvd_of_mul_left_dvd h),
«expr $ »(n.eq_zero_or_pos.elim (λ
  n0, by rwa [expr n0] ["at", "⊢", ident nt]), λ n0l : «expr < »(0, n), let ⟨k, ke⟩ := nt in
 have «expr ∣ »(yn n, «expr * »(k, «expr ^ »(xn n, «expr - »(k, 1)))), from «expr $ »(nat.dvd_of_mul_dvd_mul_right (strict_mono_y n0l), «expr $ »(modeq_zero_iff_dvd.1, by have [ident xm] [] [":=", expr (xy_modeq_yn a1 n k).right]; rw ["<-", expr ke] ["at", ident xm]; exact [expr «expr $ »(xm.modeq_of_dvd, by simp [] [] [] ["[", expr pow_succ, "]"] [] []).symm.trans h.modeq_zero_nat])),
 by rw [expr ke] []; exact [expr dvd_mul_of_dvd_right (((xy_coprime _ _).pow_left _).symm.dvd_of_dvd_mul_right this) _])

theorem pell_zd_succ_succ n : (pell_zd (n+2)+pell_zd n) = (2*a : ℕ)*pell_zd (n+1) :=
  have  : ((1 : ℤ√d)+⟨a, 1⟩*⟨a, 1⟩) = ⟨a, 1⟩*2*a :=
    by 
      rw [Zsqrtd.coe_nat_val]
      change (⟨_, _⟩ : ℤ√d a1) = ⟨_, _⟩
      rw [dz_val]
      dsimp [az]
      rw [Zsqrtd.ext]
      dsimp 
      split  <;> ring 
  by 
    simpa [mul_addₓ, mul_commₓ, mul_left_commₓ, add_commₓ] using congr_argₓ (·*pell_zd a1 n) this

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem xy_succ_succ
(n) : «expr ∧ »(«expr = »(«expr + »(xn «expr + »(n, 2), xn n), «expr * »(«expr * »(2, a), xn «expr + »(n, 1))), «expr = »(«expr + »(yn «expr + »(n, 2), yn n), «expr * »(«expr * »(2, a), yn «expr + »(n, 1)))) :=
begin
  have [] [] [":=", expr pell_zd_succ_succ a1 n],
  unfold [ident pell_zd] ["at", ident this],
  rw ["[", "<-", expr int.cast_coe_nat, ",", expr zsqrtd.smul_val, "]"] ["at", ident this],
  injection [expr this] ["with", ident h₁, ident h₂],
  split; apply [expr int.coe_nat_inj]; [simpa [] [] [] [] [] ["using", expr h₁], simpa [] [] [] [] [] ["using", expr h₂]]
end

theorem xn_succ_succ n : (xn (n+2)+xn n) = (2*a)*xn (n+1) :=
  (xy_succ_succ n).1

theorem yn_succ_succ n : (yn (n+2)+yn n) = (2*a)*yn (n+1) :=
  (xy_succ_succ n).2

theorem xz_succ_succ n : xz (n+2) = ((2*a : ℕ)*xz (n+1)) - xz n :=
  eq_sub_of_add_eq$
    by 
      delta' xz <;> rw [←Int.coe_nat_add, ←Int.coe_nat_mul, xn_succ_succ]

theorem yz_succ_succ n : yz (n+2) = ((2*a : ℕ)*yz (n+1)) - yz n :=
  eq_sub_of_add_eq$
    by 
      delta' yz <;> rw [←Int.coe_nat_add, ←Int.coe_nat_mul, yn_succ_succ]

theorem yn_modeq_a_sub_one : ∀ n, yn n ≡ n [MOD a - 1]
| 0 =>
  by 
    simp 
| 1 =>
  by 
    simp 
| n+2 =>
  (yn_modeq_a_sub_one n).add_right_cancel$
    by 
      rw [yn_succ_succ,
        (by 
          ring :
        ((n+2)+n) = 2*n+1)]
      exact ((modeq_sub a1.le).mul_left 2).mul (yn_modeq_a_sub_one (n+1))

theorem yn_modeq_two : ∀ n, yn n ≡ n [MOD 2]
| 0 =>
  by 
    simp 
| 1 =>
  by 
    simp 
| n+2 =>
  (yn_modeq_two n).add_right_cancel$
    by 
      rw [yn_succ_succ, mul_assocₓ,
        (by 
          ring :
        ((n+2)+n) = 2*n+1)]
      exact (dvd_mul_right 2 _).modeq_zero_nat.trans (dvd_mul_right 2 _).zero_modeq_nat

section 

omit a1

theorem x_sub_y_dvd_pow_lem (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : ℤ) :
  ((((a2*yn1) - yn0)*ay)+y2) - ((a2*xn1) - xn0) = (((y2 - a2*y1)+y0)+a2*((yn1*ay)+y1) - xn1) - (((yn0*ay)+y0) - xn0) :=
  by 
    ring

end 

theorem x_sub_y_dvd_pow (y : ℕ) : ∀ n, ((((2*a)*y) - y*y) - 1 : ℤ) ∣ ((yz n*a - y)+«expr↑ » (y ^ n)) - xz n
| 0 =>
  by 
    simp [xz, yz, Int.coe_nat_zero, Int.coe_nat_one]
| 1 =>
  by 
    simp [xz, yz, Int.coe_nat_zero, Int.coe_nat_one]
| n+2 =>
  have  : ((((2*a)*y) - y*y) - 1 : ℤ) ∣ («expr↑ » (y ^ n+2) - «expr↑ » (2*a)*«expr↑ » (y ^ n+1))+«expr↑ » (y ^ n) :=
    ⟨-«expr↑ » (y ^ n),
      by 
        simp [pow_succₓ, mul_addₓ, Int.coe_nat_mul, show ((2 : ℕ) : ℤ) = 2 from rfl, mul_commₓ, mul_left_commₓ]
        ring⟩
  by 
    rw [xz_succ_succ, yz_succ_succ, x_sub_y_dvd_pow_lem («expr↑ » (y ^ n+2)) («expr↑ » (y ^ n+1)) («expr↑ » (y ^ n))]
    exact dvd_sub (dvd_add this$ (x_sub_y_dvd_pow (n+1)).mul_left _) (x_sub_y_dvd_pow n)

theorem xn_modeq_x2n_add_lem n j : xn n ∣ ((d*yn n)*yn n*xn j)+xn j :=
  have h1 : (((d*yn n)*yn n*xn j)+xn j) = (((d*yn n)*yn n)+1)*xn j :=
    by 
      simp [add_mulₓ, mul_assocₓ]
  have h2 : (((d*yn n)*yn n)+1) = xn n*xn n :=
    by 
      apply Int.coe_nat_inj <;>
        repeat' 
            first |
              rw [Int.coe_nat_add]|
              rw [Int.coe_nat_mul] <;>
          exact add_eq_of_eq_sub' (Eq.symm$ pell_eqz _ _)
  by 
    rw [h2] at h1 <;> rw [h1, mul_assocₓ] <;> exact dvd_mul_right _ _

theorem xn_modeq_x2n_add n j : (xn ((2*n)+j)+xn j) ≡ 0 [MOD xn n] :=
  by 
    rw [two_mul, add_assocₓ, xn_add, add_assocₓ, ←zero_addₓ 0]
    refine' (dvd_mul_right (xn a1 n) (xn a1 (n+j))).modeq_zero_nat.add _ 
    rw [yn_add, left_distrib, add_assocₓ, ←zero_addₓ 0]
    exact ((dvd_mul_right _ _).mul_left _).modeq_zero_nat.add (xn_modeq_x2n_add_lem _ _ _).modeq_zero_nat

theorem xn_modeq_x2n_sub_lem {n j} (h : j ≤ n) : (xn ((2*n) - j)+xn j) ≡ 0 [MOD xn n] :=
  have h1 : xz n ∣ ((«expr↑ » d*yz n)*yz (n - j))+xz j :=
    by 
      rw [yz_sub _ h, mul_sub_left_distrib, sub_add_eq_add_sub] <;>
        exact
          dvd_sub
            (by 
              delta' xz <;>
                delta' yz <;>
                  repeat' 
                      first |
                        rw [←Int.coe_nat_add]|
                        rw [←Int.coe_nat_mul] <;>
                    rw [mul_commₓ (xn a1 j) (yn a1 n)] <;> exact Int.coe_nat_dvd.2 (xn_modeq_x2n_add_lem _ _ _))
            ((dvd_mul_right _ _).mul_left _)
  by 
    rw [two_mul, add_tsub_assoc_of_le h, xn_add, add_assocₓ, ←zero_addₓ 0]
    exact
      (dvd_mul_right _ _).modeq_zero_nat.add
        (Int.coe_nat_dvd.1$
            by 
              simpa [xz, yz] using h1).modeq_zero_nat

theorem xn_modeq_x2n_sub {n j} (h : j ≤ 2*n) : (xn ((2*n) - j)+xn j) ≡ 0 [MOD xn n] :=
  (le_totalₓ j n).elim xn_modeq_x2n_sub_lem
    fun jn =>
      have  : (((2*n) - j)+j) ≤ n+j :=
        by 
          rw [tsub_add_cancel_of_le h, two_mul] <;> exact Nat.add_le_add_leftₓ jn _ 
      let t := xn_modeq_x2n_sub_lem (Nat.le_of_add_le_add_rightₓ this)
      by 
        rwa [tsub_tsub_cancel_of_le h, add_commₓ] at t

theorem xn_modeq_x4n_add n j : xn ((4*n)+j) ≡ xn j [MOD xn n] :=
  modeq.add_right_cancel' (xn ((2*n)+j))$
    by 
      refine'
          @modeq.trans _ _ 0 _ _
            (by 
              rw [add_commₓ] <;> exact (xn_modeq_x2n_add _ _ _).symm) <;>
        rw [show (4*n) = (2*n)+2*n from right_distrib 2 2 n, add_assocₓ] <;> apply xn_modeq_x2n_add

theorem xn_modeq_x4n_sub {n j} (h : j ≤ 2*n) : xn ((4*n) - j) ≡ xn j [MOD xn n] :=
  have h' : j ≤ 2*n :=
    le_transₓ h
      (by 
        rw [Nat.succ_mul] <;> apply Nat.le_add_leftₓ)
  modeq.add_right_cancel' (xn ((2*n) - j))$
    by 
      refine'
          @modeq.trans _ _ 0 _ _
            (by 
              rw [add_commₓ] <;> exact (xn_modeq_x2n_sub _ h).symm) <;>
        rw [show (4*n) = (2*n)+2*n from right_distrib 2 2 n, add_tsub_assoc_of_le h'] <;> apply xn_modeq_x2n_add

theorem eq_of_xn_modeq_lem1 {i n} : ∀ {j}, i < j → j < n → xn i % xn n < xn j % xn n
| 0, ij, _ => absurd ij (Nat.not_lt_zeroₓ _)
| j+1, ij, jn =>
  suffices xn j % xn n < xn (j+1) % xn n from
    (lt_or_eq_of_leₓ (Nat.le_of_succ_le_succₓ ij)).elim (fun h => lt_transₓ (eq_of_xn_modeq_lem1 h (le_of_ltₓ jn)) this)
      fun h =>
        by 
          rw [h] <;> exact this 
  by 
    rw [Nat.mod_eq_of_ltₓ (strict_mono_x _ (Nat.lt_of_succ_ltₓ jn)), Nat.mod_eq_of_ltₓ (strict_mono_x _ jn)] <;>
      exact strict_mono_x _ (Nat.lt_succ_selfₓ _)

theorem eq_of_xn_modeq_lem2 {n} (h : (2*xn n) = xn (n+1)) : a = 2 ∧ n = 0 :=
  by 
    rw [xn_succ, mul_commₓ] at h <;>
      exact
        have  : n = 0 :=
          n.eq_zero_or_pos.resolve_right$
            fun np =>
              ne_of_ltₓ
                (lt_of_le_of_ltₓ (Nat.mul_le_mul_leftₓ _ a1)
                  (Nat.lt_add_of_pos_rightₓ$ mul_pos (d_pos a1) (strict_mono_y a1 np)))
                h 
        by 
          cases this <;> simp  at h <;> exact ⟨h.symm, rfl⟩

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_xn_modeq_lem3
{i n}
(npos : «expr < »(0, n)) : ∀
{j}, «expr < »(i, j) → «expr ≤ »(j, «expr * »(2, n)) → «expr ≠ »(j, n) → «expr¬ »(«expr ∧ »(«expr = »(a, 2), «expr ∧ »(«expr = »(n, 1), «expr ∧ »(«expr = »(i, 0), «expr = »(j, 2))))) → «expr < »(«expr % »(xn i, xn n), «expr % »(xn j, xn n))
| 0, ij, _, _, _ := absurd ij (nat.not_lt_zero _)
| «expr + »(j, 1), ij, j2n, jnn, ntriv := have lem2 : ∀
k «expr > » n, «expr ≤ »(k, «expr * »(2, n)) → «expr = »((«expr↑ »(«expr % »(xn k, xn n)) : exprℤ()), «expr - »(xn n, xn «expr - »(«expr * »(2, n), k))), from λ
k
kn
k2n, let k2nl := «expr $ »(lt_of_add_lt_add_right, show «expr < »(«expr + »(«expr - »(«expr * »(2, n), k), k), «expr + »(n, k)), by { rw [expr tsub_add_cancel_of_le] [],
       rw [expr two_mul] []; exact [expr add_lt_add_left kn n],
       exact [expr k2n] }) in
have xle : «expr ≤ »(xn «expr - »(«expr * »(2, n), k), xn n), from «expr $ »(le_of_lt, strict_mono_x k2nl),
suffices «expr = »(«expr % »(xn k, xn n), «expr - »(xn n, xn «expr - »(«expr * »(2, n), k))), by rw ["[", expr this, ",", expr int.coe_nat_sub xle, "]"] [],
by { rw ["<-", expr nat.mod_eq_of_lt (nat.sub_lt (x_pos a1 n) (x_pos a1 «expr - »(«expr * »(2, n), k)))] [],
  apply [expr modeq.add_right_cancel' (xn a1 «expr - »(«expr * »(2, n), k))],
  rw ["[", expr tsub_add_cancel_of_le xle, "]"] [],
  have [ident t] [] [":=", expr xn_modeq_x2n_sub_lem a1 k2nl.le],
  rw [expr tsub_tsub_cancel_of_le k2n] ["at", ident t],
  exact [expr t.trans dvd_rfl.zero_modeq_nat] },
«expr $ »((lt_trichotomy j n).elim (λ
  jn : «expr < »(j, n), eq_of_xn_modeq_lem1 ij (lt_of_le_of_ne jn jnn)), λ
 o, o.elim (λ jn : «expr = »(j, n), by { cases [expr jn] [],
    apply [expr int.lt_of_coe_nat_lt_coe_nat],
    rw ["[", expr lem2 «expr + »(n, 1) (nat.lt_succ_self _) j2n, ",", expr show «expr = »(«expr - »(«expr * »(2, n), «expr + »(n, 1)), «expr - »(n, 1)), by rw ["[", expr two_mul, ",", expr tsub_add_eq_tsub_tsub, ",", expr add_tsub_cancel_right, "]"] [], "]"] [],
    refine [expr lt_sub_left_of_add_lt (int.coe_nat_lt_coe_nat_of_lt _)],
    cases [expr «expr $ »(lt_or_eq_of_le, nat.le_of_succ_le_succ ij)] ["with", ident lin, ident ein],
    { rw [expr nat.mod_eq_of_lt (strict_mono_x _ lin)] [],
      have [ident ll] [":", expr «expr ≤ »(«expr + »(xn a1 «expr - »(n, 1), xn a1 «expr - »(n, 1)), xn a1 n)] [],
      { rw ["[", "<-", expr two_mul, ",", expr mul_comm, ",", expr show «expr = »(xn a1 n, xn a1 «expr + »(«expr - »(n, 1), 1)), by rw ["[", expr tsub_add_cancel_of_le (succ_le_of_lt npos), "]"] [], ",", expr xn_succ, "]"] [],
        exact [expr le_trans (nat.mul_le_mul_left _ a1) (nat.le_add_right _ _)] },
      have [ident npm] [":", expr «expr = »(«expr - »(n, 1).succ, n)] [":=", expr nat.succ_pred_eq_of_pos npos],
      have [ident il] [":", expr «expr ≤ »(i, «expr - »(n, 1))] [],
      { apply [expr nat.le_of_succ_le_succ],
        rw [expr npm] [],
        exact [expr lin] },
      cases [expr lt_or_eq_of_le il] ["with", ident ill, ident ile],
      { exact [expr lt_of_lt_of_le (nat.add_lt_add_left (strict_mono_x a1 ill) _) ll] },
      { rw [expr ile] [],
        apply [expr lt_of_le_of_ne ll],
        rw ["<-", expr two_mul] [],
        exact [expr λ
         e, «expr $ »(ntriv, let ⟨a2, s1⟩ := @eq_of_xn_modeq_lem2 _ a1 «expr - »(n, 1) (by rwa ["[", expr tsub_add_cancel_of_le (succ_le_of_lt npos), "]"] []) in
          have n1 : «expr = »(n, 1), from le_antisymm (tsub_eq_zero_iff_le.mp s1) npos,
          by rw ["[", expr ile, ",", expr a2, ",", expr n1, "]"] []; exact [expr ⟨rfl, rfl, rfl, rfl⟩])] } },
    { rw ["[", expr ein, ",", expr nat.mod_self, ",", expr add_zero, "]"] [],
      exact [expr strict_mono_x _ (nat.pred_lt npos.ne')] } }) (λ
  jn : «expr > »(j, n), have lem1 : «expr ≠ »(j, n) → «expr < »(«expr % »(xn j, xn n), «expr % »(xn «expr + »(j, 1), xn n)) → «expr < »(«expr % »(xn i, xn n), «expr % »(xn «expr + »(j, 1), xn n)), from λ
  jn
  s, (lt_or_eq_of_le (nat.le_of_succ_le_succ ij)).elim (λ
   h, lt_trans «expr $ »(eq_of_xn_modeq_lem3 h (le_of_lt j2n) jn, λ
    ⟨a1, n1, i0, j2⟩, by rw ["[", expr n1, ",", expr j2, "]"] ["at", ident j2n]; exact [expr absurd j2n exprdec_trivial()]) s) (λ
   h, by rw [expr h] []; exact [expr s]),
  «expr $ »(lem1 (ne_of_gt jn), «expr $ »(int.lt_of_coe_nat_lt_coe_nat, by { rw ["[", expr lem2 j jn (le_of_lt j2n), ",", expr lem2 «expr + »(j, 1) (nat.le_succ_of_le jn) j2n, "]"] [],
      refine [expr sub_lt_sub_left «expr $ »(int.coe_nat_lt_coe_nat_of_lt, strict_mono_x _ _) _],
      rw ["[", expr nat.sub_succ, "]"] [],
      exact [expr nat.pred_lt «expr $ »(ne_of_gt, tsub_pos_of_lt j2n)] }))))

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_xn_modeq_le
{i j n}
(npos : «expr < »(0, n))
(ij : «expr ≤ »(i, j))
(j2n : «expr ≤ »(j, «expr * »(2, n)))
(h : «expr ≡ [MOD ]»(xn i, xn j, xn n))
(ntriv : «expr¬ »(«expr ∧ »(«expr = »(a, 2), «expr ∧ »(«expr = »(n, 1), «expr ∧ »(«expr = »(i, 0), «expr = »(j, 2)))))) : «expr = »(i, j) :=
«expr $ »((lt_or_eq_of_le ij).resolve_left, λ ij', if jn : «expr = »(j, n) then by { refine [expr ne_of_gt _ h],
   rw ["[", expr jn, ",", expr nat.mod_self, "]"] [],
   have [ident x0] [":", expr «expr < »(0, «expr % »(xn a1 0, xn a1 n))] [":=", expr by rw ["[", expr nat.mod_eq_of_lt (strict_mono_x a1 npos), "]"] []; exact [expr exprdec_trivial()]],
   cases [expr i] ["with", ident i],
   exact [expr x0],
   rw [expr jn] ["at", ident ij'],
   exact [expr x0.trans «expr $ »(eq_of_xn_modeq_lem3 _ npos (nat.succ_pos _) (le_trans ij j2n) (ne_of_lt ij'), λ
     ⟨a1, n1, _, i2⟩, by rw ["[", expr n1, ",", expr i2, "]"] ["at", ident ij']; exact [expr absurd ij' exprdec_trivial()])] } else ne_of_lt (eq_of_xn_modeq_lem3 npos ij' j2n jn ntriv) h)

theorem eq_of_xn_modeq {i j n} (npos : 0 < n) (i2n : i ≤ 2*n) (j2n : j ≤ 2*n) (h : xn i ≡ xn j [MOD xn n])
  (ntriv : a = 2 → n = 1 → (i = 0 → j ≠ 2) ∧ (i = 2 → j ≠ 0)) : i = j :=
  (le_totalₓ i j).elim (fun ij => eq_of_xn_modeq_le npos ij j2n h$ fun ⟨a2, n1, i0, j2⟩ => (ntriv a2 n1).left i0 j2)
    fun ij => (eq_of_xn_modeq_le npos ij i2n h.symm$ fun ⟨a2, n1, j0, i2⟩ => (ntriv a2 n1).right i2 j0).symm

theorem eq_of_xn_modeq' {i j n} (ipos : 0 < i) (hin : i ≤ n) (j4n : j ≤ 4*n) (h : xn j ≡ xn i [MOD xn n]) :
  j = i ∨ (j+i) = 4*n :=
  have i2n : i ≤ 2*n :=
    by 
      apply le_transₓ hin <;> rw [two_mul] <;> apply Nat.le_add_leftₓ 
  have npos : 0 < n := lt_of_lt_of_leₓ ipos hin
  (le_or_gtₓ j (2*n)).imp
    (fun j2n : j ≤ 2*n =>
      eq_of_xn_modeq npos j2n i2n h$
        fun a2 n1 =>
          ⟨fun j0 i2 =>
              by 
                rw [n1, i2] at hin <;>
                  exact
                    absurd hin
                      (by 
                        decide),
            fun j2 i0 => ne_of_gtₓ ipos i0⟩)
    fun j2n : (2*n) < j =>
      suffices i = (4*n) - j by 
        rw [this, add_tsub_cancel_of_le j4n]
      have j42n : (4*n) - j ≤ 2*n :=
        @Nat.le_of_add_le_add_rightₓ j _ _$
          by 
            rw [tsub_add_cancel_of_le j4n, show (4*n) = (2*n)+2*n from right_distrib 2 2 n] <;>
              exact Nat.add_le_add_leftₓ (le_of_ltₓ j2n) _ 
      eq_of_xn_modeq npos i2n j42n
        (h.symm.trans$
          let t := xn_modeq_x4n_sub j42n 
          by 
            rwa [tsub_tsub_cancel_of_le j4n] at t)
        fun a2 n1 =>
          ⟨fun i0 => absurd i0 (ne_of_gtₓ ipos),
            fun i2 =>
              by 
                rw [n1, i2] at hin 
                exact
                  absurd hin
                    (by 
                      decide)⟩

theorem modeq_of_xn_modeq {i j n} (ipos : 0 < i) (hin : i ≤ n) (h : xn j ≡ xn i [MOD xn n]) :
  j ≡ i [MOD 4*n] ∨ (j+i) ≡ 0 [MOD 4*n] :=
  let j' := j % 4*n 
  have n4 : 0 < 4*n :=
    mul_pos
      (by 
        decide)
      (ipos.trans_le hin)
  have jl : j' < 4*n := Nat.mod_ltₓ _ n4 
  have jj : j ≡ j' [MOD 4*n] :=
    by 
      delta' modeq <;> rw [Nat.mod_eq_of_ltₓ jl]
  have  : ∀ j q, xn (j+(4*n)*q) ≡ xn j [MOD xn n] :=
    by 
      intro j q 
      induction' q with q IH
      ·
        simp 
      rw [Nat.mul_succ, ←add_assocₓ, add_commₓ]
      exact (xn_modeq_x4n_add _ _ _).trans IH 
  Or.imp
    (fun ji : j' = i =>
      by 
        rwa [←ji])
    (fun ji : (j'+i) = 4*n =>
      (jj.add_right _).trans$
        by 
          rw [ji]
          exact dvd_rfl.modeq_zero_nat)
    (eq_of_xn_modeq' ipos hin jl.le$
      (h.symm.trans$
          by 
            rw [←Nat.mod_add_divₓ j (4*n)]
            exact this j' _).symm)

end 

theorem xy_modeq_of_modeq {a b c} (a1 : 1 < a) (b1 : 1 < b) (h : a ≡ b [MOD c]) :
  ∀ n, xn a1 n ≡ xn b1 n [MOD c] ∧ yn a1 n ≡ yn b1 n [MOD c]
| 0 =>
  by 
    constructor <;> rfl
| 1 =>
  by 
    simp  <;> exact ⟨h, modeq.refl 1⟩
| n+2 =>
  ⟨(xy_modeq_of_modeq n).left.add_right_cancel$
      by 
        rw [xn_succ_succ a1, xn_succ_succ b1]
        exact (h.mul_left _).mul (xy_modeq_of_modeq (n+1)).left,
    (xy_modeq_of_modeq n).right.add_right_cancel$
      by 
        rw [yn_succ_succ a1, yn_succ_succ b1]
        exact (h.mul_left _).mul (xy_modeq_of_modeq (n+1)).right⟩

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem matiyasevic
{a
 k
 x
 y} : «expr ↔ »(«expr∃ , »((a1 : «expr < »(1, a)), «expr ∧ »(«expr = »(xn a1 k, x), «expr = »(yn a1 k, y))), «expr ∧ »(«expr < »(1, a), «expr ∧ »(«expr ≤ »(k, y), «expr ∨ »(«expr ∧ »(«expr = »(x, 1), «expr = »(y, 0)), «expr∃ , »((u
      v
      s
      t
      b : exprℕ()), «expr ∧ »(«expr = »(«expr - »(«expr * »(x, x), «expr * »(«expr * »(«expr - »(«expr * »(a, a), 1), y), y)), 1), «expr ∧ »(«expr = »(«expr - »(«expr * »(u, u), «expr * »(«expr * »(«expr - »(«expr * »(a, a), 1), v), v)), 1), «expr ∧ »(«expr = »(«expr - »(«expr * »(s, s), «expr * »(«expr * »(«expr - »(«expr * »(b, b), 1), t), t)), 1), «expr ∧ »(«expr < »(1, b), «expr ∧ »(«expr ≡ [MOD ]»(b, 1, «expr * »(4, y)), «expr ∧ »(«expr ≡ [MOD ]»(b, a, u), «expr ∧ »(«expr < »(0, v), «expr ∧ »(«expr ∣ »(«expr * »(y, y), v), «expr ∧ »(«expr ≡ [MOD ]»(s, x, u), «expr ≡ [MOD ]»(t, k, «expr * »(4, y)))))))))))))))) :=
⟨λ
 ⟨a1, hx, hy⟩, by rw ["[", "<-", expr hx, ",", "<-", expr hy, "]"] []; refine [expr ⟨a1, (nat.eq_zero_or_pos k).elim (λ
    k0, by rw [expr k0] []; exact [expr ⟨le_rfl, or.inl ⟨rfl, rfl⟩⟩]) (λ
    kpos, _)⟩]; exact [expr let x := xn a1 k,
      y := yn a1 k,
      m := «expr * »(2, «expr * »(k, y)),
      u := xn a1 m,
      v := yn a1 m in
  have ky : «expr ≤ »(k, y), from yn_ge_n a1 k,
  have yv : «expr ∣ »(«expr * »(y, y), v), from «expr $ »((ysq_dvd_yy a1 k).trans, «expr $ »((y_dvd_iff _ _ _).2, dvd_mul_left _ _)),
  have uco : nat.coprime u «expr * »(4, y), from have «expr ∣ »(2, v), from «expr $ »(modeq_zero_iff_dvd.1, (yn_modeq_two _ _).trans (dvd_mul_right _ _).modeq_zero_nat),
  have nat.coprime u 2, from (xy_coprime a1 m).coprime_dvd_right this,
  «expr $ »((this.mul_right this).mul_right, (xy_coprime _ _).coprime_dvd_right (dvd_of_mul_left_dvd yv)),
  let ⟨b, ba, bm1⟩ := chinese_remainder uco a 1 in
  have m1 : «expr < »(1, m), from have «expr < »(0, «expr * »(k, y)), from mul_pos kpos (strict_mono_y a1 kpos),
  nat.mul_le_mul_left 2 this,
  have vp : «expr < »(0, v), from strict_mono_y a1 (lt_trans zero_lt_one m1),
  have b1 : «expr < »(1, b), from have «expr < »(xn a1 1, u), from strict_mono_x a1 m1,
  have «expr < »(a, u), by simp [] [] [] [] [] ["at", ident this]; exact [expr this],
  «expr $ »(lt_of_lt_of_le a1, by delta [ident modeq] ["at", ident ba]; rw [expr nat.mod_eq_of_lt this] ["at", ident ba]; rw ["<-", expr ba] []; apply [expr nat.mod_le]),
  let s := xn b1 k, t := yn b1 k in
  have sx : «expr ≡ [MOD ]»(s, x, u), from (xy_modeq_of_modeq b1 a1 ba k).left,
  have tk : «expr ≡ [MOD ]»(t, k, «expr * »(4, y)), from have «expr ∣ »(«expr * »(4, y), «expr - »(b, 1)), from «expr $ »(int.coe_nat_dvd.1, by rw [expr int.coe_nat_sub (le_of_lt b1)] []; exact [expr bm1.symm.dvd]),
  (yn_modeq_a_sub_one _ _).modeq_of_dvd this,
  ⟨ky, or.inr ⟨u, v, s, t, b, pell_eq _ _, pell_eq _ _, pell_eq _ _, b1, bm1, ba, vp, yv, sx, tk⟩⟩], λ
 ⟨a1, ky, o⟩, ⟨a1, match o with
  | or.inl ⟨x1, y0⟩ := by rw [expr y0] ["at", ident ky]; rw ["[", expr nat.eq_zero_of_le_zero ky, ",", expr x1, ",", expr y0, "]"] []; exact [expr ⟨rfl, rfl⟩]
  | or.inr ⟨u, v, s, t, b, xy, uv, st, b1, rem⟩ := match x, y, eq_pell a1 xy, u, v, eq_pell a1 uv, s, t, eq_pell b1 st, rem, ky with
  | ._, ._, ⟨i, rfl, rfl⟩, ._, ._, ⟨n, rfl, rfl⟩, ._, ._, ⟨j, rfl, rfl⟩, ⟨(bm1 : «expr ≡ [MOD ]»(b, 1, «expr * »(4, yn a1 i))), (ba : «expr ≡ [MOD ]»(b, a, xn a1 n)), (vp : «expr < »(0, yn a1 n)), (yv : «expr ∣ »(«expr * »(yn a1 i, yn a1 i), yn a1 n)), (sx : «expr ≡ [MOD ]»(xn b1 j, xn a1 i, xn a1 n)), (tk : «expr ≡ [MOD ]»(yn b1 j, k, «expr * »(4, yn a1 i)))⟩, (ky : «expr ≤ »(k, yn a1 i)) := «expr $ »((nat.eq_zero_or_pos i).elim (λ
    i0, by simp [] [] [] ["[", expr i0, "]"] [] ["at", ident ky]; rw ["[", expr i0, ",", expr ky, "]"] []; exact [expr ⟨rfl, rfl⟩]), λ
   ipos, suffices «expr = »(i, k), by rw [expr this] []; exact [expr ⟨rfl, rfl⟩],
   by clear [ident _x, ident o, ident rem, ident xy, ident uv, ident st, ident _match, ident _match, ident _fun_match]; exact [expr have iln : «expr ≤ »(i, n), from «expr $ »(le_of_not_gt, λ
     hin, not_lt_of_ge (nat.le_of_dvd vp (dvd_of_mul_left_dvd yv)) (strict_mono_y a1 hin)),
    have yd : «expr ∣ »(«expr * »(4, yn a1 i), «expr * »(4, n)), from «expr $ »(mul_dvd_mul_left _, dvd_of_ysq_dvd a1 yv),
    have jk : «expr ≡ [MOD ]»(j, k, «expr * »(4, yn a1 i)), from have «expr ∣ »(«expr * »(4, yn a1 i), «expr - »(b, 1)), from «expr $ »(int.coe_nat_dvd.1, by rw [expr int.coe_nat_sub (le_of_lt b1)] []; exact [expr bm1.symm.dvd]),
    ((yn_modeq_a_sub_one b1 _).modeq_of_dvd this).symm.trans tk,
    have ki : «expr < »(«expr + »(k, i), «expr * »(4, yn a1 i)), from «expr $ »(lt_of_le_of_lt (add_le_add ky (yn_ge_n a1 i)), by rw ["<-", expr two_mul] []; exact [expr nat.mul_lt_mul_of_pos_right exprdec_trivial() (strict_mono_y a1 ipos)]),
    have ji : «expr ≡ [MOD ]»(j, i, «expr * »(4, n)), from have «expr ≡ [MOD ]»(xn a1 j, xn a1 i, xn a1 n), from (xy_modeq_of_modeq b1 a1 ba j).left.symm.trans sx,
    «expr $ »((modeq_of_xn_modeq a1 ipos iln this).resolve_right, λ
     ji : «expr ≡ [MOD ]»(«expr + »(j, i), 0, «expr * »(4, n)), «expr $ »(not_le_of_gt ki, «expr $ »(nat.le_of_dvd «expr $ »(lt_of_lt_of_le ipos, nat.le_add_left _ _), «expr $ »(modeq_zero_iff_dvd.1, «expr $ »((jk.symm.add_right i).trans, ji.modeq_of_dvd yd))))),
    by have [] [":", expr «expr = »(«expr % »(i, «expr * »(4, yn a1 i)), «expr % »(k, «expr * »(4, yn a1 i)))] [":=", expr (ji.modeq_of_dvd yd).symm.trans jk]; rwa ["[", expr nat.mod_eq_of_lt (lt_of_le_of_lt (nat.le_add_left _ _) ki), ",", expr nat.mod_eq_of_lt (lt_of_le_of_lt (nat.le_add_right _ _) ki), "]"] ["at", ident this]])
  end
  end⟩⟩

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_pow_of_pell_lem
{a y k}
(a1 : «expr < »(1, a))
(ypos : «expr < »(0, y)) : «expr < »(0, k) → «expr < »(«expr ^ »(y, k), a) → «expr < »((«expr↑ »(«expr ^ »(y, k)) : exprℤ()), «expr - »(«expr - »(«expr * »(«expr * »(2, a), y), «expr * »(y, y)), 1)) :=
have «expr < »(y, a) → «expr ≤ »(«expr + »(a, «expr + »(«expr * »(y, y), 1)), «expr * »(«expr * »(2, a), y)), begin
  intro [ident ya],
  induction [expr y] [] ["with", ident y, ident IH] [],
  exact [expr absurd ypos (lt_irrefl _)],
  cases [expr nat.eq_zero_or_pos y] ["with", ident y0, ident ypos],
  { rw [expr y0] [],
    simpa [] [] [] ["[", expr two_mul, "]"] [] [] },
  { rw ["[", expr nat.mul_succ, ",", expr nat.mul_succ, ",", expr nat.succ_mul y, "]"] [],
    have [] [":", expr «expr ≤ »(«expr + »(y, nat.succ y), «expr * »(2, a))] [],
    { change [expr «expr < »(«expr + »(y, y), «expr * »(2, a))] [] [],
      rw ["<-", expr two_mul] [],
      exact [expr mul_lt_mul_of_pos_left (nat.lt_of_succ_lt ya) exprdec_trivial()] },
    have [] [] [":=", expr add_le_add (IH ypos (nat.lt_of_succ_lt ya)) this],
    convert [] [expr this] ["using", 1],
    ring [] }
end,
λ
k0
yak, «expr $ »(lt_of_lt_of_le (int.coe_nat_lt_coe_nat_of_lt yak), by rw [expr sub_sub] []; apply [expr le_sub_right_of_add_le]; apply [expr int.coe_nat_le_coe_nat_of_le]; have [ident y1] [] [":=", expr nat.pow_le_pow_of_le_right ypos k0]; simp [] [] [] [] [] ["at", ident y1]; exact [expr this (lt_of_le_of_lt y1 yak)])

-- error in NumberTheory.Pell: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_pow_of_pell
{m
 n
 k} : «expr ↔ »(«expr = »(«expr ^ »(n, k), m), «expr ∨ »(«expr ∧ »(«expr = »(k, 0), «expr = »(m, 1)), «expr ∧ »(«expr < »(0, k), «expr ∨ »(«expr ∧ »(«expr = »(n, 0), «expr = »(m, 0)), «expr ∧ »(«expr < »(0, n), «expr∃ , »((w
       a
       t
       z : exprℕ())
      (a1 : «expr < »(1, a)), «expr ∧ »(«expr ≡ [MOD ]»(xn a1 k, «expr + »(«expr * »(yn a1 k, «expr - »(a, n)), m), t), «expr ∧ »(«expr = »(«expr * »(«expr * »(2, a), n), «expr + »(t, «expr + »(«expr * »(n, n), 1))), «expr ∧ »(«expr < »(m, t), «expr ∧ »(«expr ≤ »(n, w), «expr ∧ »(«expr ≤ »(k, w), «expr = »(«expr - »(«expr * »(a, a), «expr * »(«expr * »(«expr - »(«expr * »(«expr + »(w, 1), «expr + »(w, 1)), 1), «expr * »(w, z)), «expr * »(w, z))), 1)))))))))))) :=
⟨λ
 e, by rw ["<-", expr e] []; refine [expr (nat.eq_zero_or_pos k).elim (λ
   k0, by rw [expr k0] []; exact [expr or.inl ⟨rfl, rfl⟩]) (λ
   kpos, or.inr ⟨kpos, _⟩)]; refine [expr (nat.eq_zero_or_pos n).elim (λ
   n0, by rw ["[", expr n0, ",", expr zero_pow kpos, "]"] []; exact [expr or.inl ⟨rfl, rfl⟩]) (λ
   npos, or.inr ⟨npos, _⟩)]; exact [expr let w := max n k in
  have nw : «expr ≤ »(n, w), from le_max_left _ _,
  have kw : «expr ≤ »(k, w), from le_max_right _ _,
  have wpos : «expr < »(0, w), from lt_of_lt_of_le npos nw,
  have w1 : «expr < »(1, «expr + »(w, 1)), from nat.succ_lt_succ wpos,
  let a := xn w1 w in
  have a1 : «expr < »(1, a), from strict_mono_x w1 wpos,
  let x := xn a1 k, y := yn a1 k in
  let ⟨z, ze⟩ := show «expr ∣ »(w, yn w1 w), from «expr $ »(modeq_zero_iff_dvd.1, (yn_modeq_a_sub_one w1 w).trans dvd_rfl.modeq_zero_nat) in
  have nt : «expr < »((«expr↑ »(«expr ^ »(n, k)) : exprℤ()), «expr - »(«expr - »(«expr * »(«expr * »(2, a), n), «expr * »(n, n)), 1)), from «expr $ »(eq_pow_of_pell_lem a1 npos kpos, calc
     «expr ≤ »(«expr ^ »(n, k), «expr ^ »(n, w)) : nat.pow_le_pow_of_le_right npos kw
     «expr < »(..., «expr ^ »(«expr + »(w, 1), w)) : nat.pow_lt_pow_of_lt_left (nat.lt_succ_of_le nw) wpos
     «expr ≤ »(..., a) : xn_ge_a_pow w1 w),
  let ⟨t, te⟩ := «expr $ »(int.eq_coe_of_zero_le, le_trans (int.coe_zero_le _) nt.le) in
  have na : «expr ≤ »(n, a), from «expr $ »(nw.trans, «expr $ »(le_of_lt, n_lt_xn w1 w)),
  have tm : «expr ≡ [MOD ]»(x, «expr + »(«expr * »(y, «expr - »(a, n)), «expr ^ »(n, k)), t), begin
    apply [expr modeq_of_dvd],
    rw ["[", expr int.coe_nat_add, ",", expr int.coe_nat_mul, ",", expr int.coe_nat_sub na, ",", "<-", expr te, "]"] [],
    exact [expr x_sub_y_dvd_pow a1 n k]
  end,
  have ta : «expr = »(«expr * »(«expr * »(2, a), n), «expr + »(t, «expr + »(«expr * »(n, n), 1))), from «expr $ »(int.coe_nat_inj, by rw ["[", expr int.coe_nat_add, ",", "<-", expr te, ",", expr sub_sub, "]"] []; repeat { rw [expr int.coe_nat_add] [] <|> rw [expr int.coe_nat_mul] [] }; rw ["[", expr int.coe_nat_one, ",", expr sub_add_cancel, "]"] []; refl),
  have mt : «expr < »(«expr ^ »(n, k), t), from «expr $ »(int.lt_of_coe_nat_lt_coe_nat, by rw ["<-", expr te] []; exact [expr nt]),
  have zp : «expr = »(«expr - »(«expr * »(a, a), «expr * »(«expr * »(«expr - »(«expr * »(«expr + »(w, 1), «expr + »(w, 1)), 1), «expr * »(w, z)), «expr * »(w, z))), 1), by rw ["<-", expr ze] []; exact [expr pell_eq w1 w],
  ⟨w, a, t, z, a1, tm, ta, mt, nw, kw, zp⟩], λ o, match o with
 | or.inl ⟨k0, m1⟩ := by rw ["[", expr k0, ",", expr m1, "]"] []; refl
 | or.inr ⟨kpos, or.inl ⟨n0, m0⟩⟩ := by rw ["[", expr n0, ",", expr m0, ",", expr zero_pow kpos, "]"] []
 | or.inr ⟨kpos, or.inr ⟨npos, w, a, t, z, (a1 : «expr < »(1, a)), (tm : «expr ≡ [MOD ]»(xn a1 k, «expr + »(«expr * »(yn a1 k, «expr - »(a, n)), m), t)), (ta : «expr = »(«expr * »(«expr * »(2, a), n), «expr + »(t, «expr + »(«expr * »(n, n), 1)))), (mt : «expr < »(m, t)), (nw : «expr ≤ »(n, w)), (kw : «expr ≤ »(k, w)), (zp : «expr = »(«expr - »(«expr * »(a, a), «expr * »(«expr * »(«expr - »(«expr * »(«expr + »(w, 1), «expr + »(w, 1)), 1), «expr * »(w, z)), «expr * »(w, z))), 1))⟩⟩ := have wpos : «expr < »(0, w), from lt_of_lt_of_le npos nw,
 have w1 : «expr < »(1, «expr + »(w, 1)), from nat.succ_lt_succ wpos,
 let ⟨j, xj, yj⟩ := eq_pell w1 zp in
 by clear [ident _match, ident o, ident _let_match]; exact [expr have jpos : «expr < »(0, j), from «expr $ »((nat.eq_zero_or_pos j).resolve_left, λ
   j0, have a1 : «expr = »(a, 1), by rw [expr j0] ["at", ident xj]; exact [expr xj],
   have «expr = »(«expr * »(2, n), «expr + »(t, «expr + »(«expr * »(n, n), 1))), by rw [expr a1] ["at", ident ta]; exact [expr ta],
   have n1 : «expr = »(n, 1), from have «expr < »(«expr * »(n, n), «expr * »(n, 2)), by rw ["[", expr mul_comm n 2, ",", expr this, "]"] []; apply [expr nat.le_add_left],
   have «expr ≤ »(n, 1), from «expr $ »(nat.le_of_lt_succ, lt_of_mul_lt_mul_left this (nat.zero_le _)),
   le_antisymm this npos,
   by rw [expr n1] ["at", ident this]; rw ["<-", expr @nat.add_right_cancel 0 2 t this] ["at", ident mt]; exact [expr nat.not_lt_zero _ mt]),
  have wj : «expr ≤ »(w, j), from «expr $ »(nat.le_of_dvd jpos, «expr $ »(modeq_zero_iff_dvd.1, «expr $ »((yn_modeq_a_sub_one w1 j).symm.trans, modeq_zero_iff_dvd.2 ⟨z, yj.symm⟩))),
  have nt : «expr < »((«expr↑ »(«expr ^ »(n, k)) : exprℤ()), «expr - »(«expr - »(«expr * »(«expr * »(2, a), n), «expr * »(n, n)), 1)), from «expr $ »(eq_pow_of_pell_lem a1 npos kpos, calc
     «expr ≤ »(«expr ^ »(n, k), «expr ^ »(n, j)) : nat.pow_le_pow_of_le_right npos (le_trans kw wj)
     «expr < »(..., «expr ^ »(«expr + »(w, 1), j)) : nat.pow_lt_pow_of_lt_left (nat.lt_succ_of_le nw) jpos
     «expr ≤ »(..., xn w1 j) : xn_ge_a_pow w1 j
     «expr = »(..., a) : xj.symm),
  have na : «expr ≤ »(n, a), by rw [expr xj] []; exact [expr le_trans (le_trans nw wj) «expr $ »(le_of_lt, n_lt_xn _ _)],
  have te : «expr = »((t : exprℤ()), «expr - »(«expr - »(«expr * »(«expr * »(2, «expr↑ »(a)), «expr↑ »(n)), «expr * »(«expr↑ »(n), «expr↑ »(n))), 1)), by rw [expr sub_sub] []; apply [expr eq_sub_of_add_eq]; apply [expr (int.coe_nat_eq_coe_nat_iff _ _).2]; exact [expr ta.symm],
  have «expr ≡ [MOD ]»(xn a1 k, «expr + »(«expr * »(yn a1 k, «expr - »(a, n)), «expr ^ »(n, k)), t), by have [] [] [":=", expr x_sub_y_dvd_pow a1 n k]; rw ["[", "<-", expr te, ",", "<-", expr int.coe_nat_sub na, "]"] ["at", ident this]; exact [expr modeq_of_dvd this],
  have «expr = »(«expr % »(«expr ^ »(n, k), t), «expr % »(m, t)), from (this.symm.trans tm).add_left_cancel' _,
  by rw ["<-", expr te] ["at", ident nt]; rwa ["[", expr nat.mod_eq_of_lt (int.lt_of_coe_nat_lt_coe_nat nt), ",", expr nat.mod_eq_of_lt mt, "]"] ["at", ident this]]
 end⟩

end Pell

