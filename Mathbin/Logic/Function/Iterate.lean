import Mathbin.Logic.Function.Conjugate

/-!
# Iterations of a function

In this file we prove simple properties of `nat.iterate f n` a.k.a. `f^[n]`:

* `iterate_zero`, `iterate_succ`, `iterate_succ'`, `iterate_add`, `iterate_mul`:
  formulas for `f^[0]`, `f^[n+1]` (two versions), `f^[n+m]`, and `f^[n*m]`;

* `iterate_id` : `id^[n]=id`;

* `injective.iterate`, `surjective.iterate`, `bijective.iterate` :
  iterates of an injective/surjective/bijective function belong to the same class;

* `left_inverse.iterate`, `right_inverse.iterate`, `commute.iterate_left`, `comute.iterate_right`,
  `commute.iterate_iterate`:
  some properties of pairs of functions survive under iterations

* `iterate_fixed`, `semiconj.iterate_*`, `semiconj₂.iterate`:
  if `f` fixes a point (resp., semiconjugates unary/binary operarations), then so does `f^[n]`.

-/


universe u v

variable{α : Type u}{β : Type v}

namespace Function

variable(f : α → α)

@[simp]
theorem iterate_zero : f^[0] = id :=
  rfl

theorem iterate_zero_apply (x : α) : (f^[0]) x = x :=
  rfl

@[simp]
theorem iterate_succ (n : ℕ) : f^[n.succ] = f^[n] ∘ f :=
  rfl

theorem iterate_succ_apply (n : ℕ) (x : α) : (f^[n.succ]) x = (f^[n]) (f x) :=
  rfl

@[simp]
theorem iterate_id (n : ℕ) : (id : α → α)^[n] = id :=
  Nat.recOn n rfl$
    fun n ihn =>
      by 
        rw [iterate_succ, ihn, comp.left_id]

theorem iterate_add : ∀ m n : ℕ, f^[m+n] = f^[m] ∘ f^[n]
| m, 0 => rfl
| m, Nat.succ n =>
  by 
    rw [Nat.add_succ, iterate_succ, iterate_succ, iterate_add]

theorem iterate_add_apply (m n : ℕ) (x : α) : (f^[m+n]) x = (f^[m]) ((f^[n]) x) :=
  by 
    rw [iterate_add]

@[simp]
theorem iterate_one : f^[1] = f :=
  funext$ fun a => rfl

theorem iterate_mul (m : ℕ) : ∀ n, f^[m*n] = f^[m]^[n]
| 0 =>
  by 
    simp only [Nat.mul_zero, iterate_zero]
| n+1 =>
  by 
    simp only [Nat.mul_succ, Nat.mul_one, iterate_one, iterate_add, iterate_mul n]

variable{f}

theorem iterate_fixed {x} (h : f x = x) (n : ℕ) : (f^[n]) x = x :=
  Nat.recOn n rfl$
    fun n ihn =>
      by 
        rw [iterate_succ_apply, h, ihn]

theorem injective.iterate (Hinj : injective f) (n : ℕ) : injective (f^[n]) :=
  Nat.recOn n injective_id$ fun n ihn => ihn.comp Hinj

theorem surjective.iterate (Hsurj : surjective f) (n : ℕ) : surjective (f^[n]) :=
  Nat.recOn n surjective_id$ fun n ihn => ihn.comp Hsurj

theorem bijective.iterate (Hbij : bijective f) (n : ℕ) : bijective (f^[n]) :=
  ⟨Hbij.1.iterate n, Hbij.2.iterate n⟩

namespace Semiconj

theorem iterate_right {f : α → β} {ga : α → α} {gb : β → β} (h : semiconj f ga gb) (n : ℕ) :
  semiconj f (ga^[n]) (gb^[n]) :=
  Nat.recOn n id_right$ fun n ihn => ihn.comp_right h

theorem iterate_left {g : ℕ → α → α} (H : ∀ n, semiconj f (g n) (g$ n+1)) (n k : ℕ) : semiconj (f^[n]) (g k) (g$ n+k) :=
  by 
    induction' n with n ihn generalizing k
    ·
      rw [Nat.zero_add]
      exact id_left
    ·
      rw [Nat.succ_eq_add_one, Nat.add_right_comm, Nat.add_assoc]
      exact (H k).compLeft (ihn (k+1))

end Semiconj

namespace Commute

variable{g : α → α}

theorem iterate_right (h : commute f g) (n : ℕ) : commute f (g^[n]) :=
  h.iterate_right n

theorem iterate_left (h : commute f g) (n : ℕ) : commute (f^[n]) g :=
  (h.symm.iterate_right n).symm

theorem iterate_iterate (h : commute f g) (m n : ℕ) : commute (f^[m]) (g^[n]) :=
  (h.iterate_left m).iterate_right n

theorem iterate_eq_of_map_eq (h : commute f g) (n : ℕ) {x} (hx : f x = g x) : (f^[n]) x = (g^[n]) x :=
  Nat.recOn n rfl$
    fun n ihn =>
      by 
        simp only [iterate_succ_apply, hx, (h.iterate_left n).Eq, ihn, ((refl g).iterate_right n).Eq]

theorem comp_iterate (h : commute f g) (n : ℕ) : (f ∘ g)^[n] = f^[n] ∘ g^[n] :=
  by 
    induction' n with n ihn
    ·
      rfl 
    funext x 
    simp only [ihn, (h.iterate_right n).Eq, iterate_succ, comp_app]

variable(f)

theorem iterate_self (n : ℕ) : commute (f^[n]) f :=
  (refl f).iterate_left n

theorem self_iterate (n : ℕ) : commute f (f^[n]) :=
  (refl f).iterate_right n

theorem iterate_iterate_self (m n : ℕ) : commute (f^[m]) (f^[n]) :=
  (refl f).iterate_iterate m n

end Commute

theorem semiconj₂.iterate {f : α → α} {op : α → α → α} (hf : semiconj₂ f op op) (n : ℕ) : semiconj₂ (f^[n]) op op :=
  Nat.recOn n (semiconj₂.id_left op) fun n ihn => ihn.comp hf

variable(f)

theorem iterate_succ' (n : ℕ) : f^[n.succ] = f ∘ f^[n] :=
  by 
    rw [iterate_succ, (commute.self_iterate f n).comp_eq]

theorem iterate_succ_apply' (n : ℕ) (x : α) : (f^[n.succ]) x = f ((f^[n]) x) :=
  by 
    rw [iterate_succ']

theorem iterate_pred_comp_of_pos {n : ℕ} (hn : 0 < n) : f^[n.pred] ∘ f = f^[n] :=
  by 
    rw [←iterate_succ, Nat.succ_pred_eq_of_posₓ hn]

theorem comp_iterate_pred_of_pos {n : ℕ} (hn : 0 < n) : f ∘ f^[n.pred] = f^[n] :=
  by 
    rw [←iterate_succ', Nat.succ_pred_eq_of_posₓ hn]

/-- A recursor for the iterate of a function. -/
def iterate.rec (p : α → Sort _) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) (n : ℕ) : p ((f^[n]) a) :=
  Nat.rec ha
    (fun m =>
      by 
        rw [iterate_succ']
        exact h _)
    n

theorem iterate.rec_zero (p : α → Sort _) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) :
  iterate.rec p h ha 0 = ha :=
  rfl

variable{f}

theorem left_inverse.iterate {g : α → α} (hg : left_inverse g f) (n : ℕ) : left_inverse (g^[n]) (f^[n]) :=
  (Nat.recOn n fun _ => rfl)$
    fun n ihn =>
      by 
        rw [iterate_succ', iterate_succ]
        exact ihn.comp hg

theorem right_inverse.iterate {g : α → α} (hg : RightInverse g f) (n : ℕ) : RightInverse (g^[n]) (f^[n]) :=
  hg.iterate n

theorem iterate_comm (f : α → α) (m n : ℕ) : f^[n]^[m] = f^[m]^[n] :=
  (iterate_mul _ _ _).symm.trans
    (Eq.trans
      (by 
        rw [Nat.mul_comm])
      (iterate_mul _ _ _))

theorem iterate_commute (m n : ℕ) : commute (fun f : α → α => f^[m]) fun f => f^[n] :=
  fun f => iterate_comm f m n

end Function

