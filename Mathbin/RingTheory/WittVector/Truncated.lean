/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.RingTheory.WittVector.InitTail

/-!

# Truncated Witt vectors

The ring of truncated Witt vectors (of length `n`) is a quotient of the ring of Witt vectors.
It retains the first `n` coefficients of each Witt vector.
In this file, we set up the basic quotient API for this ring.

The ring of Witt vectors is the projective limit of all the rings of truncated Witt vectors.

## Main declarations

- `truncated_witt_vector`: the underlying type of the ring of truncated Witt vectors
- `truncated_witt_vector.comm_ring`: the ring structure on truncated Witt vectors
- `witt_vector.truncate`: the quotient homomorphism that truncates a Witt vector,
  to obtain a truncated Witt vector
- `truncated_witt_vector.truncate`: the homomorphism that truncates
  a truncated Witt vector of length `n` to one of length `m` (for some `m â¤ n`)
- `witt_vector.lift`: the unique ring homomorphism into the ring of Witt vectors
  that is compatible with a family of ring homomorphisms to the truncated Witt vectors:
  this realizes the ring of Witt vectors as projective limit of the rings of truncated Witt vectors

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


open Function (Injective Surjective)

noncomputable section

variable {p : â} [hp : Fact p.Prime] (n : â) (R : Type _)

-- mathport name: Â«exprðÂ»
local notation "ð" => WittVector p

/-- A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated) Witt
vector operations.

`truncated_witt_vector p n R` takes a parameter `p : â` that is not used in the definition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `truncated_witt_vector p n R`.
(`truncated_witt_vector pâ n R` and `truncated_witt_vector pâ n R` are definitionally
equal as types but will have different ring operations.)
-/
-- type as `\bbW`
@[nolint unused_arguments]
def TruncatedWittVector (p : â) (n : â) (R : Type _) :=
  Finâ n â R

instance (p n : â) (R : Type _) [Inhabited R] : Inhabited (TruncatedWittVector p n R) :=
  â¨fun _ => defaultâ©

variable {n R}

namespace TruncatedWittVector

variable (p)

/-- Create a `truncated_witt_vector` from a vector `x`. -/
def mk (x : Finâ n â R) : TruncatedWittVector p n R :=
  x

variable {p}

/-- `x.coeff i` is the `i`th entry of `x`. -/
def coeff (i : Finâ n) (x : TruncatedWittVector p n R) : R :=
  x i

@[ext]
theorem ext {x y : TruncatedWittVector p n R} (h : â i, x.coeff i = y.coeff i) : x = y :=
  funext h

theorem ext_iff {x y : TruncatedWittVector p n R} : x = y â â i, x.coeff i = y.coeff i :=
  â¨fun h i => by
    rw [h], extâ©

@[simp]
theorem coeff_mk (x : Finâ n â R) (i : Finâ n) : (mk p x).coeff i = x i :=
  rfl

@[simp]
theorem mk_coeff (x : TruncatedWittVector p n R) : (mk p fun i => x.coeff i) = x := by
  ext i
  rw [coeff_mk]

variable [CommRingâ R]

/-- We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
def out (x : TruncatedWittVector p n R) : ð R :=
  (WittVector.mk p) fun i => if h : i < n then x.coeff â¨i, hâ© else 0

@[simp]
theorem coeff_out (x : TruncatedWittVector p n R) (i : Finâ n) : x.out.coeff i = x.coeff i := by
  rw [out, WittVector.coeff_mk, dif_pos i.is_lt, Finâ.eta]

theorem out_injective : Injective (@out p n R _) := by
  intro x y h
  ext i
  rw [WittVector.ext_iff] at h
  simpa only [â coeff_out] using h âi

end TruncatedWittVector

namespace WittVector

variable {p} (n)

section

/-- `truncate_fun n x` uses the first `n` entries of `x` to construct a `truncated_witt_vector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `witt_vector.truncate` -/
def truncateFun (x : ð R) : TruncatedWittVector p n R :=
  (TruncatedWittVector.mk p) fun i => x.coeff i

end

variable {n}

@[simp]
theorem coeff_truncate_fun (x : ð R) (i : Finâ n) : (truncateFun n x).coeff i = x.coeff i := by
  rw [truncate_fun, TruncatedWittVector.coeff_mk]

variable [CommRingâ R]

@[simp]
theorem out_truncate_fun (x : ð R) : (truncateFun n x).out = init n x := by
  ext i
  dsimp' [â TruncatedWittVector.out, â init, â select]
  split_ifs with hi
  swap
  Â· rfl
    
  rw [coeff_truncate_fun, Finâ.coe_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRingâ R]

@[simp]
theorem truncate_fun_out (x : TruncatedWittVector p n R) : x.out.truncateFun n = x := by
  simp only [â WittVector.truncateFun, â coeff_out, â mk_coeff]

open WittVector

variable (p n R)

include hp

instance : Zero (TruncatedWittVector p n R) :=
  â¨truncateFun n 0â©

instance : One (TruncatedWittVector p n R) :=
  â¨truncateFun n 1â©

instance : HasNatCast (TruncatedWittVector p n R) :=
  â¨fun i => truncateFun n iâ©

instance : HasIntCast (TruncatedWittVector p n R) :=
  â¨fun i => truncateFun n iâ©

instance : Add (TruncatedWittVector p n R) :=
  â¨fun x y => truncateFun n (x.out + y.out)â©

instance : Mul (TruncatedWittVector p n R) :=
  â¨fun x y => truncateFun n (x.out * y.out)â©

instance : Neg (TruncatedWittVector p n R) :=
  â¨fun x => truncateFun n (-x.out)â©

instance : Sub (TruncatedWittVector p n R) :=
  â¨fun x y => truncateFun n (x.out - y.out)â©

instance hasNatScalar : HasSmul â (TruncatedWittVector p n R) :=
  â¨fun m x => truncateFun n (m â¢ x.out)â©

instance hasIntScalar : HasSmul â¤ (TruncatedWittVector p n R) :=
  â¨fun m x => truncateFun n (m â¢ x.out)â©

instance hasNatPow : Pow (TruncatedWittVector p n R) â :=
  â¨fun x m => truncateFun n (x.out ^ m)â©

@[simp]
theorem coeff_zero (i : Finâ n) : (0 : TruncatedWittVector p n R).coeff i = 0 := by
  show coeff i (truncate_fun _ 0 : TruncatedWittVector p n R) = 0
  rw [coeff_truncate_fun, WittVector.zero_coeff]

end TruncatedWittVector

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- A macro tactic used to prove that `truncate_fun` respects ring operations. -/
unsafe def tactic.interactive.witt_truncate_fun_tac : tactic Unit :=
  sorry

namespace WittVector

variable (p n R)

variable [CommRingâ R]

theorem truncate_fun_surjective : Surjective (@truncateFun p n R) :=
  Function.RightInverse.surjective TruncatedWittVector.truncate_fun_out

include hp

@[simp]
theorem truncate_fun_zero : truncateFun n (0 : ð R) = 0 :=
  rfl

@[simp]
theorem truncate_fun_one : truncateFun n (1 : ð R) = 1 :=
  rfl

variable {p R}

@[simp]
theorem truncate_fun_add (x y : ð R) : truncateFun n (x + y) = truncateFun n x + truncateFun n y := by
  witt_truncate_fun_tac
  rw [init_add]

@[simp]
theorem truncate_fun_mul (x y : ð R) : truncateFun n (x * y) = truncateFun n x * truncateFun n y := by
  witt_truncate_fun_tac
  rw [init_mul]

theorem truncate_fun_neg (x : ð R) : truncateFun n (-x) = -truncateFun n x := by
  witt_truncate_fun_tac
  rw [init_neg]

theorem truncate_fun_sub (x y : ð R) : truncateFun n (x - y) = truncateFun n x - truncateFun n y := by
  witt_truncate_fun_tac
  rw [init_sub]

theorem truncate_fun_nsmul (x : ð R) (m : â) : truncateFun n (m â¢ x) = m â¢ truncateFun n x := by
  witt_truncate_fun_tac
  rw [init_nsmul]

theorem truncate_fun_zsmul (x : ð R) (m : â¤) : truncateFun n (m â¢ x) = m â¢ truncateFun n x := by
  witt_truncate_fun_tac
  rw [init_zsmul]

theorem truncate_fun_pow (x : ð R) (m : â) : truncateFun n (x ^ m) = truncateFun n x ^ m := by
  witt_truncate_fun_tac
  rw [init_pow]

theorem truncate_fun_nat_cast (m : â) : truncateFun n (m : ð R) = m :=
  rfl

theorem truncate_fun_int_cast (m : â¤) : truncateFun n (m : ð R) = m :=
  rfl

end WittVector

namespace TruncatedWittVector

open WittVector

variable (p n R)

variable [CommRingâ R]

include hp

instance : CommRingâ (TruncatedWittVector p n R) :=
  (truncate_fun_surjective p n R).CommRing _ (truncate_fun_zero p n R) (truncate_fun_one p n R) (truncate_fun_add n)
    (truncate_fun_mul n) (truncate_fun_neg n) (truncate_fun_sub n) (truncate_fun_nsmul n) (truncate_fun_zsmul n)
    (truncate_fun_pow n) (truncate_fun_nat_cast n) (truncate_fun_int_cast n)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (n)

variable [CommRingâ R]

include hp

/-- `truncate n` is a ring homomorphism that truncates `x` to its first `n` entries
to obtain a `truncated_witt_vector`, which has the same base `p` as `x`. -/
noncomputable def truncate : ð R â+* TruncatedWittVector p n R where
  toFun := truncateFun n
  map_zero' := truncate_fun_zero p n R
  map_add' := truncate_fun_add n
  map_one' := truncate_fun_one p n R
  map_mul' := truncate_fun_mul n

variable (p n R)

theorem truncate_surjective : Surjective (truncate n : ð R â TruncatedWittVector p n R) :=
  truncate_fun_surjective p n R

variable {p n R}

@[simp]
theorem coeff_truncate (x : ð R) (i : Finâ n) : (truncate n x).coeff i = x.coeff i :=
  coeff_truncate_fun _ _

variable (n)

theorem mem_ker_truncate (x : ð R) : x â (@truncate p _ n R _).ker â â, â i < n, â, x.coeff i = 0 := by
  simp only [â RingHom.mem_ker, â truncate, â truncate_fun, â RingHom.coe_mk, â TruncatedWittVector.ext_iff, â
    TruncatedWittVector.coeff_mk, â coeff_zero]
  exact Subtype.forall

variable (p)

@[simp]
theorem truncate_mk (f : â â R) : truncate n (mk p f) = TruncatedWittVector.mk _ fun k => f k := by
  ext i
  rw [coeff_truncate, coeff_mk, TruncatedWittVector.coeff_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRingâ R]

include hp

/-- A ring homomorphism that truncates a truncated Witt vector of length `m` to
a truncated Witt vector of length `n`, for `n â¤ m`.
-/
def truncate {m : â} (hm : n â¤ m) : TruncatedWittVector p m R â+* TruncatedWittVector p n R :=
  RingHom.liftOfRightInverse (WittVector.truncate m) out truncate_fun_out
    â¨WittVector.truncate n, by
      intro x
      simp only [â WittVector.mem_ker_truncate]
      intro h i hi
      exact h i (lt_of_lt_of_leâ hi hm)â©

@[simp]
theorem truncate_comp_witt_vector_truncate {m : â} (hm : n â¤ m) :
    (@truncate p _ n R _ m hm).comp (WittVector.truncate m) = WittVector.truncate n :=
  RingHom.lift_of_right_inverse_comp _ _ _ _

@[simp]
theorem truncate_witt_vector_truncate {m : â} (hm : n â¤ m) (x : ð R) :
    truncate hm (WittVector.truncate m x) = WittVector.truncate n x :=
  RingHom.lift_of_right_inverse_comp_apply _ _ _ _ _

@[simp]
theorem truncate_truncate {nâ nâ nâ : â} (h1 : nâ â¤ nâ) (h2 : nâ â¤ nâ) (x : TruncatedWittVector p nâ R) :
    (truncate h1) (truncate h2 x) = truncate (h1.trans h2) x := by
  obtain â¨x, rflâ© := WittVector.truncate_surjective p nâ R x
  simp only [â truncate_witt_vector_truncate]

@[simp]
theorem truncate_comp {nâ nâ nâ : â} (h1 : nâ â¤ nâ) (h2 : nâ â¤ nâ) :
    (@truncate p _ _ R _ _ h1).comp (truncate h2) = truncate (h1.trans h2) := by
  ext1 x
  simp only [â truncate_truncate, â Function.comp_app, â RingHom.coe_comp]

theorem truncate_surjective {m : â} (hm : n â¤ m) : Surjective (@truncate p _ _ R _ _ hm) := by
  intro x
  obtain â¨x, rflâ© := WittVector.truncate_surjective p _ R x
  exact â¨WittVector.truncate _ x, truncate_witt_vector_truncate _ _â©

@[simp]
theorem coeff_truncate {m : â} (hm : n â¤ m) (i : Finâ n) (x : TruncatedWittVector p m R) :
    (truncate hm x).coeff i = x.coeff (Finâ.castLe hm i) := by
  obtain â¨y, rflâ© := WittVector.truncate_surjective p _ _ x
  simp only [â truncate_witt_vector_truncate, â WittVector.coeff_truncate, â Finâ.coe_cast_le]

section Fintype

omit hp

instance {R : Type _} [Fintype R] : Fintype (TruncatedWittVector p n R) :=
  Pi.fintype

variable (p n R)

theorem card {R : Type _} [Fintype R] : Fintype.card (TruncatedWittVector p n R) = Fintype.card R ^ n := by
  simp only [â TruncatedWittVector, â Fintype.card_fin, â Fintype.card_fun]

end Fintype

theorem infi_ker_truncate : (â¨ i : â, (@WittVector.truncate p _ i R _).ker) = â¥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext
  simp only [â WittVector.mem_ker_truncate, â Ideal.mem_infi, â WittVector.zero_coeff] at hxâ¢
  exact hx _ _ (Nat.lt_succ_selfâ _)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector hiding truncate coeff

section lift

variable [CommRingâ R]

variable {S : Type _} [Semiringâ S]

variable (f : â k : â, S â+* TruncatedWittVector p k R)

variable (f_compat : â (kâ kâ : â) (hk : kâ â¤ kâ), (TruncatedWittVector.truncate hk).comp (f kâ) = f kâ)

variable {p R}

variable (n)

/-- Given a family `fâ : S â truncated_witt_vector p k R` and `s : S`, we produce a Witt vector by
defining the `k`th entry to be the final entry of `fâ s`.
-/
def liftFun (s : S) : ð R :=
  (WittVector.mk p) fun k => TruncatedWittVector.coeff (Finâ.last k) (f (k + 1) s)

variable {f}

include f_compat

@[simp]
theorem truncate_lift_fun (s : S) : WittVector.truncate n (liftFun f s) = f n s := by
  ext i
  simp only [â lift_fun, â TruncatedWittVector.coeff_mk, â WittVector.truncate_mk]
  rw [â f_compat (i + 1) n i.is_lt, RingHom.comp_apply, TruncatedWittVector.coeff_truncate]
  -- this is a bit unfortunate
  congr with _
  simp only [â Finâ.coe_last, â Finâ.coe_cast_le]

variable (f)

/-- Given compatible ring homs from `S` into `truncated_witt_vector n` for each `n`, we can lift these
to a ring hom `S â ð R`.

`lift` defines the universal property of `ð R` as the inverse limit of `truncated_witt_vector n`.
-/
def lift : S â+* ð R := by
  refine_struct { toFun := lift_fun f } <;>
    Â· intros
      rw [â sub_eq_zero, â Ideal.mem_bot, â infi_ker_truncate, Ideal.mem_infi]
      simp [â RingHom.mem_ker, â f_compat]
      

variable {f}

@[simp]
theorem truncate_lift (s : S) : WittVector.truncate n (lift _ f_compat s) = f n s :=
  truncate_lift_fun _ f_compat s

@[simp]
theorem truncate_comp_lift : (WittVector.truncate n).comp (lift _ f_compat) = f n := by
  ext1
  rw [RingHom.comp_apply, truncate_lift]

/-- The uniqueness part of the universal property of `ð R`. -/
theorem lift_unique (g : S â+* ð R) (g_compat : â k, (WittVector.truncate k).comp g = f k) : lift _ f_compat = g := by
  ext1 x
  rw [â sub_eq_zero, â Ideal.mem_bot, â infi_ker_truncate, Ideal.mem_infi]
  intro i
  simp only [â RingHom.mem_ker, â g_compat, RingHom.comp_apply, â truncate_comp_lift, â RingHom.map_sub, â sub_self]

omit f_compat

include hp

/-- The universal property of `ð R` as projective limit of truncated Witt vector rings. -/
@[simps]
def liftEquiv :
    { f : â k, S â+* TruncatedWittVector p k R //
        â (kâ kâ) (hk : kâ â¤ kâ), (TruncatedWittVector.truncate hk).comp (f kâ) = f kâ } â
      (S â+* ð R) where
  toFun := fun f => lift f.1 f.2
  invFun := fun g =>
    â¨fun k => (truncate k).comp g, by
      intro _ _ h
      simp only [RingHom.comp_assoc, â truncate_comp_witt_vector_truncate]â©
  left_inv := by
    rintro â¨f, hfâ©
    simp only [â truncate_comp_lift]
  right_inv := fun g => (lift_unique _ _) fun _ => rfl

theorem hom_ext (gâ gâ : S â+* ð R) (h : â k, (truncate k).comp gâ = (truncate k).comp gâ) : gâ = gâ :=
  liftEquiv.symm.Injective <| Subtype.ext <| funext h

end lift

end WittVector

