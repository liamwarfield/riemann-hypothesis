module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
noncomputable section

open Matrix Polynomial

namespace UpperTheory.V.GradeZeroInterpolatingElement

abbrev M4 (R : Type) : Type := Matrix (Fin 4) (Fin 4) R

def sgn : Fin 4 → ℤ := ![1, 1, -1, -1]

def lamW : Fin 4 → ℤ := ![1, 0, 1, 0]

def muW : Fin 4 → ℤ := ![1, 1, 0, 0]

def wt (i j : Fin 4) : ℤ × ℤ := (lamW i - lamW j, muW i - muW j)

def wAl : ℤ × ℤ := (1, 0)
def wBe : ℤ × ℤ := (-1, 1)
def wPs : ℤ × ℤ := (0, 1)
def wTh : ℤ × ℤ := (1, 1)

def oddRoots : Finset (ℤ × ℤ) := {wAl, -wAl, wBe, -wBe, wTh, -wTh}

def wts : Finset (ℤ × ℤ) := oddRoots ∪ {wPs, -wPs, 0}

theorem wt_mem (i j : Fin 4) : wt i j ∈ wts := by revert i j; decide

theorem wt_rev (i j : Fin 4) : wt j.rev i.rev = wt i j := by revert i j; decide

theorem wt_eq_zero (i j : Fin 4) : wt i j = 0 ↔ i = j := by revert i j; decide

variable {R R' : Type} [CommRing R] [CommRing R']

def adj (X : M4 R) : M4 R := Matrix.of fun i j => (sgn i * sgn j) • X j.rev i.rev

theorem adj_apply (X : M4 R) (i j : Fin 4) : adj X i j = (sgn i * sgn j) • X j.rev i.rev := rfl

def IsGSp (ν : R) (g : M4 R) : Prop := adj g * g = ν • (1 : M4 R)

def sp4 (R : Type) [CommRing R] : Submodule R (M4 R) where
  carrier := {X | adj X = -X}
  zero_mem' := by ext i j; simp [adj_apply]
  add_mem' {a b} ha hb := by
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [adj_apply, Matrix.neg_apply, Matrix.add_apply, smul_add] at *
    rw [h1, h2, neg_add]
  smul_mem' c a ha := by
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [adj_apply, Matrix.neg_apply, Matrix.smul_apply] at *
    rw [smul_comm, h1, smul_neg]

def spW (R : Type) [CommRing R] (w : ℤ × ℤ) : Submodule R (M4 R) :=
  sp4 R ⊓ ⨅ (i : Fin 4) (j : Fin 4) (_ : wt i j ≠ w), LinearMap.ker (Matrix.entryLinearMap R R i j)

def Xm (R : Type) [CommRing R] : M4 R := Matrix.single 2 0 1 + Matrix.single 3 1 1

def IsBlock (X : M4 R) : Prop := ∀ i j, lamW i ≠ lamW j → X i j = 0

def wv (t : Rˣ × Rˣ) (w : ℤ × ℤ) : Rˣ := t.1 ^ w.1 * t.2 ^ w.2

def tconj (t : Rˣ × Rˣ) (X : M4 R) : M4 R := Matrix.of fun i j => (wv t (wt i j) : R) * X i j

def prj (c : Fin 4 → R) (X : M4 R) (i : Fin 4) : M4 R :=
  aeval X (∏ j ∈ Finset.univ.erase i, (Polynomial.X - C (c j)) : R[X])

section Rep

variable {H : Type} [Group H]

def mapRep {n : Type} [Fintype n] [DecidableEq n] (f : R →+* R') (r : H →* Matrix n n R) : H →* Matrix n n R' :=
  (f.mapMatrix : Matrix n n R →+* Matrix n n R').toMonoidHom.comp r

@[simp] theorem mapRep_apply {n : Type} [Fintype n] [DecidableEq n] (f : R →+* R') (r : H →* Matrix n n R) (g : H) (i j : n) :
    mapRep f r g i j = f (r g i j) := rfl

def diagRep (χ : Fin 4 → H →* Rˣ) : H →* M4 R where
  toFun g := Matrix.diagonal fun i => (χ i g : R)
  map_one' := by simp
  map_mul' a b := by simp [Matrix.diagonal_mul_diagonal]

def mono (r : H →* M4 R) (w : ℤ × ℤ) : Set R :=
  {x | ∃ L : List (H × Fin 4 × Fin 4), (L.map fun a => wt a.2.1 a.2.2).sum = w ∧ x = (L.map fun a => r a.1 a.2.1 a.2.2).prod}

def Irr {n : Type} [Fintype n] [DecidableEq n] (r : H →* Matrix n n R) : Prop := Submodule.span R (Set.range r) = ⊤

def Ge (r : H →* M4 R) (i j : Fin 4) : Prop := ∃ g, r g i j ≠ 0

def DiagType (r : H →* M4 R) : Prop := ∀ i j, i ≠ j → Ge r i j → ¬ Ge r j i

def ixA : Fin 2 → Fin 4 := ![0, 2]

def IsConj4 (r r' : H →* M4 R) : Prop := ∃ u : (M4 R)ˣ, ∀ g, r' g = u * r g * (u⁻¹ : (M4 R)ˣ)

structure Ord (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R) : Prop where
  charpoly : (r s₀).charpoly = ∏ j, (Polynomial.X - C (ps j s₀))
  stable : ∀ g i j, i < j → prj (fun a => ps a s₀) (r s₀) j * r g * prj (fun a => ps a s₀) (r s₀) i = 0
  inert : ∀ s ∈ I, ∀ i, prj (fun a => ps a s₀) (r s₀) i * (r s - ps i s • (1 : M4 R)) * prj (fun a => ps a s₀) (r s₀) i = 0

end Rep

end UpperTheory.V.GradeZeroInterpolatingElement

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowLtSqMulOfPrimitiveCharPowEqOne
private theorem primitive_dyadic_character_ne_one (R : Type) [CommRing R] (m : ℕ)
    (ξ : DirichletCharacter R (2 ^ (m + 2))) (hξ : ξ.IsPrimitive) :
    ξ (1 + 2 ^ (m + 1)) ≠ 1 := by
  intro h
  have hd : 2 ^ (m + 1) ∣ 2 ^ (m + 2) := pow_dvd_pow 2 (by omega)
  have hf : ξ.FactorsThrough (2 ^ (m + 1)) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).2 fun x hx => ?_
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one,
      ZMod.cast_eq_val] at hx
    have hM : 1 < 2 ^ (m + 1) := Nat.one_lt_two_pow (by omega)
    have hx1 : ((x : ZMod (2 ^ (m + 2))).val : ZMod (2 ^ (m + 1))) = ((1 : ℕ) : ZMod (2 ^ (m + 1))) := by
      simpa using hx
    have hx2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hx1
    rw [Nat.mod_eq_of_lt hM] at hx2
    have hlt := ZMod.val_lt (x : ZMod (2 ^ (m + 2)))
    have h2 : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by ring
    have hq : (x : ZMod (2 ^ (m + 2))).val / 2 ^ (m + 1) < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      omega
    have hv := Nat.mod_add_div (x : ZMod (2 ^ (m + 2))).val (2 ^ (m + 1))
    rw [hx2] at hv
    have hx' : (x : ZMod (2 ^ (m + 2))) =
        ((1 + 2 ^ (m + 1) * ((x : ZMod (2 ^ (m + 2))).val / 2 ^ (m + 1)) : ℕ) :
          ZMod (2 ^ (m + 2))) := by
      rw [hv, ZMod.natCast_zmod_val]
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, hx']
    interval_cases hq' : (x : ZMod (2 ^ (m + 2))).val / 2 ^ (m + 1)
    · simp
    · push_cast
      simpa using h
  have hle : ξ.conductor ≤ 2 ^ (m + 1) := Nat.sInf_le hf
  rw [hξ] at hle
  have h2 : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by ring
  have : 0 < 2 ^ (m + 1) := by positivity
  omega

private theorem two_adic_unit_pow_two_pow (x k : ℕ) (j : ℕ) (hx : ∃ d, x = 1 + 2 ^ (k + 2) * (2 * d + 1)) :
    ∃ d, x ^ (2 ^ j) = 1 + 2 ^ (k + 2 + j) * (2 * d + 1) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + 2 ^ (k + j) * (2 * d + 1) ^ 2, ?_⟩
    rw [pow_succ 2 j, pow_mul, hd]
    ring

private theorem two_adic_unit_pow_odd (x k : ℕ) (w : ℕ) (hx : ∃ d, x = 1 + 2 ^ (k + 1) * (2 * d + 1)) :
    ∃ d, x ^ (2 * w + 1) = 1 + 2 ^ (k + 1) * (2 * d + 1) := by
  obtain ⟨c, hc⟩ := hx
  induction w with
  | zero => exact ⟨c, by simpa using hc⟩
  | succ w ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + ((2 * c + 1) + 2 ^ k * (2 * c + 1) ^ 2) * (1 + 2 ^ (k + 1) * (2 * d + 1)), ?_⟩
    have : x ^ (2 * (w + 1) + 1) = x ^ (2 * w + 1) * x ^ 2 := by ring
    rw [this, hd, hc]
    ring

theorem UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (ξ : DirichletCharacter O (2 ^ n)), ξ.IsPrimitive → ∀ v a u : ℕ, Odd v → 1 < v → Odd u → ξ (v : ZMod (2 ^ n)) ^ (2 ^ a * u) = 1 → 2 ^ n < v ^ 2 * 2 ^ a := by
  intro O _ _ n ξ hξ v a u hv hv1 hu h
  obtain ⟨t, ht⟩ := hv
  obtain ⟨u', hu'⟩ := hu
  have hv3 : 3 ≤ v := by omega
  have hpos : 0 < 2 ^ a := by positivity
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h1 : 2 ^ n ≤ 2 := by interval_cases n <;> norm_num
    have h2 : 9 ≤ v ^ 2 := by nlinarith
    nlinarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsq : v ^ 2 = 4 * (t * (t + 1)) + 1 := by rw [ht]; ring
  have hw : v ^ 2 - 1 ≠ 0 := by
    rw [hsq, Nat.add_sub_cancel]
    have : 0 < t := by omega
    positivity
  obtain ⟨s, r, hr, hsr⟩ := Nat.exists_eq_two_pow_mul_odd hw
  have hs : 2 ≤ s := by
    by_contra hs
    obtain ⟨e, he⟩ := hr
    rw [hsq, Nat.add_sub_cancel] at hsr
    generalize t * (t + 1) = P at hsr
    interval_cases s <;> omega
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  obtain ⟨d, rfl⟩ := hr
  have hW : v ^ 2 = 1 + 2 ^ (k + 1 + 1) * (2 * d + 1) := by
    have := Nat.eq_add_of_sub_eq (by omega) hsr
    rw [this]
    ring
  obtain ⟨d1, hd1⟩ := two_adic_unit_pow_odd (v ^ 2) (k + 1) u' ⟨d, hW⟩
  obtain ⟨d2, hd2⟩ := two_adic_unit_pow_two_pow ((v ^ 2) ^ (2 * u' + 1)) k a ⟨d1, by rw [hd1]⟩
  have hbig : m + 2 ≤ k + 2 + a := by
    by_contra hlt
    obtain ⟨d3, hd3⟩ := two_adic_unit_pow_two_pow (((v ^ 2) ^ (2 * u' + 1)) ^ 2 ^ a) (k + a) (m + 1 - (k + 2 + a))
      ⟨d2, by rw [hd2, show k + 2 + a = k + a + 2 by ring]⟩
    rw [show k + a + 2 + (m + 1 - (k + 2 + a)) = m + 1 by omega] at hd3
    apply primitive_dyadic_character_ne_one O m ξ hξ
    have hcast : ((((((v ^ 2) ^ (2 * u' + 1)) ^ 2 ^ a) ^ 2 ^ (m + 1 - (k + 2 + a)) : ℕ)) :
        ZMod (2 ^ (m + 2))) = 1 + 2 ^ (m + 1) := by
      rw [hd3]
      push_cast
      have h0 : (2 : ZMod (2 ^ (m + 2))) ^ (m + 2) = 0 := by
        rw [show (2 : ZMod (2 ^ (m + 2))) ^ (m + 2) = ((2 ^ (m + 2) : ℕ) : ZMod (2 ^ (m + 2))) by
          push_cast; rfl, ZMod.natCast_self]
      linear_combination (d3 : ZMod (2 ^ (m + 2))) * h0
    rw [← hcast]
    have hval : ((((((v ^ 2) ^ (2 * u' + 1)) ^ 2 ^ a) ^ 2 ^ (m + 1 - (k + 2 + a)) : ℕ)) :
        ZMod (2 ^ (m + 2))) = ((v : ZMod (2 ^ (m + 2))) ^ (2 ^ a * u)) ^ (2 * 2 ^ (m + 1 - (k + 2 + a))) := by
      rw [hu']
      push_cast
      ring
    rw [hval, map_pow, map_pow, h, one_pow]
  have hk : 2 ^ (k + 2) < v ^ 2 := by
    rw [hW]
    have : 2 ^ (k + 2) ≤ 2 ^ (k + 1 + 1) * (2 * d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  calc 2 ^ (m + 2) ≤ 2 ^ (k + 2 + a) := Nat.pow_le_pow_right (by norm_num) hbig
    _ = 2 ^ (k + 2) * 2 ^ a := by ring
    _ < v ^ 2 * 2 ^ a := Nat.mul_lt_mul_of_pos_right hk hpos
end
