module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofSpanCondition

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TranslationZeroModeLift
namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

def Uq {dim : (E →+* ℂ) → ℕ} (q : ℕ) (a : Vsp dim) (F : Vsp dim → ℂ) : Vsp dim → ℂ :=
  fun v => cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)

def Uh (X : PT E) (q : ℕ) (a : Vsp X.dim) (F : Vsp X.dim → ℂ) : Vsp X.dim → ℂ :=
  fun v => (X.eps a : ℂ) ^ q * Uq q a F v

def F0 {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (q : ℕ)
    (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ) : Vsp dim → ℂ :=
  fun v => cexp ((q * Real.pi / 2 : ℂ) * S (IR I) v) * β (wmap (IR I) v)

theorem Uh_add (X : PT E) (q : ℕ) {a b : Vsp X.dim} (ha : a ∈ X.L) (hb : b ∈ X.L) (F : Vsp X.dim → ℂ) :
    Uh X q a (Uh X q b F) = Uh X q (a + b) F := by
  funext v
  obtain ⟨k, hk⟩ := X.integral a b ha hb
  have hε := X.eps_add a ha b hb
  rw [hk] at hε
  have hsin : Real.sin (Real.pi * k) = 0 := by
    rw [mul_comm]; exact Real.sin_int_mul_pi k
  have hεC : (X.eps (a + b) : ℂ) = X.eps a * X.eps b * (Real.cos (Real.pi * k) : ℝ) := by
    exact_mod_cast hε

  have h1 : Hf v (a + b) = Hf v a + Hf v b := by
    simp only [Hf, PiLp.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have h2 : Hf (v - a) b = Hf v b - Hf a b := by
    simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have h3 : Hf (a + b) (a + b) = Hf a a + Hf a b + Hf b a + Hf b b := by
    simp only [Hf, PiLp.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]
    ring
  have h4 : Hf b a = (starRingEnd ℂ) (Hf a b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Hf, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h5 : Hf b a - Hf a b = -(2 * (k : ℂ) * Complex.I) := by
    rw [h4]
    have hz := Complex.re_add_im (Hf a b)
    rw [← hz, hk]
    simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hexp : Complex.exp (-(q * Real.pi * (2 * (k : ℂ) * Complex.I)) / 2) =
      ((Real.cos (Real.pi * k) : ℝ) : ℂ) ^ q := by
    have : -(q * Real.pi * (2 * (k : ℂ) * Complex.I)) / 2 = q * (-((Real.pi * k : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_nat_mul, Complex.exp_mul_I]
    congr 1
    rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hsin]
    simp
  have hAB : Complex.exp ((q : ℂ) * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) *
      Complex.exp ((q : ℂ) * Real.pi * (Hf v b - Hf a b) - q * Real.pi * Hf b b / 2) =
      Complex.exp ((q : ℂ) * Real.pi * (Hf v a + Hf v b) -
        q * Real.pi * (Hf a a + Hf a b + Hf b a + Hf b b) / 2) *
        ((Real.cos (Real.pi * k) : ℝ) : ℂ) ^ q := by
    rw [← Complex.exp_add, ← hexp, ← Complex.exp_add]
    congr 1
    linear_combination ((q : ℂ) * Real.pi / 2) * h5
  simp only [Uh, Uq]
  rw [sub_sub, hεC, h1, h2, h3]
  linear_combination ((X.eps a : ℂ) ^ q * (X.eps b : ℂ) ^ q * F (v - (a + b))) * hAB

theorem Uh_shift (X : PT E) (q : ℕ) (a : Vsp X.dim) (G : Vsp X.dim → ℂ) (v : Vsp X.dim) :
    Uh X q a G (v + a) = (X.eps a : ℂ) ^ q * cexp (q * Real.pi * Hf v a + q * Real.pi * Hf a a / 2) * G v := by
  have hH : Hf (v + a) a = Hf v a + Hf a a := by
    simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
  simp only [Uh, Uq, add_sub_cancel_right, hH]
  have he : (q : ℂ) * Real.pi * (Hf v a + Hf a a) - q * Real.pi * Hf a a / 2 =
      q * Real.pi * Hf v a + q * Real.pi * Hf a a / 2 := by ring
  rw [he]; ring

section F0sec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (q : ℕ) {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ}
  (hβ : β ∈ (YB hI hP q).Sec q)
include hI hβ

theorem zeroModeLift_add_lattice {x : Vsp X.dim} (hx : x ∈ Ip X I) (v : Vsp X.dim) :
    F0 I q β (v + x) = (X.eps x : ℂ) ^ q * cexp (q * Real.pi * Hf v x + q * Real.pi * Hf x x / 2) * F0 I q β v := by
  unfold GT.Sec at hβ
  obtain ⟨-, hsec⟩ := hβ
  have hγ : wmap (IR I) x ∈ lat (YB hI hP q).b := by
    show wmap (IR I) x ∈ lat (bB hI hP)
    rw [lat_bB]
    exact wmap_mem_GB hx
  have h1 := hsec _ hγ (wmap (IR I) v)
  rw [show (YB hI hP q).ka = kaB X I q from rfl, kaB_wmap hI _ hx] at h1
  push_cast at h1
  have hz : ∀ k, z (IR I) k (v + x) = z (IR I) k v + z (IR I) k x := by
    intro k
    first
    | (simp only [z]; rw [Hf_add_l])
    | simp [z, Hf_add_l]
  have hzr : ∀ k, (starRingEnd ℂ) (z (IR I) k x) = z (IR I) k x := fun k =>
    Complex.conj_eq_iff_im.mpr (z_im_Ip hx k)
  have hd1 := Hf_decomp (K := IR I) (hK_of hI) v x
  have hd2 := Hf_decomp (K := IR I) (hK_of hI) x x
  unfold F0 S
  rw [map_add (f := _), h1, Hf_wmap (hK_of hI), Hf_wmap (hK_of hI), hd1, hd2]
  simp only [hz, hzr]
  have hexp : ∀ a b c d : ℂ, a + b = c + d → cexp a * cexp b = cexp c * cexp d := by
    intro a b c d h
    rw [← Complex.exp_add, ← Complex.exp_add, h]
  have hs : ∑ k, (z (IR I) k v + z (IR I) k x) ^ 2 = ∑ k, z (IR I) k v ^ 2 +
      2 * ∑ k, z (IR I) k v * z (IR I) k x + ∑ k, z (IR I) k x * z (IR I) k x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have key := hexp ((q : ℂ) * Real.pi / 2 * ∑ k, (z (IR I) k v + z (IR I) k x) ^ 2)
    ((q : ℂ) * Real.pi * Hf (p2 (IR I) v) (p2 (IR I) x) +
      q * Real.pi * Hf (p2 (IR I) x) (p2 (IR I) x) / 2)
    ((q : ℂ) * Real.pi * (∑ k, z (IR I) k v * z (IR I) k x + Hf (p2 (IR I) v) (p2 (IR I) x)) +
      q * Real.pi * (∑ k, z (IR I) k x * z (IR I) k x + Hf (p2 (IR I) x) (p2 (IR I) x)) / 2)
    ((q : ℂ) * Real.pi / 2 * ∑ k, z (IR I) k v ^ 2) (by rw [hs]; ring)
  linear_combination ((X.eps x : ℂ) ^ q * β (wmap (IR I) v)) * key

theorem translation_zeroModeLift {x : Vsp X.dim} (hx : x ∈ Ip X I) : Uh X q x (F0 I q β) = F0 I q β := by
  funext v
  have h := zeroModeLift_add_lattice hI hP q hβ hx (v - x)
  rw [sub_add_cancel] at h
  have h2 : Hf (v - x) x = Hf v x - Hf x x := by
    simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [h2] at h
  simp only [Uh, Uq]
  rw [h]
  have he : (q : ℂ) * Real.pi * (Hf v x - Hf x x) + q * Real.pi * Hf x x / 2 =
      q * Real.pi * Hf v x - q * Real.pi * Hf x x / 2 := by ring
  rw [he]; ring

end F0sec

def NIp (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Submodule ℤ X.L := (Ip X I).comap X.L.subtype

abbrev Qc (X : PT E) (I : Submodule ℤ (Vsp X.dim)) := X.L ⧸ NIp X I

def Tm (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (γ : X.L) : Vsp X.dim → ℂ :=
  Uh X q γ (F0 I q β)

def Tc (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (c : Qc X I) : Vsp X.dim → ℂ :=
  Tm X I q β (Quotient.out c)

def sP (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (v : Vsp X.dim) : ℂ :=
  ∑' c : Qc X I, Tc X I q β c v

section Tsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (q : ℕ) {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ}
  (hβ : β ∈ (YB hI hP q).Sec q)
include hI hβ

theorem Tm_congr {γ γ' : X.L} (h : γ - γ' ∈ NIp X I) : Tm X I q β γ = Tm X I q β γ' := by
  have hd : ((γ - γ' : X.L) : Vsp X.dim) ∈ Ip X I := h
  unfold Tm
  have e : (γ : Vsp X.dim) = (γ' : Vsp X.dim) + ((γ - γ' : X.L) : Vsp X.dim) := by
    simp
  rw [e, ← Uh_add X q γ'.2 (γ - γ').2, translation_zeroModeLift hI hP q hβ hd]

theorem Tc_mk (γ : X.L) : Tc X I q β (Submodule.Quotient.mk γ) = Tm X I q β γ := by
  unfold Tc
  apply Tm_congr hI hP q hβ
  rw [← Submodule.Quotient.eq]
  first
  | exact Quotient.out_eq _
  | exact Quotient.out_eq' _
  | simp

theorem Tc_shift (c : Qc X I) (γ0 : X.L) (v : Vsp X.dim) :
    Tc X I q β c (v + (γ0 : Vsp X.dim)) = (X.eps (γ0 : Vsp X.dim) : ℂ) ^ q *
      cexp (q * Real.pi * Hf v (γ0 : Vsp X.dim) + q * Real.pi * Hf (γ0 : Vsp X.dim) γ0 / 2) *
        Tc X I q β (c - Submodule.Quotient.mk γ0) v := by
  have hc : c - Submodule.Quotient.mk γ0 = Submodule.Quotient.mk (Quotient.out c - γ0) := by
    rw [Submodule.Quotient.mk_sub]
    congr 1
    exact (Quotient.out_eq c).symm
  rw [hc, Tc_mk hI hP q hβ]
  unfold Tc Tm
  have e : ((Quotient.out c : X.L) : Vsp X.dim) =
      (γ0 : Vsp X.dim) + ((Quotient.out c - γ0 : X.L) : Vsp X.dim) := by
    simp
  rw [e, ← Uh_add X q γ0.2 (Quotient.out c - γ0).2, Uh_shift]

theorem sP_shift (γ0 : X.L) (v : Vsp X.dim) :
    sP X I q β (v + (γ0 : Vsp X.dim)) = (X.eps (γ0 : Vsp X.dim) : ℂ) ^ q *
      cexp (q * Real.pi * Hf v (γ0 : Vsp X.dim) + q * Real.pi * Hf (γ0 : Vsp X.dim) γ0 / 2) *
        sP X I q β v := by
  unfold sP
  simp only [Tc_shift hI hP q hβ]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subRight (Submodule.Quotient.mk γ0 : Qc X I)).tsum_eq (fun c => Tc X I q β c v)

end Tsec

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofFinrankIRLe
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem tof_shell_term (d k : ℕ) (hd : 2 ≤ d) :
    (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      (3 * (d : ℝ)) ^ d * (Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k) := by
  have hpi := Real.pi_gt_three
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hE : Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k =
      Real.exp (-1 + k * (1 - Real.pi / 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
  rw [hE]
  have key : (3 * ((k : ℝ) + 1)) ^ d ≤
      (3 * (d : ℝ)) ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hdd : (4 : ℝ) ≤ (d : ℝ) ^ d := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ (d : ℝ) ^ 2 := by gcongr
          _ ≤ (d : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
      have hQ : Real.pi / 2 * ((0 : ℕ) : ℝ) ^ 2 + (-1 + ((0 : ℕ) : ℝ) * (1 - Real.pi / 2)) = -1 := by
        simp
      rw [hQ, Real.exp_neg]
      have h1 : (1 : ℝ) ≤ (d : ℝ) ^ d * (Real.exp 1)⁻¹ := by
        rw [le_mul_inv_iff₀ (Real.exp_pos 1)]
        linarith
      calc (3 * (((0 : ℕ) : ℝ) + 1)) ^ d = 3 ^ d * 1 := by simp
        _ ≤ 3 ^ d * ((d : ℝ) ^ d * (Real.exp 1)⁻¹) := by gcongr
        _ = (3 * (d : ℝ)) ^ d * (Real.exp 1)⁻¹ := by rw [mul_pow]; ring
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      by_cases hkd : k + 1 ≤ d
      · have hkd' : (k : ℝ) + 1 ≤ d := by exact_mod_cast hkd
        have h1 : (3 * ((k : ℝ) + 1)) ^ d ≤ (3 * (d : ℝ)) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
        have h2 : 0 ≤ Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)) := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2)
            (by linarith : (0 : ℝ) ≤ k)) (by linarith : (0 : ℝ) ≤ k - 1)]
        calc (3 * ((k : ℝ) + 1)) ^ d ≤ (3 * (d : ℝ)) ^ d := h1
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_exp h2)
      · have hdk : (d : ℝ) ≤ k := by exact_mod_cast (by omega : d ≤ k)
        have hk2 : (2 : ℝ) ≤ k := le_trans hd' hdk
        have h1 : ((k : ℝ) + 1) ^ d ≤ Real.exp ((k : ℝ) * k) := by
          calc ((k : ℝ) + 1) ^ d ≤ (Real.exp k) ^ d :=
                pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (k : ℝ)]) d
            _ = Real.exp (d * k) := by rw [← Real.exp_nat_mul]
            _ ≤ Real.exp (k * k) := Real.exp_le_exp.mpr (by nlinarith)
        have h2 : (k : ℝ) * k ≤ Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)) := by
          have hkk : 2 ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
          have hpp : (1 : ℝ) / 2 ≤ Real.pi / 2 - 1 := by linarith
          nlinarith [mul_le_mul hpp hkk (by norm_num) (by linarith)]
        have h3 : (1 : ℝ) ≤ (d : ℝ) ^ d := one_le_pow₀ (by linarith)
        calc (3 * ((k : ℝ) + 1)) ^ d = 3 ^ d * ((k : ℝ) + 1) ^ d := mul_pow _ _ _
          _ ≤ 3 ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) := by
            gcongr
            exact h1.trans (Real.exp_le_exp.mpr h2)
          _ ≤ 3 ^ d * ((d : ℝ) ^ d *
              Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)))) := by
            gcongr
            exact le_mul_of_one_le_left (Real.exp_pos _).le h3
          _ = _ := by rw [mul_pow]; ring
  have hexp : Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) *
      Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) = Real.exp (-1 + k * (1 - Real.pi / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc _ ≤ (3 * (d : ℝ)) ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) *
        Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, hexp]

theorem tof_shell_sum (d K : ℕ) (hd : 2 ≤ d) :
    ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      2 * (3 * (d : ℝ)) ^ d := by
  set r := Real.exp (1 - Real.pi / 2) with hr
  have hpi := Real.pi_gt_three
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 2 / 3 := by
    have h := Real.add_one_le_exp (Real.pi / 2 - 1)
    have hrr : r * Real.exp (Real.pi / 2 - 1) = 1 := by
      rw [hr, ← Real.exp_add]
      simp
    nlinarith
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have hrr : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      simp
    have := Real.exp_pos (-1)
    nlinarith
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range K, r ^ k := Finset.sum_nonneg (fun k _ => pow_nonneg hr0.le k)
  have hS : ∑ k ∈ Finset.range K, r ^ k ≤ 3 := by
    have h := geom_sum_mul r K
    have : 0 ≤ r ^ K := by positivity
    nlinarith
  have hd0 : (0 : ℝ) ≤ (3 * (d : ℝ)) ^ d := by positivity
  calc ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.range K, (3 * (d : ℝ)) ^ d * (Real.exp (-1) * r ^ k) :=
        Finset.sum_le_sum (fun k _ => tof_shell_term d k hd)
    _ = (3 * (d : ℝ)) ^ d * Real.exp (-1) * ∑ k ∈ Finset.range K, r ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
    _ ≤ (3 * (d : ℝ)) ^ d * (1 / 2) * 3 := by gcongr
    _ ≤ 2 * (3 * (d : ℝ)) ^ d := by nlinarith

theorem tof_uMap_sep [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {x x' : Vsp X.dim} (hx : x ∈ X.L) (hx' : x' ∈ X.L)
    (hne : uMap I x ≠ uMap I x') : 1 ≤ ‖uMap I x - uMap I x'‖ := by
  have hsub : uMap I x - uMap I x' = uMap I (x - x') := (map_sub (uMap I) x x').symm
  have hne' : uMap I (x - x') ≠ 0 := by
    rw [← hsub]
    exact sub_ne_zero.mpr hne
  have hb := hI.sep (x - x') (X.L.sub_mem hx hx') (uMap I (x - x')) (isU_uMap I (x - x')) hne'
  have h1 : (1 : ℝ) ≤ ‖uMap I (x - x')‖ ^ 2 := le_trans P.C2 hb
  rw [hsub]
  by_contra hlt
  have hlt' : ‖uMap I (x - x')‖ < 1 := lt_of_not_ge hlt
  have h0 := norm_nonneg (uMap I (x - x'))
  nlinarith

theorem tof_finrank_IR_le [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
  obtain ⟨ρ, hρ, h⟩ := hI.rank
  rw [h]
  unfold dstar
  exact Nat.mul_le_mul_left _ hρ

theorem tof_two_le_dstar {X : PT E} {DF : ℕ} (P : Par X DF) : 2 ≤ dstar (E := E) P.m := by
  have h1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have h2 := P.hm1
  unfold dstar
  calc 2 = 2 * 1 * 1 := by norm_num
    _ ≤ 2 * PT.f E * P.m := by gcongr

theorem tof_sep_sum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) :
    ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m := by
  classical
  set d := dstar (E := E) P.m with hd
  have hd2 : 2 ≤ d := tof_two_le_dstar P
  have hDd : Module.finrank ℝ (IR I) ≤ d := tof_finrank_IR_le P hI
  have hyR : ∀ y ∈ F, y ∈ IR I := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hF y hy
    exact (IR I).starProjection_apply_mem _
  let e := (stdOrthonormalBasis ℝ (IR I)).repr
  let g : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ (IR I))) := fun y =>
    e ⟨(IR I).starProjection (y - u), (IR I).starProjection_apply_mem _⟩
  have hproj : ∀ y ∈ F, (IR I).starProjection (y - u) = y - u := fun y hy =>
    (Submodule.starProjection_eq_self_iff).mpr ((IR I).sub_mem (hyR y hy) hu)
  have hgn : ∀ y ∈ F, ‖g y‖ = ‖u - y‖ := by
    intro y hy
    simp only [g, LinearIsometryEquiv.norm_map, Submodule.coe_norm, hproj y hy]
    rw [norm_sub_rev]
  have hgd : ∀ y ∈ F, ∀ y' ∈ F, dist (g y) (g y') = ‖y - y'‖ := by
    intro y hy y' hy'
    rw [dist_eq_norm]
    simp only [g, ← map_sub, LinearIsometryEquiv.norm_map]
    simp only [Submodule.coe_norm, Submodule.coe_sub, hproj y hy, hproj y' hy']
    congr 1
    abel
  have hsep : ∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → 1 ≤ ‖y - y'‖ := by
    intro y hy y' hy' hne
    obtain ⟨x, hx, rfl⟩ := hF y hy
    obtain ⟨x', hx', rfl⟩ := hF y' hy'
    exact tof_uMap_sep P hI hx hx' hne
  set K := (F.sup fun y => ⌊‖u - y‖⌋₊) + 1 with hK
  have hmaps : ∀ y ∈ F, ⌊‖u - y‖⌋₊ ∈ Finset.range K := by
    intro y hy
    rw [Finset.mem_range, hK]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun y => ⌊‖u - y‖⌋₊) hy)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (tof_shell_sum d K hd2)
  set Fk := F.filter (fun y => ⌊‖u - y‖⌋₊ = k) with hFk
  have hFkF : ∀ y ∈ Fk, y ∈ F := fun y hy => (Finset.mem_filter.mp hy).1
  have hterm : ∀ y ∈ Fk, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
    intro y hy
    have hk : ⌊‖u - y‖⌋₊ = k := (Finset.mem_filter.mp hy).2
    have hle : (k : ℝ) ≤ ‖u - y‖ := by
      rw [← hk]
      exact Nat.floor_le (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have : (k : ℝ) ^ 2 ≤ ‖u - y‖ ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hle 2
    nlinarith [Real.pi_pos]
  have hinj : Set.InjOn g Fk := by
    intro y hy y' hy' hgg
    by_contra hne
    have h1 := hsep y (hFkF y hy) y' (hFkF y' hy') hne
    have h2 := hgd y (hFkF y hy) y' (hFkF y' hy')
    rw [hgg, dist_self] at h2
    linarith
  have hcard : (Fk.card : ℝ) ≤ (3 * ((k : ℝ) + 1)) ^ Module.finrank ℝ (IR I) := by
    rw [← Finset.card_image_of_injOn hinj]
    have hpk := hP (Module.finrank ℝ (IR I)) (Fk.image g) 1 ((k : ℝ) + 1) one_pos
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by
        intro p hp
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        rw [hgn y (hFkF y hy)]
        have hk : ⌊‖u - y‖⌋₊ = k := (Finset.mem_filter.mp hy).2
        rw [← hk]
        exact (Nat.lt_floor_add_one _).le)
      (by
        intro p hp p' hp' hne
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hp'
        rw [hgd y (hFkF y hy) y' (hFkF y' hy')]
        exact hsep y (hFkF y hy) y' (hFkF y' hy') (fun h => hne (by rw [h])))
    simpa using hpk
  calc ∑ y ∈ Fk, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2)
      ≤ ∑ y ∈ Fk, Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (Fk.card : ℝ) * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * ((k : ℝ) + 1)) ^ Module.finrank ℝ (IR I) * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        gcongr
    _ ≤ (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        gcongr
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofUMapSqSmul
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def PerFactor {X : PT E} {DF : ℕ} (P : Par X DF) (I : Submodule ℤ (Vsp X.dim))
    (s : (Fin 1 → Vsp X.dim) → ℂ) : Prop :=
  ∀ w : Vsp X.dim, ∃ y ∈ X.L, Real.sqrt (X.ptN2 1 s fun _ => w) / Real.sqrt (X.l2 1 s) ≤
    Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y‖ ^ 2)

theorem Par_ka0_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ka0 := by
  have h : (0 : ℝ) ≤ PT.rd E := by linarith [P.hrd]
  have hR : (0 : ℝ) ≤ RR (E := E) := by
    unfold RR
    exact pow_nonneg h 7
  unfold Par.ka0
  exact mul_nonneg (mul_nonneg (by norm_num) hR) (sq_nonneg _)

theorem tof_uMap_sq_smul {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (r1 : ℕ) (a y : Vsp dim) :
    ‖uMap I (((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y)‖ ^ 2 =
      (r1 : ℝ) ^ 4 * ‖uMap I a - uMap I y‖ ^ 2 := by
  have h : ((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y = ((r1 : ℝ) ^ 2) • (a - y) := by
    first
    | (rw [← smul_sub, ← Complex.coe_smul, Complex.ofReal_pow, Complex.ofReal_natCast])
    | (rw [← smul_sub]; norm_cast)
    | (rw [← smul_sub, ← Complex.coe_smul]; push_cast; rfl)
  rw [h, map_smul, map_sub, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  ring

theorem t_assemble [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hpf : PerFactor P I s)
    (r1 : ℕ) (hr1 : 2 ≤ r1) (a : Fin X.r → Vsp X.dim) (ha : ∀ j, ((r1 : ℂ) ^ 2) • a j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) (hph : 0 < P.ph) :
    ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
  choose y hyL hb using fun j => hpf (a j)
  set C : ℝ := Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) with hC
  set D : Fin X.r → ℝ := fun j => ‖uMap I (a j) - uMap I (y j)‖ ^ 2 with hD
  have hkp : 0 ≤ P.ka0 * P.ph := mul_nonneg (Par_ka0_nonneg P) hph.le
  have h1 : ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) :=
    Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hb j)
  have h2 : ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) =
      C ^ X.r * Real.exp (-(Real.pi / 2) * ∑ j, D j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, Finset.mul_sum]
  have h3 : C ^ X.r = Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) := by
    rw [hC, mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast ((P.ka0 * P.ph) ^ _),
      ← Real.rpow_mul hkp, Par.p3]
    congr 2; ring

  set xb : Fin X.r → Vsp X.dim := fun j => ((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • y j with hxb
  have hxL : ∀ j, xb j ∈ X.L ∧ IsU I (xb j) (uMap I (xb j)) := by
    intro j
    refine ⟨X.L.sub_mem (ha j) ?_, isU_uMap I _⟩
    have : ((r1 : ℂ) ^ 2) • y j = (r1 ^ 2 : ℕ) • y j := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; push_cast; rfl
    rw [this]; exact X.L.nsmul_mem (hyL j) _
  have hspan := tof_span_condition (X := X) I r1 hr1 a y hyL hgen
  have hu2 := hI.u2 X.r xb (fun j => uMap I (xb j)) hxL hspan
  have hsum : ∑ j, ‖uMap I (xb j)‖ ^ 2 / 2 = (r1 : ℝ) ^ 4 / 2 * ∑ j, D j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxb]; dsimp only
    rw [tof_uMap_sq_smul]; ring
  rw [hsum] at hu2
  have hr4 : (0 : ℝ) < (r1 : ℝ) ^ 4 := by
    have : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
    positivity
  have h4 : Real.exp (-(Real.pi / 2) * ∑ j, D j) ≤ Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
    apply Real.exp_le_exp.2
    have : Real.pi * P.ph / (r1 : ℝ) ^ 4 ≤ Real.pi / 2 * ∑ j, D j := by
      rw [div_le_iff₀ hr4]
      have := mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le
      nlinarith
    linarith
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ C ^ X.r * Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by rw [h3]

end

end ReciprocityTheory.ChartRestriction.G.I2
end
