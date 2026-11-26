module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetMemSpanAdjugate
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL3.PHfInt
section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL3.PHfArith
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

abbrev bb : D.host.E := D.host.sqd

abbrev be : ℂ := Complex.I * (Real.sqrt D.host.d : ℂ)

def OKc (z : ℂ) : Prop :=
  ∃ x y : ℤ, Even (x - y) ∧ z = ((x : ℂ) + (y : ℂ) * be D) / 2

theorem d_pos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

theorem sqrt_pos : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (d_pos D)

theorem sq_sqrtC : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (d_pos D).le]; simp

theorem be_sq : be D ^ 2 = -(D.host.d : ℂ) := by
  rw [be, mul_pow, Complex.I_sq, sq_sqrtC]; ring

theorem conj_be : starRingEnd ℂ (be D) = -be D := by
  simp [be, Complex.conj_ofReal]

theorem d_mod : ∃ k : ℤ, (D.host.d : ℤ) = 4 * k + 3 :=
  ⟨(D.host.d : ℤ) / 4, by have := D.host.hyp.2.2.2.1; omega⟩

theorem phi_b : D.host.φ₀ (bb D) = be D := D.host.φ₀_mem

theorem b_sq : bb D ^ 2 = -(D.host.d : D.host.E) := by
  apply D.host.φ₀.injective
  rw [map_pow, phi_b, be_sq, map_neg, map_natCast]

theorem bK_mem : bb D ∈ D.host.K := FL.bE_mem D

def bK : D.host.K := ⟨bb D, bK_mem D⟩

theorem okc_of (u : 𝓞 D.host.K) : OKc D (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
  by apply _root_.UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.okc_of <;> assumption

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

open Formalism.MainNotions.TaylorLogMetric

def Bf (w₁ w₂ : ℂ) : ℝ := (starRingEnd ℂ w₁ * w₂).im

theorem Bf_swap (w₁ w₂ : ℂ) : Bf w₂ w₁ = -Bf w₁ w₂ := by
  simp only [Bf, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

theorem Bf_sub_zsmul_left (u w w₂ : ℂ) (q : ℤ) : Bf (u - q • w) w₂ = Bf u w₂ - q * Bf w w₂ := by
  simp only [Bf, zsmul_eq_mul, map_sub, map_mul, map_intCast, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem Bf_sub_zsmul_right (w₁ u w : ℂ) (q : ℤ) : Bf w₁ (u - q • w) = Bf w₁ u - q * Bf w₁ w := by
  simp only [Bf, zsmul_eq_mul, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem cramer (w₁ w₂ u : ℂ) :
    (Bf u w₂ : ℂ) * w₁ + (Bf w₁ u : ℂ) * w₂ = (Bf w₁ w₂ : ℂ) * u := by
  apply Complex.ext <;>
    simp only [Bf, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem Bf_comb (w₁ w₂ : ℂ) (s t s' t' : ℝ) :
    Bf ((s : ℂ) * w₁ + (t : ℂ) * w₂) ((s' : ℂ) * w₁ + (t' : ℂ) * w₂) = (s * t' - t * s') * Bf w₁ w₂ := by
  simp only [Bf, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem cast_toNat (n : ℤ) (h : 0 ≤ n) : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

theorem area_spec (Λ : AddSubgroup ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hdisc : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = κ * n)
    (hne : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area Λ = κ * m ∧ ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = area Λ * n := by
  classical

  have hQ : ∃ n : ℕ, 0 < n ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ = κ * n := by
    obtain ⟨w₁, h₁, w₂, h₂, h0⟩ := hne
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ w₂ h₂
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · refine ⟨(-n).toNat, by omega, w₂, h₂, w₁, h₁, ?_⟩
      rw [Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring
    · exact absurd (by rw [hn, hn0]; simp) h0
    · refine ⟨n.toNat, by omega, w₁, h₁, w₂, h₂, ?_⟩
      rw [hn, cast_toNat _ hn0.le]
  set m := Nat.find hQ with hm
  obtain ⟨hm0, w₁, h₁, w₂, h₂, hw⟩ := Nat.find_spec hQ
  have hmin : ∀ n : ℕ, 0 < n → ∀ u ∈ Λ, ∀ v ∈ Λ, Bf u v = κ * n → m ≤ n :=
    fun n hn u hu v hv h => Nat.find_min' hQ ⟨hn, u, hu, v, hv, h⟩

  have harea : area Λ = κ * m := by
    unfold area
    refine IsLeast.csInf_eq ⟨⟨by positivity, w₁, h₁, w₂, h₂, ?_⟩, ?_⟩
    · change κ * m = |Bf w₁ w₂|
      rw [hw, abs_of_nonneg (by positivity)]
    · rintro a ⟨ha, u, hu, v, hv, rfl⟩
      change κ * m ≤ |Bf u v|
      obtain ⟨n, hn⟩ := hdisc u hu v hv
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have := hmin (-n).toNat (by omega) v hv u hu (by
          rw [Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring)
        rw [hn, abs_mul, abs_of_pos hκ, abs_of_neg (by exact_mod_cast hn0 : (n : ℝ) < 0)]
        have h' : ((m : ℤ) : ℝ) ≤ ((-n : ℤ) : ℝ) := by exact_mod_cast (by omega : (m : ℤ) ≤ -n)
        push_cast at h'
        exact mul_le_mul_of_nonneg_left h' hκ.le
      · exfalso; change 0 < |Bf u v| at ha; rw [hn, hn0] at ha; simp at ha
      · have := hmin n.toNat (by omega) u hu v hv (by rw [hn, cast_toNat _ hn0.le])
        rw [hn, abs_mul, abs_of_pos hκ, abs_of_pos (by exact_mod_cast hn0 : (0 : ℝ) < n)]
        have h' : ((m : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast (by omega : (m : ℤ) ≤ n)
        push_cast at h'
        exact mul_le_mul_of_nonneg_left h' hκ.le
  refine ⟨m, hm0, harea, ?_⟩
  set g := κ * m with hg
  have hg0 : 0 < g := by positivity

  have hleft : ∀ u ∈ Λ, ∃ q : ℤ, Bf u w₂ = g * q := by
    intro u hu
    obtain ⟨n, hn⟩ := hdisc u hu w₂ h₂
    refine ⟨n / m, ?_⟩
    have hr : Bf (u - (n / m) • w₁) w₂ = κ * ((n % m : ℤ) : ℝ) := by
      rw [Bf_sub_zsmul_left, hn, hw]
      have := Int.mul_ediv_add_emod n m
      have : (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ) := by
        have h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ) := by exact_mod_cast this.symm
        rw [h2]; push_cast; ring
      rw [this]; ring
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra hne0
      have hpos : 0 < n % (m : ℤ) := lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)
      have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
      have := hmin (n % (m : ℤ)).toNat (by omega) _ (Λ.sub_mem hu (Λ.zsmul_mem h₁ _)) w₂ h₂
        (by rw [hr, cast_toNat _ hpos.le])
      omega
    have := Int.mul_ediv_add_emod n m
    rw [hr0, add_zero] at this
    have h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [hn, hg, h3]; ring
  have hright : ∀ u ∈ Λ, ∃ q : ℤ, Bf w₁ u = g * q := by
    intro u hu
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ u hu
    refine ⟨n / m, ?_⟩
    have hr : Bf w₁ (u - (n / m) • w₂) = κ * ((n % m : ℤ) : ℝ) := by
      rw [Bf_sub_zsmul_right, hn, hw]
      have := Int.mul_ediv_add_emod n m
      have : (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ) := by
        have h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ) := by exact_mod_cast this.symm
        rw [h2]; push_cast; ring
      rw [this]; ring
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra hne0
      have hpos : 0 < n % (m : ℤ) := lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)
      have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
      have := hmin (n % (m : ℤ)).toNat (by omega) w₁ h₁ _ (Λ.sub_mem hu (Λ.zsmul_mem h₂ _))
        (by rw [hr, cast_toNat _ hpos.le])
      omega
    have := Int.mul_ediv_add_emod n m
    rw [hr0, add_zero] at this
    have h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [hn, hg, h3]; ring

  have hdec : ∀ u ∈ Λ, ∃ s t : ℤ, u = ((s : ℝ) : ℂ) * w₁ + ((t : ℝ) : ℂ) * w₂ := by
    intro u hu
    obtain ⟨s, hs⟩ := hleft u hu
    obtain ⟨t, ht⟩ := hright u hu
    refine ⟨s, t, ?_⟩
    have hc := cramer w₁ w₂ u
    rw [hs, ht, hw] at hc
    have hg0' : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
    apply mul_left_cancel₀ hg0'
    rw [← hc]; push_cast; ring
  intro u hu v hv
  obtain ⟨s, t, rfl⟩ := hdec u hu
  obtain ⟨s', t', rfl⟩ := hdec v hv
  refine ⟨s * t' - t * s', ?_⟩
  rw [Bf_comb, hw, harea]; push_cast; ring

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

variable (D : D7)

abbrev ph (c : 𝓞 D.host.K) : ℂ := D.host.φ₀ (((c : D.host.K) : D.host.E))

theorem okc_mul {z w : ℂ} (hz : OKc D z) (hw : OKc D w) : OKc D (z * w) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  obtain ⟨x', y', ⟨a', ha'⟩, rfl⟩ := hw
  obtain ⟨k, hk⟩ := d_mod D
  obtain rfl : x = y + a + a := by omega
  obtain rfl : x' = y' + a' + a' := by omega
  refine ⟨-(2 * k + 1) * y * y' + a * y' + a' * y + 2 * a * a', y * y' + a * y' + a' * y,
    ⟨-(k + 1) * y * y' + a * a', by ring⟩, ?_⟩
  have hkC : (D.host.d : ℂ) = 4 * k + 3 := by exact_mod_cast hk
  have hsq := be_sq D
  push_cast
  linear_combination hsq * ((y : ℂ) * y' / 4) - hkC * ((y : ℂ) * y' / 4)

theorem okc_conj {z : ℂ} (hz : OKc D z) : OKc D (starRingEnd ℂ z) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  refine ⟨x, -y, ⟨a + y, by omega⟩, ?_⟩
  rw [map_div₀, map_add (f := _), map_mul, conj_be, map_intCast, map_intCast, map_ofNat]; push_cast; ring

theorem coord_eq (x y : ℤ) :
    ((x : ℂ) + (y : ℂ) * be D) / 2 =
      (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

theorem im_coord (x y : ℤ) :
    (((x : ℂ) + (y : ℂ) * be D) / 2).im = (y : ℝ) * Real.sqrt D.host.d / 2 := by
  rw [coord_eq]; simp

theorem good_of_okc {u : ℂ} (hu : OKc D u) : Good D (2 * u / (Real.sqrt D.host.d : ℂ)) := by
  obtain ⟨x, y, hxy, rfl⟩ := hu
  refine ⟨x, y, hxy, ?_⟩
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos D).ne'
  push_cast
  field_simp

theorem half_int {F : Type*} [Field F] [CharZero F] (x : F) (k : ℤ)
    (hx : x ^ 2 = -(4 * (k : F) + 3)) : IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  push_cast
  linear_combination hx / 4

theorem bK_sq : bK D ^ 2 = -(D.host.d : D.host.K) := by
  apply Subtype.ext
  push_cast
  exact b_sq D

def om : 𝓞 D.host.K :=
  ⟨(1 + bK D) / 2, half_int _ (d_mod D).choose (by
    have h2 : ((D.host.d : ℤ) : D.host.K) = ((4 * (d_mod D).choose + 3 : ℤ) : D.host.K) :=
      congrArg (fun t : ℤ => (t : D.host.K)) (d_mod D).choose_spec
    push_cast at h2
    rw [bK_sq D]; linear_combination -h2)⟩

theorem ph_om : ph D (om D) = (1 + be D) / 2 := by
  show D.host.φ₀ ((((1 + bK D) / 2 : D.host.K)) : D.host.E) = _
  have h2 : ((2 : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : D.host.K) = 1 + 1 by norm_num, IntermediateField.coe_add, IntermediateField.coe_one]
    norm_num
  push_cast
  rw [h2, map_div₀, map_add (f := _), map_one, map_ofNat]
  exact congrArg (fun t => (1 + t) / 2) (phi_b D)

theorem Bf_lat (δ : ℂ) (c₁ c₂ : 𝓞 D.host.K) :
    Bf (δ * ph D c₁) (δ * ph D c₂) = Complex.normSq δ * (starRingEnd ℂ (ph D c₁) * ph D c₂).im := by
  have : starRingEnd ℂ (δ * ph D c₁) * (δ * ph D c₂) =
      (Complex.normSq δ : ℂ) * (starRingEnd ℂ (ph D c₁) * ph D c₂) := by
    rw [Complex.normSq_eq_conj_mul_self, map_mul]; ring
  rw [Bf, this]; simp [Complex.mul_im]

theorem okc_pair (c₁ c₂ : 𝓞 D.host.K) : OKc D (starRingEnd ℂ (ph D c₁) * ph D c₂) :=
  okc_mul D (okc_conj D (okc_of D c₁)) (okc_of D c₂)

theorem div_okc (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area (lamOf D cc δ) = Complex.normSq δ * (Real.sqrt D.host.d / 2) * m ∧
      ∀ c ∈ cc, ∀ c' ∈ cc, OKc D (starRingEnd ℂ (ph D c') * ph D c / m) := by
  have hn : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  have hs := sqrt_pos D
  have hκ : 0 < Complex.normSq δ * (Real.sqrt D.host.d / 2) := by positivity
  have hdisc : ∀ w₁ ∈ lamOf D cc δ, ∀ w₂ ∈ lamOf D cc δ, ∃ n : ℤ,
      Bf w₁ w₂ = Complex.normSq δ * (Real.sqrt D.host.d / 2) * n := by
    intro w₁ h₁ w₂ h₂
    obtain ⟨c₁, -, rfl⟩ := FL.lam_mem D cc δ w₁ h₁
    obtain ⟨c₂, -, rfl⟩ := FL.lam_mem D cc δ w₂ h₂
    obtain ⟨x, y, -, hz⟩ := okc_pair D c₁ c₂
    refine ⟨y, ?_⟩
    rw [Bf_lat, hz, im_coord]; ring
  have hne : ∃ w₁ ∈ lamOf D cc δ, ∃ w₂ ∈ lamOf D cc δ, Bf w₁ w₂ ≠ 0 := by
    set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
    refine ⟨δ * ph D c, AddSubgroup.subset_closure ⟨c, hc, rfl⟩,
      δ * ph D (c * om D), AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩, ?_⟩
    have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
      rw [← ph_om]; simp [ph]
    have hc1 : ph D c ≠ 0 := by
      simp only [ph, map_ne_zero_iff _ D.host.φ₀.injective]
      exact_mod_cast hc0
    rw [Bf_lat, hph]
    have e : starRingEnd ℂ (ph D c) * (ph D c * ((1 + be D) / 2)) =
        (Complex.normSq (ph D c) : ℂ) * ((1 + be D) / 2) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    have e4 : (1 + be D) / 2 =
        (((1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have e5 : ((Complex.normSq (ph D c) : ℂ) * ((((1 : ℝ) / 2 : ℝ) : ℂ) +
        ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I)).im =
        Complex.normSq (ph D c) * (Real.sqrt D.host.d / 2) := by simp [Complex.mul_im]
    rw [e, e4, e5]
    exact mul_ne_zero hn.ne' (mul_ne_zero (Complex.normSq_pos.2 hc1).ne' (by positivity))
  obtain ⟨m, hm, harea, hall⟩ := area_spec (lamOf D cc δ) _ hκ hdisc hne
  refine ⟨m, hm, harea, fun c hc c' hc' => ?_⟩
  obtain ⟨x, y, -, hz⟩ := okc_pair D c' c
  obtain ⟨n₁, h₁⟩ := hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _
    (AddSubgroup.subset_closure ⟨c, hc, rfl⟩)
  obtain ⟨n₂, h₂⟩ := hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _
    (AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩)
  have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
    rw [← ph_om]; simp [ph]
  rw [Bf_lat, hz, im_coord, harea] at h₁
  rw [Bf_lat, hph, ← mul_assoc, hz, harea] at h₂
  have e2 : ((x : ℂ) + (y : ℂ) * be D) / 2 * ((1 + be D) / 2) =
      ((((x - D.host.d * y : ℤ) : ℂ) + ((x + y : ℤ) : ℂ) * be D) / 2) / 2 := by
    push_cast; linear_combination (y : ℂ) / 4 * be_sq D
  rw [e2, Complex.div_ofNat_im, im_coord] at h₂
  have hy : (y : ℝ) = m * n₁ := by
    have : Complex.normSq δ * (Real.sqrt D.host.d / 2) * (y - m * n₁) = 0 := by linear_combination h₁
    have := (mul_eq_zero.1 this).resolve_left hκ.ne'
    linarith
  have hxy : ((x + y : ℤ) : ℝ) = 2 * (m * n₂) := by
    have : Complex.normSq δ * (Real.sqrt D.host.d / 2) * (((x + y : ℤ) : ℝ) - 2 * (m * n₂)) = 0 := by
      linear_combination 2 * h₂
    have := (mul_eq_zero.1 this).resolve_left hκ.ne'
    linarith
  have hyZ : y = m * n₁ := by exact_mod_cast hy
  have hxZ : x = 2 * m * n₂ - m * n₁ := by
    have : x + y = 2 * (m * n₂) := by exact_mod_cast hxy
    linarith
  refine ⟨2 * n₂ - n₁, n₁, ⟨n₂ - n₁, by ring⟩, ?_⟩
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hz, hxZ, hyZ]
  field_simp
  push_cast
  ring

def HYYIntRec : Prop :=
  ∀ D : D7, ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
    ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L', IsIntegral ℤ (hYY D A B)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

theorem HfArithRec_of_int (h : HYYIntRec) : HfArithRec := by
  intro D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'
  obtain ⟨m, hm, harea, hdiv⟩ := div_okc D cc hcc.1 δ h0
  have hh : OKc D (D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E)) :=
    okc_of D ⟨hYY D A B, h D N N' L L' hA A hA' B hB'⟩
  have hprod := okc_mul D (hdiv c hc c' hc') hh
  have hg := good_of_okc D hprod
  convert hg using 1
  have hnz : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 h0).ne'
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos D).ne'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcd : starRingEnd ℂ δ ≠ 0 := by simpa using h0
  rw [harea]
  simp only [ph, map_mul]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self] at hnz ⊢
  field_simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

open Polynomial NumberField Matrix

theorem trace_isIntegral {E : Type*} [Field E] [NumberField E] (φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M *ᵥ x ∈ L) : IsIntegral ℤ M.trace := by
  first | exact GlobalTheory.IntegralTrace.isIntegral_trace .. | (apply GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (intros; apply GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (intros; apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> first | assumption | infer_instance) | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp M hM | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp M | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› | exact @GlobalTheory.IntegralTrace.isIntegral_trace E

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits Matrix

variable (D : D7)

def sE {N N' : ℕ} (A B : Matrix (Fin N') (Fin N) D.host.E) : D.host.E :=
  ∑ i, ∑ j, A i j * D.host.conj (B i j)

theorem hYY_eq {N N' : ℕ} (A B : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D A B = Algebra.trace D.host.K D.host.E (sE D A B) := rfl

theorem conj_int (o : 𝓞 D.host.E) : IsIntegral ℤ (D.host.conj (o : D.host.E)) :=
  o.isIntegral_coe.map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).toRingHom.toIntAlgHom

def cO (o : 𝓞 D.host.E) : 𝓞 D.host.E := ⟨D.host.conj (o : D.host.E), conj_int D o⟩

theorem smul_entry {N N' : ℕ} (o : 𝓞 D.host.E) (A : Matrix (Fin N') (Fin N) D.host.E) (i j) :
    (o • A) i j = (o : D.host.E) * A i j := by
  rw [Matrix.smul_apply, Algebra.smul_def]

theorem sE_add_left {N N' : ℕ} (A A' B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (A + A') B = sE D A B + sE D A' B := by
  simp only [sE, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem sE_add_right {N N' : ℕ} (A B B' : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (B + B') = sE D A B + sE D A B' := by
  simp only [sE, Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem sE_zero_left {N N' : ℕ} (B : Matrix (Fin N') (Fin N) D.host.E) : sE D 0 B = 0 := by
  simp [sE]

theorem sE_zero_right {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) : sE D A 0 = 0 := by
  simp [sE]

theorem sE_smul_left {N N' : ℕ} (o : 𝓞 D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (o • A) B = (o : D.host.E) * sE D A B := by
  simp only [sE, smul_entry, Finset.mul_sum, mul_assoc]

theorem sE_smul_right {N N' : ℕ} (o : 𝓞 D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (o • B) = D.host.conj (o : D.host.E) * sE D A B := by
  simp only [sE, smul_entry, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sE_esmul_left {N N' : ℕ} (a : D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (a • A) B = a * sE D A B := by
  simp only [sE, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem sE_esmul_right {N N' : ℕ} (b : D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (b • B) = D.host.conj b * sE D A B := by
  simp only [sE, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sE_hom_gen {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E)
    (hA : ∀ x ∈ L, A *ᵥ x ∈ L') (hB : ∀ x ∈ L, B *ᵥ x ∈ L') : IsIntegral ℤ (sE D A B) := by
  let _ := D.host.cmStar
  set Bs : Matrix (Fin N) (Fin N') D.host.E := Matrix.of fun j i => D.host.conj (B i j) with hBs
  have hBs_mem : ∀ y ∈ L', Bs *ᵥ y ∈ L := by
    intro y hy
    rw [hL.2.2]
    intro x hx
    have h1 : stdH D.host.E N x (Bs *ᵥ y) = stdH D.host.E N' (B *ᵥ x) y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [stdH, CU.star_conj D, Matrix.mulVec, dotProduct, hBs, Matrix.of_apply, map_sum,
        map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    exact (hL'.2.2 y).1 hy _ (hB x hx)
  have hM : ∀ x ∈ L, (Bs * A) *ᵥ x ∈ L := by
    intro x hx
    rw [← Matrix.mulVec_mulVec]
    exact hBs_mem _ (hA x hx)
  have h := trace_isIntegral D.host.φ₀ L hL.1 hL.2.1 (Bs * A) hM
  have htr : (Bs * A).trace = sE D A B := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sE, hBs, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rwa [htr] at h

theorem sE_hom {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E) (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    IsIntegral ℤ (sE D A B) := by
  have h1 : ∀ A ∈ homL D L L', ∀ B, (∀ x ∈ L, B *ᵥ x ∈ L') → IsIntegral ℤ (sE D A B) := by
    intro A hA B hB
    induction hA using Submodule.span_induction with
    | mem A hA => exact sE_hom_gen D L L' hL hL' A B hA hB
    | zero => rw [sE_zero_left]; exact isIntegral_zero
    | add A A' _ _ h1 h2 => rw [sE_add_left]; exact h1.add h2
    | smul o A _ h1 => rw [sE_smul_left]; exact o.isIntegral_coe.mul h1
  induction hB using Submodule.span_induction with
  | mem B hB => exact h1 A hA B hB
  | zero => rw [sE_zero_right]; exact isIntegral_zero
  | add B B' _ _ h2 h3 => rw [sE_add_right]; exact h2.add h3
  | smul o B _ h2 => rw [sE_smul_right]; exact (conj_int D o).mul h2

def TrOK (z : D.host.E) : Prop :=
  ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace D.host.K D.host.E ((o : D.host.E) * z))

theorem trOK_zero : TrOK D 0 := fun o => by rw [mul_zero, map_zero]; exact isIntegral_zero

theorem trOK_add {z w : D.host.E} (hz : TrOK D z) (hw : TrOK D w) : TrOK D (z + w) :=
  fun o => by rw [mul_add, map_add (f := _)]; exact (hz o).add (hw o)

theorem trOK_mul {z : D.host.E} (hz : TrOK D z) (o' : 𝓞 D.host.E) : TrOK D ((o' : D.host.E) * z) :=
  fun o => by
    have := hz (o * o')
    rwa [show ((o * o' : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * o' from rfl, mul_assoc] at this

theorem trace_conj_integral (a b : D.host.E) (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (hb : b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    IsIntegral ℤ (Algebra.trace D.host.K D.host.E (a * D.host.conj b)) := by
  have h := ((D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 a).1 ha) b hb
  obtain ⟨r, hr⟩ := h
  rw [← hr]
  exact r.isIntegral_coe

theorem trOK_gen (a b : D.host.E) (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (hb : b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) (t : 𝓞 D.host.E) :
    TrOK D (a * D.host.conj b * t) := by
  intro o
  have hot : ((o * t : 𝓞 D.host.E) : D.host.E) * a ∈
      (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem (o * t) ha
    rwa [Algebra.smul_def] at this
  have := trace_conj_integral D _ b hot hb
  rw [show ((o * t : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * t from rfl] at this
  convert this using 2
  ring

theorem trOK_YY {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E) (hA : A ∈ YYl D L L') (hB : B ∈ YYl D L L') :
    TrOK D (sE D A B) := by

  have hgen : ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ A₀ ∈ homL D L L',
      ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ B₀ ∈ homL D L L',
      TrOK D (sE D (a • A₀) (b • B₀)) := by
    intro a ha A₀ hA₀ b hb B₀ hB₀
    rw [sE_esmul_left, sE_esmul_right, ← mul_assoc]
    exact trOK_gen D a b ha hb ⟨sE D A₀ B₀, sE_hom D L L' hL hL' A₀ B₀ hA₀ hB₀⟩
  have h1 : ∀ A ∈ YYl D L L', ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ B₀ ∈ homL D L L', TrOK D (sE D A (b • B₀)) := by
    intro A hA b hb B₀ hB₀
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨a, ha, A₀, hA₀, rfl⟩ := hA
      exact hgen a ha A₀ hA₀ b hb B₀ hB₀
    | zero => rw [sE_zero_left]; exact trOK_zero D
    | add A A' _ _ h2 h3 => rw [sE_add_left]; exact trOK_add D h2 h3
    | smul o A _ h2 => rw [sE_smul_left]; exact trOK_mul D h2 o
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨b, hb, B₀, hB₀, rfl⟩ := hB
    exact h1 A hA b hb B₀ hB₀
  | zero => rw [sE_zero_right]; exact trOK_zero D
  | add B B' _ _ h2 h3 => rw [sE_add_right]; exact trOK_add D h2 h3
  | smul o B _ h2 => rw [sE_smul_right]; exact trOK_mul D h2 (cO D o)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

theorem hermitian_pairing_integral : AR.HYYIntRec := by
  intro D N N' L L' hA A hA' B hB'
  have h := trOK_YY D L L' hA.2.2.1 hA.2.2.2 A B hA' hB' 1
  rw [hYY_eq]
  simpa using h

theorem arithmetic_hermitian_form : HfArithRec := HfArithRec_of_int hermitian_pairing_integral

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem hermitian_form_integral_values : HfIntRec := HfIntRec_of_gen (HfGenRec_of_arith arithmetic_hermitian_form)

theorem theta_operator_isometry : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ,
    IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IopIso D (tor0 D cc δ) :=
  IopIso_of_parts hermitian_form_integral_values self_dual_lattice

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
