module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableTheta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSubConjNotMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductModularSTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelModularSTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelModularSTransform
open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

noncomputable section

namespace GlobalTheory.Sieg.ThInv

open GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv

theorem exp_pi_I_half : cexp (π * I / 2) = I := by
  rw [show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]

theorem oddTheta_eq (τ : ℍ) (z : ℂ) : oddTheta τ z = I * ModularForm.eta (τ : ℂ) * th z τ := by
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have hC := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have hP : ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) =
      tailProd τ (cexp (2 * π * I * z)) * tailProd τ (cexp (-(2 * π * I * z))) := by
    rw [← (hB.mul hC).tprod_eq]
    refine tprod_congr fun n => ?_
    rw [ModularForm.eta_q_eq_pow, Complex.exp_neg]
    rfl
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have h1 : cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) =
      I * Function.Periodic.qParam 24 (τ : ℂ) * ee ((τ : ℂ) / 12) * ee (z / 2) := by
    rw [Function.Periodic.qParam, ee, ee]
    conv_rhs => rw [← exp_pi_I_half]
    rw [exp_pi_I_half]
    nth_rewrite 3 [← exp_pi_I_half]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h2 : ee (-z / 2) = ee (z / 2) * cexp (-(2 * π * I * z)) := by
    rw [ee, ee, ← Complex.exp_add]
    congr 1; ring
  rw [oddTheta, jacobiTheta₂_shift GlobalTheory.JacobiTriple.tripleProduct, th, hP, ModularForm.eta, ← hT1, h1, h2]
  ring

theorem sqrt_eq (τ : ℍ) : (Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : -I * (τ : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ
  have hre : 0 < (-I * (τ : ℂ)).re := by simpa using τ.im_pos
  have ha := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))
  have hl : log (I * (-I * (τ : ℂ))) = log I + log (-I * (τ : ℂ)) := by
    rw [Complex.log_mul_eq_add_log_iff I_ne_zero h0, Complex.arg_I]
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [show I * (-I * (τ : ℂ)) = τ by linear_combination (-(τ : ℂ)) * I_sq] at hl
  rw [Complex.sqrt, Complex.sqrt, Complex.cpow_def_of_ne_zero I_ne_zero, Complex.cpow_def_of_ne_zero hτ,
    Complex.cpow_def_of_ne_zero h0, hl,
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1; ring

theorem eta_S (τ : ℍ) :
    ModularForm.eta (-1 / (τ : ℂ)) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ModularForm.eta (τ : ℂ) := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  rw [← sqrt_eq, mul_assoc]
  simpa using h

theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [neg_div]

theorem oddTheta_S (τ : ℍ) (z : ℂ) :
    oddTheta (ModularGroup.S • τ) (z / (τ : ℂ)) =
      -I * (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ee (z ^ 2 / (2 * (τ : ℂ))) * oddTheta τ z := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ h.1
  have hI : -I = cexp (-(π * I / 2)) := by
    rw [Complex.exp_neg, exp_pi_I_half, Complex.inv_I]
  rw [oddTheta, oddTheta, coe_S_smul, jacobiTheta₂_functional_equation (z + ((τ : ℂ) + 1) / 2) τ,
    show z / (τ : ℂ) + (-1 / (τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) / τ + -1 / (τ : ℂ) by
      field_simp; ring, jacobiTheta₂_add_left']
  generalize jacobiTheta₂ ((z + ((τ : ℂ) + 1) / 2) / τ) (-1 / (τ : ℂ)) = J
  generalize (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = s at h0 ⊢
  have hE : ∀ A B C D : ℂ, cexp A * s * cexp B * (cexp C * (1 / s * cexp D * J)) =
      cexp (A + B + C + D) * J := by
    intro A B C D
    simp only [Complex.exp_add]
    field_simp
  rw [ee]
  conv_rhs => rw [hI]
  rw [hE, ← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

theorem th_S : ∀ (τ : ℍ) (z : ℂ), th (z / (τ : ℂ)) (ModularGroup.S • τ) =
    -Complex.I * ee (z ^ 2 / (2 * (τ : ℂ))) * th z τ := by
  intro τ z
  have h := oddTheta_S τ z
  rw [oddTheta_eq, oddTheta_eq] at h
  have hne : I * ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (ModularForm.eta_ne_zero (ModularGroup.S • τ).2)
  refine mul_left_cancel₀ hne ?_
  rw [h, coe_S_smul, eta_S]
  ring

end GlobalTheory.Sieg.ThInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelModularSTransformStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddThetaProductSiegel_modularS_transform : ∀ (τ : ℍ) (z : ℂ), th (z / (τ : ℂ)) (ModularGroup.S • τ) = -Complex.I * ee (z ^ 2 / (2 * (τ : ℂ))) * th z τ := by
  first | exact @GlobalTheory.Sieg.ThInv.th_S | exact GlobalTheory.Sieg.ThInv.th_S | (intros; apply GlobalTheory.Sieg.ThInv.th_S <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductEqOddThetaProductQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductEqOddThetaProductQuotient
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg.ThQuot

theorem ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

theorem ee_nat_mul (n : ℕ) (z : ℂ) : ee ((n : ℂ) * z) = ee z ^ n := by
  unfold ee
  rw [← Complex.exp_nat_mul]; congr 1; ring

theorem ee_neg (z : ℂ) : ee (-z) = (ee z)⁻¹ := by
  unfold ee
  rw [← Complex.exp_neg]; congr 1; ring

theorem norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  unfold ee
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have h1 := τ.im_pos
  have h2 := Real.pi_pos
  have : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have : 0 < 2 * Real.pi * τ.im := by positivity
  linarith

theorem multipliable_one_sub {q : ℂ} (hq : ‖q‖ < 1) (t : ℂ) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1) * t) := by
  have h : Summable (fun n : ℕ => -(q ^ (n + 1) * t)) := by
    have h0 := (summable_geometric_of_norm_lt_one hq).mul_right (q * t)
    refine h0.neg.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable h

theorem hasProd_pow_div {f g : ℕ → ℂ} {a b : ℂ} (hf : HasProd f a) (hg : HasProd g b) (hb : b ≠ 0) (k : ℕ) :
    HasProd (fun n => f n ^ k / g n) (a ^ k / b) := by
  unfold HasProd at *
  simp only [Finset.prod_div_distrib, Finset.prod_pow]
  exact (hf.pow k).div hg hb

theorem twelve_dvd {c : ℕ} (h1 : 1 < c) (h : Nat.Coprime c 6) : ∃ k, c ^ 2 = 12 * k + 1 := by
  have h2 : ¬ 2 ∣ c := fun hd => by
    have := Nat.Coprime.coprime_dvd_left hd h
    norm_num at this
  have h3 : ¬ 3 ∣ c := fun hd => by
    have := Nat.Coprime.coprime_dvd_left hd h
    norm_num at this
  obtain ⟨m, hm⟩ : ∃ m, c = 6 * m + 1 ∨ c = 6 * m + 5 := ⟨c / 6, by omega⟩
  rcases hm with rfl | rfl
  · exact ⟨3 * m ^ 2 + m, by ring⟩
  · exact ⟨3 * m ^ 2 + 5 * m + 2, by ring⟩

theorem cth_eq_th_quot : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → th ((c : ℂ) * z) τ ≠ 0 →
    cth c (ee (τ : ℂ)) (ee z) = (-1) ^ (c * (c - 1) / 2) * th z τ ^ (c ^ 2) / th ((c : ℂ) * z) τ := by
  intro c τ z h1 hc hne
  obtain ⟨k, hk⟩ := twelve_dvd h1 hc
  have hodd : Odd c := by
    have : Odd (c ^ 2) := ⟨6 * k, by omega⟩
    exact (Nat.odd_pow_iff (by norm_num)).mp this
  obtain ⟨j, hj⟩ := hodd
  have hq := norm_ee_lt_one τ
  set s := ee (z / 2) with hs
  set u := ee ((τ : ℂ) / 12) with hu
  have hs0 : s ≠ 0 := ee_ne_zero _
  have hu0 : u ≠ 0 := ee_ne_zero _
  have ht : ee z = s ^ 2 := by
    rw [hs, ← ee_nat_mul]; congr 1; push_cast; ring
  have hqu : ee (τ : ℂ) = u ^ 12 := by
    rw [hu, ← ee_nat_mul]; congr 1; push_cast; ring
  have e1 : ee (-z / 2) = s⁻¹ := by rw [neg_div, ee_neg]
  have e2 : ee ((c : ℂ) * z / 2) = s ^ c := by rw [mul_div_assoc, ee_nat_mul]
  have e3 : ee (-((c : ℂ) * z) / 2) = (s ^ c)⁻¹ := by rw [neg_div, ee_neg, e2]
  have e4 : ee ((c : ℂ) * z) = ee z ^ c := ee_nat_mul c z
  unfold th at hne ⊢
  unfold cth
  rw [e2, e3, e4] at hne ⊢
  rw [e1, ← hs, ← hu] at *
  have mf := ((multipliable_one_sub hq (ee z)).mul (multipliable_one_sub hq (ee z)⁻¹)).hasProd
  have mg := ((multipliable_one_sub hq (ee z ^ c)).mul (multipliable_one_sub hq (ee z ^ c)⁻¹)).hasProd
  set A := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) with hA
  set B := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z ^ c) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z ^ c)⁻¹) with hB
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hne
  have hd : s ^ c - (s ^ c)⁻¹ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hP : ∏' m : ℕ, cthFac c (ee (τ : ℂ)) (ee z) (m + 1) = A ^ (c ^ 2) / B := by
    have := hasProd_pow_div mf mg hB0 (c ^ 2)
    refine (HasProd.tprod_eq ?_)
    simpa only [cthFac, mul_pow] using this
  rw [hP]
  have x1 : (c ^ 2 - 1) / 12 = k := by omega
  have x2 : c * (c - 1) / 2 = c * j := by
    have : c * (c - 1) = 2 * (c * j) := by
      have : c - 1 = 2 * j := by omega
      rw [this]; ring
    omega
  have x3 : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c * j : ℕ) : ℤ) := by
    have : (c : ℤ) - (c : ℤ) ^ 2 = 2 * (-((c * j : ℕ) : ℤ)) := by
      subst hj; push_cast; ring
    rw [this]; omega
  rw [x1, x2, x3, zpow_neg, zpow_natCast, ht, hqu]
  have hsc : s ^ c ≠ 0 := pow_ne_zero _ hs0
  have y1 : s ^ c - (s ^ c)⁻¹ = -(1 - (s ^ 2) ^ c) / s ^ c := by
    field_simp; ring
  have y2 : s - s⁻¹ = -(1 - s ^ 2) / s := by field_simp; ring
  have hd' : 1 - (s ^ 2) ^ c ≠ 0 := by
    intro h; apply hd; rw [y1, h]; simp
  have hc2 : Odd (c ^ 2) := ⟨6 * k, by omega⟩
  have y3 : s ^ (c ^ 2) = s ^ c * (s ^ 2) ^ (c * j) := by
    rw [← pow_mul, ← pow_add]; congr 1; subst hj; ring
  have y4 : u ^ (c ^ 2) = u * (u ^ 12) ^ k := by rw [hk, ← pow_mul]; ring
  have y5 : ((-1 : ℂ)) ^ (c * j) * (-1) ^ (c * j) = 1 := by rw [← mul_pow]; simp
  rw [y1, y2, mul_pow, mul_pow, div_pow, hc2.neg_pow, y3, y4, neg_pow (s ^ 2)]
  have hS : (s ^ 2) ^ (c * j) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hs0)
  generalize (s ^ 2) ^ (c * j) = S at *
  generalize (1 - (s ^ 2) ^ c) = D at *
  generalize (1 - s ^ 2) ^ (c ^ 2) = E at *
  generalize s ^ c = T at *
  generalize A ^ (c ^ 2) = A' at *
  generalize (u ^ 12) ^ k = U at *
  generalize ((-1 : ℂ)) ^ (c * j) = ε at *
  have hε : ε ≠ 0 := left_ne_zero_of_mul (y5 ▸ one_ne_zero)
  have hi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right y5
  rw [mul_inv, hi]
  field_simp

end GlobalTheory.Sieg.ThQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductEqOddThetaProductQuotientStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → th ((c : ℂ) * z) τ ≠ 0 → cth c (ee (τ : ℂ)) (ee z) = (-1) ^ (c * (c - 1) / 2) * th z τ ^ (c ^ 2) / th ((c : ℂ) * z) τ := by
  first | exact @GlobalTheory.Sieg.ThQuot.cth_eq_th_quot | exact GlobalTheory.Sieg.ThQuot.cth_eq_th_quot | (intros; apply GlobalTheory.Sieg.ThQuot.cth_eq_th_quot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLattice
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.ThZero

lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  simp only [ee, mul_add, Complex.exp_add]

lemma ee_ne (a : ℂ) : ee a ≠ 0 := Complex.exp_ne_zero _

lemma ee_neg (a : ℂ) : ee (-a) = (ee a)⁻¹ := by
  simp only [ee, mul_neg, Complex.exp_neg]

lemma ee_pow (a : ℂ) (n : ℕ) : ee a ^ n = ee ((n : ℂ) * a) := by
  simp only [ee]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma ee_eq_one_iff (a : ℂ) : ee a = 1 ↔ ∃ k : ℤ, a = k := by
  have h : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  simp only [ee, Complex.exp_eq_one_iff]
  refine exists_congr fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · apply mul_left_cancel₀ h
    rw [hk]; ring
  · rw [hk]; ring

lemma norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  simp only [ee, Complex.norm_exp]
  rw [Real.exp_lt_one_iff]
  have h1 := τ.im_pos
  have h2 := Real.pi_pos
  have : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp
  rw [this]
  have : 0 < 2 * Real.pi * τ.im := by positivity
  linarith

lemma summable_nine_pow_mul_inv_sq_succ (τ : ℍ) (c : ℂ) : Summable fun n : ℕ => ‖-(ee (τ : ℂ) ^ (n + 1) * c)‖ := by
  have h := summable_geometric_of_lt_one (norm_nonneg _) (norm_ee_lt_one τ)
  refine (h.mul_right (‖ee (τ : ℂ)‖ * ‖c‖)).congr fun n => ?_
  simp only [norm_neg, norm_mul, norm_pow, pow_succ]
  ring

lemma tprod_ne (τ : ℍ) (a b : ℂ) (ha : ∀ n : ℕ, 1 - ee (τ : ℂ) ^ (n + 1) * a ≠ 0)
    (hb : ∀ n : ℕ, 1 - ee (τ : ℂ) ^ (n + 1) * b ≠ 0) :
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * a) * (1 - ee (τ : ℂ) ^ (n + 1) * b) ≠ 0 := by
  simp only [sub_eq_add_neg] at ha hb ⊢
  rw [(multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ a)).tprod_mul
    (multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ b))]
  exact mul_ne_zero (tprod_one_add_ne_zero_of_summable ha (summable_nine_pow_mul_inv_sq_succ τ a))
    (tprod_one_add_ne_zero_of_summable hb (summable_nine_pow_mul_inv_sq_succ τ b))

lemma first_iff (z : ℂ) : ee (z / 2) - ee (-z / 2) = 0 ↔ ∃ k : ℤ, z = k := by
  rw [← ee_eq_one_iff, sub_eq_zero]
  have h1 : ee z = ee (z / 2) * ee (z / 2) := by rw [← ee_add]; congr 1; ring
  have h2 : ee (-z / 2) = (ee (z / 2))⁻¹ := by rw [← ee_neg]; congr 1; ring
  rw [h1, h2]
  have h3 := ee_ne (z / 2)
  constructor
  · intro h
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ h3
  · intro h
    exact eq_inv_of_mul_eq_one_left h

lemma fac_iff (τ : ℍ) (w : ℂ) (n : ℕ) :
    1 - ee (τ : ℂ) ^ (n + 1) * ee w = 0 ↔ ∃ k : ℤ, ((n : ℂ) + 1) * τ + w = k := by
  rw [ee_pow, ← ee_add, sub_eq_zero, eq_comm, ee_eq_one_iff]
  push_cast
  rfl

theorem th_eq_zero_iff :
    ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  intro τ z
  unfold th
  constructor
  · intro h
    by_contra hne
    refine (mul_ne_zero (mul_ne_zero (ee_ne _) ?_) (tprod_ne τ _ _ ?_ ?_)) h
    · rw [Ne, first_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨0, k, by simp [hk]⟩
    · intro n
      rw [Ne, fac_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨-((n : ℤ) + 1), k, by push_cast; linear_combination hk⟩
    · intro n
      rw [← ee_neg, Ne, fac_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨(n : ℤ) + 1, -k, by push_cast; linear_combination -hk⟩
  · rintro ⟨m, k, hz⟩
    rcases lt_trichotomy m 0 with hm | hm | hm
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
      have : 1 - ee (τ : ℂ) ^ (n + 1) * ee z = 0 :=
        (fac_iff τ z n).2 ⟨k, by rw [hz]; push_cast; ring⟩
      rw [tprod_of_exists_eq_zero ⟨n, by rw [this, zero_mul]⟩, mul_zero]
    · have : ee (z / 2) - ee (-z / 2) = 0 := (first_iff z).2 ⟨k, by simp [hz, hm]⟩
      rw [this, mul_zero, zero_mul]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
      have : 1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹ = 0 := by
        rw [← ee_neg]
        exact (fac_iff τ (-z) n).2 ⟨-k, by rw [hz]; push_cast; ring⟩
      rw [tprod_of_exists_eq_zero ⟨n, by rw [this, mul_zero]⟩, mul_zero]

end GlobalTheory.ThZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLatticeStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice : ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  first | exact @GlobalTheory.ThZero.th_eq_zero_iff | exact GlobalTheory.ThZero.th_eq_zero_iff | (intros; apply GlobalTheory.ThZero.th_eq_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductModularSTransform
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory

open GlobalTheory.Sieg

lemma Sieg.cthS_ee_pow (w : ℂ) (n : ℕ) : ee w ^ n = ee ((n : ℂ) * w) := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma Sieg.cthS_negI_pow (c : ℕ) (hc : Nat.Coprime c 6) : (-Complex.I) ^ (c ^ 2) = -Complex.I := by
  have h2 : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
  have hodd : Odd c := by
    rcases Nat.even_or_odd c with h | h
    · exfalso
      obtain ⟨j, hj⟩ := h
      have : 2 ∣ Nat.gcd c 2 := Nat.dvd_gcd ⟨j, by omega⟩ dvd_rfl
      rw [h2] at this
      omega
    · exact h
  obtain ⟨j, rfl⟩ := hodd
  have : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
  rw [this, pow_succ, pow_mul]
  have h4 : (-Complex.I) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  rw [h4, one_pow, one_mul]

theorem Sieg.cth_modular_S (c : ℕ) (τ : ℍ) (z : ℂ) (h1 : 1 < c) (hc : Nat.Coprime c 6)
    (hz : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) :
    cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [inv_neg]

  have hB : th ((c : ℂ) * z) τ ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice τ _).1 h
    exact hz m n hmn

  have hB' : th ((c : ℂ) * (z / (τ : ℂ))) (ModularGroup.S • τ) ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice _ _).1 h
    rw [hS] at hmn
    apply hz n (-m)
    have : (c : ℂ) * z = (τ : ℂ) * ((c : ℂ) * (z / (τ : ℂ))) := by field_simp
    rw [this, hmn]
    push_cast
    field_simp
    ring
  rw [GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB', GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB]
  rw [show (c : ℂ) * (z / (τ : ℂ)) = ((c : ℂ) * z) / (τ : ℂ) by ring]
  rw [GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ z, GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ ((c : ℂ) * z)]
  have hee : ee (z ^ 2 / (2 * (τ : ℂ))) ^ (c ^ 2) = ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) := by
    rw [Sieg.cthS_ee_pow]
    congr 1
    push_cast
    ring
  have hE : ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hI : (-Complex.I) ≠ 0 := by simp
  rw [mul_pow, mul_pow, Sieg.cthS_negI_pow c hc, hee]
  field_simp
  rw [mul_comm, mul_div_assoc, div_self (by unfold ee; exact Complex.exp_ne_zero _), mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductModularSTransformStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedThetaQProduct_modularS_transform : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → (∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) → cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  first | exact @GlobalTheory.Sieg.cth_modular_S | exact GlobalTheory.Sieg.cth_modular_S | (intros; apply GlobalTheory.Sieg.cth_modular_S <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmul
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem act_S (x : Fin 2 → ℚ) : act x ModularGroup.S = ![x 1, -x 0] := by
  funext i
  fin_cases i <;> simp [act, ModularGroup.S, Fin.sum_univ_two]

theorem sg_S : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x →
    sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  intro c x τ h
  obtain ⟨hc, hc6, hx⟩ := h
  set z : ℂ := (x 1 : ℂ) * (τ : ℂ) - (x 0 : ℂ) with hz
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h1 : pt x (ModularGroup.S • τ) = z / (τ : ℂ) := by
    rw [pt, UpperHalfPlane.modular_S_smul, hz]
    simp only [UpperHalfPlane.coe_mk]
    field_simp
    ring
  have h2 : pt (act x ModularGroup.S) τ = z := by
    rw [act_S, pt, hz]
    simp
    ring
  have hnot : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n := by
    intro m n heq
    apply hx
    have him := congrArg Complex.im heq
    have hre := congrArg Complex.re heq
    simp [hz, mul_sub] at him hre
    have hpos : 0 < τ.im := τ.im_pos
    have e1 : (c : ℝ) * (x 1 : ℝ) = m := by
      have : ((c : ℝ) * (x 1 : ℝ) - m) * τ.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hpos.ne'
    have e0 : (c : ℝ) * (x 0 : ℝ) = ((-n : ℤ) : ℝ) := by
      rw [← mul_assoc, e1] at hre
      push_cast
      linarith
    refine ⟨⟨-n, ?_⟩, ⟨m, ?_⟩⟩
    · exact_mod_cast e0.symm
    · exact_mod_cast e1.symm
  unfold sg
  rw [h1, h2]
  exact GlobalTheory.T.smoothedThetaQProduct_modularS_transform c τ z hc hc6 hnot

end GlobalTheory.Sieg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmulStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_modularS_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  first | exact @GlobalTheory.Sieg.sg_S | exact GlobalTheory.Sieg.sg_S | (intros; apply GlobalTheory.Sieg.sg_S <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularGroupTSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularGroupTSmul
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem coe_T_smul (τ : ℍ) : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  push_cast; ring

theorem ee_add_one (z : ℂ) : ee (z + 1) = ee z := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (z + 1) = 2 * Real.pi * Complex.I * z + 2 * Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem rowVectorMulIntMatrixSL2_modularGroupT_apply (x : Fin 2 → ℚ) : act x ModularGroup.T 0 = x 0 ∧ act x ModularGroup.T 1 = x 0 + x 1 := by
  simp [act, ModularGroup.T, Fin.sum_univ_two]

theorem pt_T_smul (x : Fin 2 → ℚ) (τ : ℍ) : pt x (ModularGroup.T • τ) = pt (act x ModularGroup.T) τ := by
  obtain ⟨h0, h1⟩ := rowVectorMulIntMatrixSL2_modularGroupT_apply x
  simp only [pt, coe_T_smul, h0, h1]
  push_cast; ring

theorem sg_T_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), sg c x (ModularGroup.T • τ) = sg c (act x ModularGroup.T) τ := by
  intro c x τ
  simp only [sg]
  rw [pt_T_smul, coe_T_smul, ee_add_one]

end GlobalTheory.Sieg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularGroupTSmulStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_modularGroupT_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), sg c x (ModularGroup.T • τ) = sg c (act x ModularGroup.T) τ := by
  first | exact @GlobalTheory.Sieg.sg_T_smul | exact GlobalTheory.Sieg.sg_T_smul | (intros; apply GlobalTheory.Sieg.sg_T_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndT
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndT
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem act_one_gen (x : Fin 2 → ℚ) : act x 1 = x := by
  funext i
  fin_cases i <;> simp [act, Fin.sum_univ_two]

theorem act_mul_gen (x : Fin 2 → ℚ) (γ δ : SL(2, ℤ)) : act x (γ * δ) = act (act x γ) δ := by
  funext i
  simp only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem modular_law_of_generators (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ)
    (hP : ∀ x γ, P x → P (act x γ))
    (hS : ∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ)
    (hT : ∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) :
    ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {γ | ∀ x τ, P x → f x (γ • τ) = f (act x γ) τ}
      one_mem' := by
        intro x τ _
        simp [act_one_gen]
      mul_mem' := by
        intro γ δ hγ hδ x τ hx
        rw [mul_smul, hγ x _ hx, hδ _ τ (hP x γ hx), act_mul_gen]
      inv_mem' := by
        intro γ hγ x τ hx
        have h := hγ (act x γ⁻¹) (γ⁻¹ • τ) (hP x _ hx)
        rw [smul_inv_smul, ← act_mul_gen, inv_mul_cancel, act_one_gen] at h
        exact h.symm }
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ H := by
    rw [Subgroup.closure_le]
    intro γ hγ
    rcases hγ with rfl | rfl
    · exact hS
    · exact hT
  intro γ
  have : γ ∈ H := hle (by rw [_root_.SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ)
  exact this

end GlobalTheory.Sieg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndTStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modular_law_of_s_and_t : ∀ (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ), (∀ x γ, P x → P (act x γ)) → (∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ) → (∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) → ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.modular_law_of_generators | exact GlobalTheory.Sieg.modular_law_of_generators | (intros; apply GlobalTheory.Sieg.modular_law_of_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformation
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_smul (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ) (hx : admitted c x) :
    sg c x (γ • τ) = sg c (act x γ) τ :=
  GlobalTheory.T.modular_law_of_s_and_t (admitted c) (sg c) (fun x γ h => GlobalTheory.T.admissible_of_sl2_action c x γ h)
    (fun x τ h => GlobalTheory.T.smoothedSiegelUnit_modularS_smul c x τ h) (fun x τ _ => GlobalTheory.T.smoothedSiegelUnit_modularGroupT_smul c x τ) γ x τ hx

end GlobalTheory.Sieg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformationStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_function_transformation : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ), admitted c x → sg c x (γ • τ) = sg c (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.sg_smul | exact GlobalTheory.Sieg.sg_smul | (intros; apply GlobalTheory.Sieg.sg_smul <;> assumption)
end
