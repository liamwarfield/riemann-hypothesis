module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Formalism.PairingDivisors.StatementN

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceUnitSetEqSmoothingMulPieceRaw
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.Smoothing

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem zpow_congr_of_pow_eq_one {ζ : K} {M : ℕ} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨s, hs⟩ := h.dvd
  have hb : b = a + M * s := by linarith
  rw [hb, zpow_add₀ hz, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem eisF_congr_mod {j M : ℕ} (hM : 0 < M) {ζ : K} (hζ : ζ ^ M = 1) {a₁ a₂ b₁ b₂ : ℤ}
    (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) :
    eisF j M ζ a₁ a₂ = eisF j M ζ b₁ b₂ := by
  funext n
  have h₁' : a₁ % (M : ℤ) = b₁ % (M : ℤ) := h₁
  have hc : const0 j M ζ a₁ a₂ = const0 j M ζ b₁ b₂ := by
    have hd : ((M : ℤ) ∣ a₁) ↔ ((M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁']
    have hf : frc M a₁ = frc M b₁ := by unfold frc; rw [h₁']
    unfold const0
    rw [zpow_congr_of_pow_eq_one hM hζ h₂, hf]
    simp only [hd]
  have hp : coefPos j M ζ a₁ a₂ n = coefPos j M ζ b₁ b₂ n := by
    unfold coefPos
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have e1 : ∀ z : ℤ, z ≡ a₁ [ZMOD M] ↔ z ≡ b₁ [ZMOD M] :=
      fun z => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    rw [zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)).neg]
    simp only [e1]
  unfold eisF
  rw [hc, hp]

omit [CharZero K] in
theorem cmul_expand (a b a' b' : K) (f g h l : ℕ → K) (r : ℕ) :
    cmul (fun i => a * f i - b * g i) (fun i => a' * h i - b' * l i) r =
      a * a' * cmul f h r - a * b' * cmul f l r - b * a' * cmul g h r + b * b' * cmul g l r := by
  unfold cmul
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem not_dvd_val_iff_isUnit {p n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) (y : ZMod (p ^ n)) :
    ¬ p ∣ y.val ↔ IsUnit y := by
  have h := ZMod.isUnit_iff_coprime y.val (p ^ n)
  rw [ZMod.natCast_zmod_val] at h
  rw [h, Nat.coprime_pow_right_iff hn, Nat.coprime_comm, hp.out.coprime_iff_not_dvd]

theorem isUnit_intCast_of_not_dvd {p n : ℕ} [hp : Fact p.Prime] {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : IsUnit (c : ZMod (p ^ n)) := by
  have h1 : IsCoprime (p : ℤ) c :=
    (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hc
  obtain ⟨a, b, hab⟩ := (h1.pow_left (m := n))
  have h2 : ((a * (p : ℤ) ^ n + b * c : ℤ) : ZMod (p ^ n)) = 1 := by rw [hab]; simp
  have h3 : ((p : ZMod (p ^ n))) ^ n = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  push_cast at h2
  rw [h3, mul_zero, zero_add, mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

def diagGL {R : Type*} [CommRing R] (u v : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![(u : R), v], Matrix.diagonal ![((u⁻¹ : Rˣ) : R), ((v⁻¹ : Rˣ) : R)],
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp,
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp⟩

theorem diagGL_mul_zero {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 j =
      (u : R) * (γ : Matrix (Fin 2) (Fin 2) R) 0 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_one {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 j =
      (v : R) * (γ : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_det {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      (u : R) * v * (γ : Matrix (Fin 2) (Fin 2) R).det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [diagGL_mul_zero, diagGL_mul_one]
  ring

theorem diagGL_mul_mem {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (u v : (ZMod (p ^ n))ˣ)
    (γ : GL (Fin 2) (ZMod (p ^ n))) : diagGL u v * γ ∈ unitSet p n ↔ γ ∈ unitSet p n := by
  simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, not_dvd_val_iff_isUnit hn,
    diagGL_mul_zero, diagGL_mul_one, Units.isUnit_units_mul]

end GlobalTheory.KummerEisensteinGalois.Smoothing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShell
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShell
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L]

theorem approxRoot_exists_val_pow {p : ℕ} {v : Valuation L ℝ≥0} {F : Subfield L}
    (hA : ApproxRoot p v F) {u : L} (hu : u ∈ F) (hu0 : u ≠ 0) :
    ∃ w ∈ F, v w ^ p = v u := by
  obtain ⟨θ, hθ, h⟩ := hA
  obtain ⟨w, hw, hle⟩ := h u hu
  have hvu : 0 < v u := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hu0)
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact lt_of_le_of_lt hle (mul_lt_of_lt_one_left hvu hθ)
  refine ⟨w, hw, ?_⟩
  rw [← map_pow]
  exact Valuation.map_eq_of_sub_lt v hlt

theorem approxRoot_exists_root_of_p {p : ℕ} (hp : p.Prime) {v : Valuation L ℝ≥0} {F : Subfield L}
    (hA : ApproxRoot p v F) (hp0 : 0 < v (p : L)) :
    ∀ k : ℕ, ∃ π ∈ F, v π ^ (p ^ k) = v (p : L) := by
  intro k
  induction k with
  | zero => exact ⟨(p : L), natCast_mem F p, by simp⟩
  | succ k ih =>
    obtain ⟨π, hπ, hv⟩ := ih
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow (pow_ne_zero _ hp.ne_zero)] at hv
      exact hp0.ne hv
    obtain ⟨w, hw, hw'⟩ := approxRoot_exists_val_pow hA hπ hπ0
    refine ⟨w, hw, ?_⟩
    rw [pow_succ', pow_mul, hw', hv]

theorem exists_scale_shell (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (hp : p.Prime)
    (F : Subfield L) (hA : ApproxRoot p v F) (hp0 : 0 < v (p : L)) (hp1 : v (p : L) < 1)
    (r : ℝ≥0) (hr : r < 1) (x : L) (hx : x ≠ 0) :
    ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pow_pos hp0 p) hr
  obtain ⟨π, hπ, hv⟩ := approxRoot_exists_root_of_p hp hA hp0 n
  set s := v π with hs
  set t := s ^ p with ht
  have hrt : r < t := by
    by_contra h
    push_neg at h
    have h1 : t ^ (p ^ n) ≤ r ^ (p ^ n) := pow_le_pow_left₀ (by positivity) h _
    have h2 : r ^ (p ^ n) ≤ r ^ n :=
      pow_le_pow_of_le_one (by positivity) hr.le (Nat.lt_pow_self hp.one_lt).le
    have h3 : t ^ (p ^ n) = v (p : L) ^ p := by rw [ht, ← pow_mul, mul_comm, pow_mul, hv]
    exact absurd (lt_of_le_of_lt (h3 ▸ h1.trans h2) hn) (lt_irrefl _)
  have hs1 : s < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := p ^ n) h
    rw [hv] at this
    exact absurd hp1 (not_lt.mpr this)
  have ht1 : t < 1 := pow_lt_one₀ (by positivity) hs1 hp.ne_zero
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) hrt
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have h0 : s = 0 := by rw [hs, map_zero]
    rw [ht, h0, zero_pow hp.ne_zero] at ht0
    exact lt_irrefl _ ht0
  have hvx : 0 < v x := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hx)
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow hvx ((one_lt_inv₀ ht0).mpr ht1)
  refine ⟨π ^ (m + 1), zpow_mem hπ _, zpow_ne_zero _ hπ0, ?_⟩
  have hval : v (x * (π ^ (m + 1)) ^ p) = v x * t ^ (m + 1) := by
    rw [map_mul, map_pow, map_zpow₀, ← hs, ht, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul, mul_comm (m + 1)]
  rw [hval]
  have htne : t ≠ 0 := ht0.ne'
  constructor
  · have e : t⁻¹ ^ m * t ^ (m + 1) = t := by
      rw [inv_zpow, zpow_add_one₀ htne, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ htne), one_mul]
    calc r < t := hrt
      _ = t⁻¹ ^ m * t ^ (m + 1) := e.symm
      _ < v x * t ^ (m + 1) := mul_lt_mul_of_pos_right hm1 (zpow_pos ht0 _)
  · have e : t⁻¹ ^ (m + 1) * t ^ (m + 1) = 1 := by
      rw [inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ htne)]
    calc v x * t ^ (m + 1) ≤ t⁻¹ ^ (m + 1) * t ^ (m + 1) := mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = 1 := e

theorem klc_scale : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L,
    ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ r : ℝ≥0, r < 1 → ∀ x : L, x ≠ 0 →
    ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 :=
  fun L _ v p hp F hA hp0 hp1 r hr x hx => exists_scale_shell L v p hp F hA hp0 hp1 r hr x hx

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShellStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pth_power_scale_thin_shell : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ r : ℝ≥0, r < 1 → ∀ x : L, x ≠ 0 → ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 := by
  first | exact @GlobalTheory.AlmostEt.klc_scale | exact GlobalTheory.AlmostEt.klc_scale | (intros; apply GlobalTheory.AlmostEt.klc_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransform
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem slash_periodic_comp {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ}
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) (x : SL(2, ℤ)) :
    Function.Periodic ((f ∣[k] x) ∘ ofComplex) (M : ℝ) := by
  have key : ∀ τ : ℍ, (f ∣[k] x) ((M : ℝ) +ᵥ τ) = (f ∣[k] x) τ := by
    intro τ
    have hT : (ModularGroup.T ^ (M : ℤ)) • τ = (M : ℝ) +ᵥ τ := by
      rw [modular_T_zpow_smul]; simp
    have hδ : x * ModularGroup.T ^ (M : ℤ) * x⁻¹ ∈ Γ := by
      have h1 : ModularGroup.T ^ (M : ℤ) ∈ CongruenceSubgroup.Gamma M := by
        simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
      exact hΓ ((CongruenceSubgroup.Gamma_normal M).conj_mem _ h1 x)
    have e : (f ∣[k] x) ∣[k] (ModularGroup.T ^ (M : ℤ)) = f ∣[k] x := by
      rw [← SlashAction.slash_mul,
        (inv_mul_cancel_right (x * ModularGroup.T ^ (M : ℤ)) x).symm,
        SlashAction.slash_mul, hf.1 _ hδ]
    have h := congrFun e τ
    have hden : denom (ModularGroup.T ^ (M : ℤ) : SL(2, ℤ)) τ = 1 := by
      rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
    rw [ModularForm.SL_slash_apply (f := f ∣[k] x), hT, hden, one_zpow, mul_one] at h
    exact h
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simp [hw]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert key ⟨w, hw⟩ using 2
    ext
    simp [ofComplex_apply_of_im_pos hw', add_comm]
  · push_neg at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem analyticAt_cuspFunction_slash {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ}
    (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) (x : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction (M : ℝ) (f ∣[k] x)) 0 :=
  analyticAt_cuspFunction_zero (by exact_mod_cast hM) (slash_periodic_comp hΓ hf x)
    (mdiff_slash hf.2.1 k x) (hf.2.2 x)

theorem qParam_one_vadd_eq_exp_mul (M : ℕ) (τ : ℍ) :
    Function.Periodic.qParam (M : ℝ) (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / M) * Function.Periodic.qParam (M : ℝ) (τ : ℂ) := by
  simp only [Function.Periodic.qParam, coe_vadd, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_unique_of_hasSum {h : ℝ} {g : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m => c m • Function.Periodic.qParam h (τ : ℂ) ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem co_transform (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) (hM : 0 < M)
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) :
    (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n =
        Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧
      (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧
      (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun x n => ?_, fun γ hγ x n => ?_, fun hk x n => ?_⟩
  · set ζ := Complex.exp (2 * Real.pi * Complex.I / M)
    have happ : ∀ τ : ℍ, (f ∣[k] (x * ModularGroup.T)) τ = (f ∣[k] x) ((1 : ℝ) +ᵥ τ) := by
      intro τ
      rw [slash_mul_apply, modular_T_smul]
      have hden : denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = 1 := by
        rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
      rw [hden, one_zpow, mul_one]
    have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => (ζ ^ m * co M k f x m) •
        Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ m) ((f ∣[k] (x * ModularGroup.T)) τ) := by
      intro τ
      have h := hasSum_qExpansion hM' (slash_periodic_comp hΓ hf x) (mdiff_slash hf.2.1 k x)
        (hf.2.2 x) ((1 : ℝ) +ᵥ τ)
      rw [happ]
      convert h using 1
      funext m
      rw [qParam_one_vadd_eq_exp_mul, co, smul_eq_mul, smul_eq_mul, mul_pow]
      ring
    exact (coeff_unique_of_hasSum hM'
      (analyticAt_cuspFunction_slash hM hΓ hf (x * ModularGroup.T)) hsum n).symm
  · simp only [co, hf.slash_mul hγ x]
  · simp only [co, slash_neg_of_odd hk f x]
    rw [qExpansion_neg (analyticAt_cuspFunction_slash hM hΓ hf x)]
    simp

end GlobalTheory.OddFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransformStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slashQExpansionCoeffWidth_transform : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧ (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧ (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  first | exact @GlobalTheory.OddFrame.co_transform | exact GlobalTheory.OddFrame.co_transform | (intros; apply GlobalTheory.OddFrame.co_transform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoin
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoin
noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
open Polynomial

namespace GlobalTheory.K5.Level

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev Bn (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) Ω :=
  Algebra.adjoin (O0 p) {T.ζ n, T.qq n}

theorem bn_le_succ (T : Tower p Ω) (n : ℕ) : Bn T n ≤ Bn T (n + 1) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · rw [← T.ζpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _
  · rw [← T.qpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _

theorem bn_mono (T : Tower p Ω) : Monotone (Bn T) :=
  monotone_nat_of_le_succ (bn_le_succ T)

theorem bn_le_B (T : Tower p Ω) (n : ℕ) :
    Bn T n ≤ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  apply Algebra.adjoin_mono
  rintro x (rfl | rfl)
  · exact Or.inl ⟨n, rfl⟩
  · exact Or.inr ⟨n, rfl⟩

theorem exists_mem_bn (T : Tower p Ω) {b : Ω}
    (hb : b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)) : ∃ n, b ∈ Bn T n := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact ⟨n, Algebra.subset_adjoin (by simp)⟩
    · exact ⟨n, Algebra.subset_adjoin (by simp)⟩
  | algebraMap r => exact ⟨0, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max m k, Subalgebra.add_mem _ (bn_mono T (le_max_left m k) hm)
      (bn_mono T (le_max_right m k) hk)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max m k, Subalgebra.mul_mem _ (bn_mono T (le_max_left m k) hm)
      (bn_mono T (le_max_right m k) hk)⟩

theorem bn_le_range (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι) :
    Bn T n ≤ ι.range := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact ⟨xn p n, h.1⟩
  · exact ⟨yn p n, h.2⟩

theorem range_le_bn (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι)
    (w : On p n) : ι w ∈ Bn T n := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hX : ι (Ideal.Quotient.mk (towerIdeal p n) (C X)) ∈ Bn T n := by
    have : ι (xn p n) = T.ζ n := h.1
    simp only [xn] at this
    rw [this]; exact Algebra.subset_adjoin (by simp)
  have hY : ι (Ideal.Quotient.mk (towerIdeal p n) X) ∈ Bn T n := by
    have : ι (yn p n) = T.qq n := h.2
    simp only [yn] at this
    rw [this]; exact Algebra.subset_adjoin (by simp)
  have hC : ∀ a : Polynomial (O0 p), ι (Ideal.Quotient.mk (towerIdeal p n) (C a)) ∈ Bn T n := by
    intro a
    induction a using Polynomial.induction_on with
    | C c =>
      have : (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c := rfl
      rw [this, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg =>
      set_option synthInstance.maxHeartbeats 200000 in
        simpa only [map_add] using Subalgebra.add_mem (Bn T n) hf hg
    | monomial k c _ =>
      simp only [map_mul, map_pow]
      refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)
      have : (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c := rfl
      rw [this, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ c
  induction P using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg =>
    set_option synthInstance.maxHeartbeats 200000 in
      simpa only [map_add] using Subalgebra.add_mem (Bn T n) hf hg
  | monomial k a _ =>
    simp only [map_mul, map_pow]
    exact Subalgebra.mul_mem _ (hC a) (Subalgebra.pow_mem _ hY _)

end GlobalTheory.K5.Level

theorem GlobalTheory.K5.exists_level_of_mem_adjoin :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
      ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
        ∃ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (w : On p n), 1 ≤ n ∧ IsEmb T n ι ∧ ι w = b ∧
          ∀ w' : On p n, ι w' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  intro p _ Ω _ _ _ T b hb
  obtain ⟨m, hm⟩ := GlobalTheory.K5.Level.exists_mem_bn T hb
  have hm1 : b ∈ GlobalTheory.K5.Level.Bn T (m + 1) := GlobalTheory.K5.Level.bn_le_succ T m hm
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T (m + 1)
  obtain ⟨w, hw⟩ := GlobalTheory.K5.Level.bn_le_range T (m + 1) ι hι hm1
  exact ⟨m + 1, ι, w, Nat.le_add_left 1 m, hι, hw, fun w' =>
    GlobalTheory.K5.Level.bn_le_B T (m + 1) (GlobalTheory.K5.Level.range_le_bn T (m + 1) ι hι w')⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoinStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (w : On p n), 1 ≤ n ∧ IsEmb T n ι ∧ ι w = b ∧ ∀ w' : On p n, ι w' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  first | exact @GlobalTheory.K5.exists_level_of_mem_adjoin | exact GlobalTheory.K5.exists_level_of_mem_adjoin | (intros; apply GlobalTheory.K5.exists_level_of_mem_adjoin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorOfChar
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorOfChar
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem zeta_pow_val_add {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζN : ζ ^ N = 1) (x y : ZMod N) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) N, pow_add, pow_mul, hζN, one_pow, one_mul]

theorem kummer_generator_of_char : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (E : IntermediateField K Ω) (χ : (Ω ≃ₐ[K] Ω) → ZMod N),
  IsLocallyConstant χ → (∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, χ (g * h) = χ g + χ h) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ E ∧ ∀ g ∈ E.fixingSubgroup, g θ = ζ ^ (χ g).val * θ := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix E χ hχ hadd
  haveI : NeZero N := ⟨hN.ne'⟩
  classical
  set H := E.fixingSubgroup with hH
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  have h1 : χ 1 = 0 := by
    have := hadd 1 H.one_mem 1 H.one_mem
    simpa using this

  have hV : {g : Ω ≃ₐ[K] Ω | χ g = 0} ∈ nhds (1 : Ω ≃ₐ[K] Ω) := by
    have := (hχ.isOpen_fiber (χ 1)).mem_nhds (show (1 : Ω ≃ₐ[K] Ω) ∈ χ ⁻¹' {χ 1} from rfl)
    simpa [h1] using this
  obtain ⟨F, hFfin, hFV⟩ := (krullTopology_mem_nhds_one_iff K Ω _).mp hV

  let r : (Ω ≃ₐ[K] Ω) → (F →ₐ[K] Ω) := fun g => (g : Ω →ₐ[K] Ω).comp F.val
  have hr : ∀ g x, r g x = g (x : Ω) := fun _ _ => rfl
  have hrχ : ∀ g ∈ H, ∀ h ∈ H, r g = r h → χ g = χ h := by
    intro g hg h hh he
    have hm : h⁻¹ * g ∈ H := H.mul_mem (H.inv_mem hh) hg
    have hF : h⁻¹ * g ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have := congrArg (fun φ => φ ⟨x, hx⟩) he
      simp only [hr] at this
      simp [AlgEquiv.mul_apply, this]
    have h0 : χ (h⁻¹ * g) = 0 := hFV hF
    have := hadd h hh (h⁻¹ * g) hm
    rw [mul_inv_cancel_left, h0, add_zero] at this
    exact this
  haveI : FiniteDimensional K F := hFfin
  let ι := {φ : F →ₐ[K] Ω // ∃ g ∈ H, r g = φ}
  haveI : Finite (F →ₐ[K] Ω) := inferInstance
  haveI : Fintype ι := Fintype.ofFinite ι
  let s : ι → (Ω ≃ₐ[K] Ω) := fun i => i.2.choose
  have hsH : ∀ i, s i ∈ H := fun i => i.2.choose_spec.1
  have hsr : ∀ i, r (s i) = i.1 := fun i => i.2.choose_spec.2
  let a : (Ω ≃ₐ[K] Ω) → Ω := fun g => ζ ^ (χ g).val
  have ha0 : ∀ g, a g ≠ 0 := fun g => pow_ne_zero _ hζ0
  have hamul : ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g * a h := by
    intro g hg h hh
    simp only [a, hadd g hg h hh, zeta_pow_val_add hζN]
  have hafix : ∀ (g h : Ω ≃ₐ[K] Ω), g (a h) = a h := by
    intro g h; simp only [a, map_pow, hfix]
  let w : ι → Ω := fun i => (a (s i))⁻¹

  let v : ι → (F →* Ω) := fun i => (i.1 : F →+* Ω).toMonoidHom
  have hv : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom F Ω).comp v hv
  obtain ⟨c, hc⟩ : ∃ c : F, ∑ i, w i * i.1 c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∑ i, w i • ((v i : F →* Ω) : F → Ω) = 0 := by
      funext x
      simpa [Finset.sum_apply, v] using hcon x
    have := Fintype.linearIndependent_iff.mp hli w hz ⟨r 1, 1, H.one_mem, rfl⟩
    exact inv_ne_zero (ha0 _) this
  have hmain : ∀ g ∈ H, g (∑ i, w i * i.1 c) = a g * ∑ i, w i * i.1 c := by
    intro g hg
    let e : ι → ι := fun i => ⟨r (g * s i), g * s i, H.mul_mem hg (hsH i), rfl⟩
    have hic : ∀ i : ι, i.1 c = s i (c : Ω) := by
      intro i; rw [← hsr i]; exact hr _ _
    have hec : ∀ i, (e i).1 c = g (i.1 c) := by
      intro i; rw [hic i]; rfl
    have hwe : ∀ i, w i = a g * w (e i) := by
      intro i
      have hχe : χ (s (e i)) = χ (g * s i) :=
        hrχ _ (hsH (e i)) _ (H.mul_mem hg (hsH i)) (hsr (e i))
      have : a (s (e i)) = a g * a (s i) := by
        rw [← hamul g hg (s i) (hsH i)]; simp only [a, hχe]
      simp only [w, this, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ha0 g), one_mul]
    have he : Function.Injective e := by
      intro i j hij
      have h2 : r (g * s i) = r (g * s j) := congrArg Subtype.val hij
      apply Subtype.ext
      rw [← hsr i, ← hsr j]
      apply AlgHom.ext
      intro x
      have := DFunLike.congr_fun h2 x
      simp only [hr, AlgEquiv.mul_apply] at this
      simpa [hr] using g.injective this
    have hb : Function.Bijective e := Finite.injective_iff_bijective.mp he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    simp only [map_mul, hfix, w, map_inv₀, hafix]
    refine (Fintype.sum_bijective e hb _ _ ?_)
    intro i
    have h3 := hwe i
    simp only [w] at h3
    rw [h3, ← hec i]; ring
  refine ⟨∑ i, w i * i.1 c, hc, ?_, ?_⟩
  · haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro g hg
    have key := hmain g hg
    rw [map_pow, key, mul_pow]
    have : a g ^ N = 1 := by
      show (ζ ^ (χ g).val) ^ N = 1
      rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]
    rw [this, one_mul]
  · exact hmain

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorOfCharStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummer_generator_of_locallyConstant_hom : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (E : IntermediateField K Ω) (χ : (Ω ≃ₐ[K] Ω) → ZMod N),
  IsLocallyConstant χ → (∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, χ (g * h) = χ g + χ h) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ E ∧ ∀ g ∈ E.fixingSubgroup, g θ = ζ ^ (χ g).val * θ := by
  first | exact @GlobalTheory.kummer_generator_of_char | exact GlobalTheory.kummer_generator_of_char | (intros; apply GlobalTheory.kummer_generator_of_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesEqSumSingleMulPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesEqSumSingleMulPow
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem powerSeries_pow_eq_expand_zmod (p : ℕ) [hp : Fact p.Prime] (g : PowerSeries (ZMod p)) :
    g ^ p = PowerSeries.expand p hp.out.ne_zero g := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) (f := g) p hp.out.ne_zero
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

theorem powerSeries_eq_sum_X_pow_mul_pow (p : ℕ) [hp : Fact p.Prime] (F : PowerSeries (ZMod p)) :
    ∃ G : Fin p → PowerSeries (ZMod p),
      F = ∑ j : Fin p, PowerSeries.X ^ (j : ℕ) * G j ^ p := by
  have hp0 : 0 < p := hp.out.pos
  refine ⟨fun j => PowerSeries.mk fun i => PowerSeries.coeff (p * i + j) F, ?_⟩
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [powerSeries_pow_eq_expand_zmod, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_expand]
  rw [Finset.sum_eq_single (⟨n % p, Nat.mod_lt n hp0⟩ : Fin p)]
  · have h1 : n % p ≤ n := Nat.mod_le n p
    have h2 : p ∣ n - n % p := Nat.dvd_sub_mod n
    simp only [h1, h2, if_true, PowerSeries.coeff_mk]
    congr 1
    rw [Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]
  · intro j _ hj
    split_ifs with h1 h2
    · exfalso
      apply hj
      ext
      simp only
      have hj' : (j : ℕ) < p := j.2
      obtain ⟨c, hc⟩ := h2
      have : n = p * c + j := by omega
      rw [this, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hj']
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem laurentSeries_eq_sum_single_mul_pow :
    ∀ (p : ℕ) [Fact p.Prime] (f : LaurentSeries (ZMod p)), ∃ g : Fin p → LaurentSeries (ZMod p),
      f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ZMod p) * g j ^ p := by
  intro p hp f
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  set N : ℕ := f.order.natAbs with hN
  set m : ℕ := (f.order + p * N).toNat with hm
  have hm' : ((m : ℕ) : ℤ) = f.order + p * N := by
    rw [hm, Int.toNat_of_nonneg]
    have : (f.order.natAbs : ℤ) = |f.order| := Int.natCast_natAbs _
    rw [hN, this]
    have h2 : -f.order ≤ |f.order| := neg_le_abs _
    have h3 : 0 ≤ |f.order| := abs_nonneg _
    nlinarith
  obtain ⟨G, hG⟩ := powerSeries_eq_sum_X_pow_mul_pow p (PowerSeries.X ^ m * f.powerSeriesPart)
  refine ⟨fun j => HahnSeries.single (-(N : ℤ)) (1 : ZMod p) * HahnSeries.ofPowerSeries ℤ _ (G j), ?_⟩
  have key : f = HahnSeries.single (-(p * N : ℤ)) (1 : ZMod p) *
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.X ^ m * f.powerSeriesPart) := by
    conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart f]
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, hm',
      mul_one]
    congr 2
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, hG, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow, map_pow, mul_pow, HahnSeries.single_pow, one_pow]
  have : (p • (-(N : ℤ))) = -(p * N : ℤ) := by rw [nsmul_eq_mul]; ring
  rw [this]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesEqSumSingleMulPowStatement
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime : ∀ (p : ℕ) [Fact p.Prime] (f : LaurentSeries (ZMod p)), ∃ g : Fin p → LaurentSeries (ZMod p), f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ZMod p) * g j ^ p := by
  first | exact @GlobalTheory.laurentSeries_eq_sum_single_mul_pow | exact GlobalTheory.laurentSeries_eq_sum_single_mul_pow | (intros; apply GlobalTheory.laurentSeries_eq_sum_single_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombination
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.LauZ

variable (p : ℕ) [hp : Fact p.Prime]

def red : Lau p →+* LaurentSeries (ZMod p) where
  toFun f := f.map (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_one' := by
    ext n
    show PadicInt.toZMod ((1 : Lau p).coeff n) = (1 : LaurentSeries (ZMod p)).coeff n
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> simp
  map_mul' x y := HahnSeries.map_mul _
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem red_coeff (f : Lau p) (n : ℤ) : (red p f).coeff n = PadicInt.toZMod (f.coeff n) := rfl

def lift (F : LaurentSeries (ZMod p)) : Lau p :=
  ⟨fun n => ((F.coeff n).val : ℤ_[p]), F.isPWO_support'.mono fun n hn => by
    simp only [Function.mem_support] at hn ⊢
    intro h; apply hn; rw [h]; simp⟩

theorem red_lift (F : LaurentSeries (ZMod p)) : red p (lift p F) = F := by
  ext n
  rw [red_coeff]
  show PadicInt.toZMod (((F.coeff n).val : ℕ) : ℤ_[p]) = F.coeff n
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem red_single (a : ℤ) : red p (HahnSeries.single a (1 : ℤ_[p])) = HahnSeries.single a (1 : ZMod p) := by
  ext n
  rw [red_coeff]
  by_cases h : n = a
  · subst h; simp
  · simp [HahnSeries.coeff_single_of_ne h]

theorem exists_pow_comb (f : Lau p) : ∃ (g : Fin p → Lau p) (h : Lau p),
    f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  obtain ⟨G, hG⟩ := GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime p (red p f)
  set S : Lau p := ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * lift p (G j) ^ p
  have hS : red p S = red p f := by
    rw [hG]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [S, map_sum, map_mul, map_pow, red_single, red_lift]
  have h0 : (f - S).map (PadicInt.toZMod (p := p)).toNonUnitalRingHom = 0 := by
    show red p (f - S) = 0
    rw [map_sub, hS, sub_self]
  obtain ⟨h, hh⟩ := (GlobalTheory.K5.Basic.dvd_iff_map p (f - S)).2 h0
  exact ⟨fun j => lift p (G j), h, by rw [← hh, add_sub_cancel]⟩

end GlobalTheory.K5.LauZ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombinationStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination : ∀ (p : ℕ) [Fact p.Prime] (f : Lau p), ∃ (g : Fin p → Lau p) (h : Lau p), f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  first | exact @GlobalTheory.K5.LauZ.exists_pow_comb | exact GlobalTheory.K5.LauZ.exists_pow_comb | (intros; apply GlobalTheory.K5.LauZ.exists_pow_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesMinPadicValBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesMinPadicValBound
namespace GlobalTheory

open Formalism.PairingDivisionLocalBalance

theorem exists_pow_ne_one_mod (l n : ℕ) (hl : l.Prime) (hn : ¬ (l - 1) ∣ n) :
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ ¬ l ∣ a ^ n - 1 := by
  haveI := Fact.mk hl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hl]
  refine ⟨(g : ZMod l).val, ?_, ZMod.val_coe_unit_coprime g, ?_⟩
  · by_contra h
    push_neg at h
    interval_cases hv : (g : ZMod l).val
    · have : (g : ZMod l) = 0 := (ZMod.val_eq_zero _).mp hv
      exact (Units.ne_zero g) this
    · have h1 : (g : ZMod l) = 1 := by
        rw [← ZMod.natCast_zmod_val (g : ZMod l), hv, Nat.cast_one]
      have : g = 1 := Units.ext h1
      rw [this, orderOf_one] at hord
      exact hn (by rw [← hord]; exact one_dvd n)
  · intro hdvd
    have hpos : 1 ≤ (g : ZMod l).val ^ n := by
      apply Nat.one_le_pow
      rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact Units.ne_zero g
    have h0 : (((g : ZMod l).val ^ n - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hpos, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero] at h0
    have hgn : g ^ n = 1 := Units.ext (by simpa using h0)
    exact hn (hord ▸ orderOf_dvd_of_pow_eq_one hgn)

theorem cmValues_minPadicVal_bound : MinVal := by
  intro l n hl hn2 hne
  haveI := Fact.mk hl
  have hn0 : n ≠ 0 := by omega
  unfold mE
  simp only [Nat.padicValNat_def]
  by_cases h2 : l = 2
  · subst h2
    refine ⟨3, by norm_num, by norm_num, ?_⟩
    have h := padicValNat.pow_two_sub_one (x := 3) (n := n) (by norm_num) (by norm_num) hn0 hne
    have h4 : multiplicity 2 (3 + 1) = 2 := by
      norm_num
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have h2' : multiplicity 2 (3 - 1) = 1 := by
      norm_num
    rw [h4, h2'] at h
    simp only [if_true]
    omega
  · simp only [h2, if_false]
    have hodd : Odd l := hl.odd_of_ne_two h2
    by_cases hd : (l - 1) ∣ n
    · simp only [hd, if_true]
      refine ⟨l + 1, by have := hl.two_le; omega, ?_, ?_⟩
      · first
          | exact (Nat.coprime_succ_self l)
          | exact (Nat.coprime_self_succ l)
          | simp
      · have h := padicValNat.pow_sub_pow (p := l) (x := l + 1) (y := 1) hodd (by have := hl.one_lt; omega)
          (by simp) (by
            intro hdv
            have : l ∣ 1 := (Nat.dvd_add_right (dvd_refl l)).mp hdv
            exact hl.one_lt.ne' (Nat.dvd_one.mp this)) hn0
        rw [one_pow] at h
        rw [h, show l + 1 - 1 = l by omega, padicValNat_self]
    · simp only [hd, if_false]
      obtain ⟨a, ha2, hac, hnd⟩ := exists_pow_ne_one_mod l n hl hd
      exact ⟨a, ha2, hac, padicValNat.eq_zero_of_not_dvd hnd⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesMinPadicValBoundStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerValuations_minVal : Formalism.PairingDivisionLocalBalance.MinVal := by
  first | exact @GlobalTheory.cmValues_minPadicVal_bound | exact GlobalTheory.cmValues_minPadicVal_bound | (intros; apply GlobalTheory.cmValues_minPadicVal_bound <;> assumption)
end
end
