module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeff
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelations
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeTAdjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformEigenvalueEqCharMulConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralSelfNeZeroCuspForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralSelfNeZeroCuspForm
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.PetPos

theorem volume_isOpenPosMeasure : (volume : Measure ℍ).IsOpenPosMeasure := by
  have h0 : (volume.comap UpperHalfPlane.coe : Measure ℍ).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  have hm : Continuous fun z : ℍ => (NNReal.mk z.im z.im_pos.le : NNReal) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  have hc : Continuous fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) :=
    (continuous_const.div₀ hm (fun x => NNReal.ne_iff.mp x.im_ne_zero)).pow 2
  refine ⟨fun U hU hne => ?_⟩
  rw [UpperHalfPlane.volume_def, withDensity_apply _ hU.measurableSet]
  refine ne_of_gt ?_
  have hmeas : Measurable fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal) :=
    (ENNReal.continuous_coe.comp hc).measurable
  rw [setLIntegral_pos_iff hmeas]
  have hsupp : Function.support (fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal)) = Set.univ := by
    ext z
    simp [z.im_ne_zero]
    intro h
    have h' := congrArg Subtype.val h
    simp [z.im_ne_zero] at h'
  rw [hsupp, Set.univ_inter]
  exact hU.measure_pos _ hne

theorem norm_ch_eq_one {L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) (γ : SL(2, ℤ))
    (hγ : (L : ℤ) ∣ γ 1 0) : ‖ch ε (γ 1 1)‖ = 1 := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have h1 : ((γ 1 1 : ℤ) : ZMod N) * ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    rw [hc, mul_zero, sub_zero] at h
    rw [mul_comm]
    exact h
  obtain ⟨u, hu⟩ := IsUnit.of_mul_eq_one _ h1
  show ‖ε ((γ 1 1 : ℤ) : ZMod N)‖ = 1
  rw [← hu]
  exact DirichletCharacter.unit_norm_eq_one ε u

theorem norm_sq_mul_im_pow_smul {k L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k := by
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← ModularGroup.denom_apply]
    exact UpperHalfPlane.denom_ne_zero _ _
  have hpos : 0 < ‖((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)‖ := norm_pos_iff.mpr hD
  rw [hf γ hγ τ, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, norm_mul, norm_mul,
    norm_ch_eq_one ε hNL γ hγ, one_mul, norm_pow, div_pow, Complex.normSq_eq_norm_sq]
  field_simp
  ring

theorem pet_self_ne_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  intro k L N ε ρ h hk hL hN hW hCF hh
  haveI : (volume : Measure ℍ).IsOpenPosMeasure := volume_isOpenPosMeasure
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hP : PolyB h := hCF.1.1
  have hInv : Inv k L (ch ε) (qs h) := hCF.1.2
  have hqc : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hP).2
  set Φ : ℍ → ℝ := fun τ => ‖qs h τ‖ ^ 2 * τ.im ^ k with hΦ
  set G : ℍ → ℝ := fun τ => ρ τ * Φ τ with hG
  have hΦc : Continuous Φ := (hqc.norm.pow 2).mul (UpperHalfPlane.continuous_im.pow k)
  have hGnn : 0 ≤ G := fun τ => mul_nonneg (hW.nonneg τ) (by positivity)
  have heq : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs h τ * (τ.im : ℂ) ^ k)) =
      fun τ => ((G τ : ℝ) : ℂ) := by
    funext τ
    rw [Complex.conj_mul']
    simp only [hG, hΦ]
    push_cast
    ring
  have hint := GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ (qs h) hk hL hN hW hCF hqc.aestronglyMeasurable
    (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth h hP)
  rw [heq] at hint
  have hGi : Integrable G := by
    have := hint.re
    simpa using this
  intro hzero
  have hpet : pet k ρ (qs h) (qs h) = ((∫ τ, G τ : ℝ) : ℂ) := by
    unfold pet
    rw [heq, integral_complex_ofReal]
  rw [hpet, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg hGnn hGi] at hzero
  have hmp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
    intro γ
    have hm := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
    convert hm using 1
    ext z
    simp
  have hall : ∀ᵐ τ ∂(volume : Measure ℍ), ∀ γ : Gamma0 L, G ((γ : SL(2, ℤ)) • τ) = 0 := by
    rw [ae_all_iff]
    intro γ
    have h1 := (hmp (γ : SL(2, ℤ))).quasiMeasurePreserving.ae_eq_comp hzero
    filter_upwards [h1] with τ hτ
    simpa using hτ
  have hΦ0 : Φ =ᵐ[volume] 0 := by
    filter_upwards [hall] with τ hτ
    have hterm : ∀ γ : Gamma0 L, Φ τ * ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ
      have hγL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.2)
      have hinv := norm_sq_mul_im_pow_smul ε hN hInv (γ : SL(2, ℤ)) hγL τ
      have h2 := hτ γ
      simp only [hG, hΦ] at h2 ⊢
      rw [hinv] at h2
      rw [mul_comm]
      exact h2
    have hs := (hW.sum τ).mul_left (Φ τ)
    simp only [hterm, mul_one] at hs
    exact hs.unique hasSum_zero
  have hΦz : Φ = 0 := (Continuous.ae_eq_iff_eq volume hΦc continuous_const).mp hΦ0
  apply hh
  have hq0 : qs h = qs 0 := by
    funext τ
    have h3 := congrFun hΦz τ
    simp only [hΦ, Pi.zero_apply] at h3
    have him : τ.im ^ k ≠ 0 := pow_ne_zero _ τ.im_ne_zero
    have h4 : ‖qs h τ‖ ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_right him
    have h5 : qs h τ = 0 := by simpa using h4
    rw [h5]
    simp [qs]
  exact GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth h 0 hP ⟨0, 0, fun n => by simp⟩ hq0

end GlobalTheory.EisM.PetPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralSelfNeZeroCuspFormStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  first | exact @GlobalTheory.EisM.PetPos.pet_self_ne_zero | exact GlobalTheory.EisM.PetPos.pet_self_ne_zero | (intros; apply GlobalTheory.EisM.PetPos.pet_self_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformEigenvalueEqCharMulConj
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisMReal

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (fun n => c * a n) = fun τ => c * qs a τ := by
  funext τ
  unfold qs
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

theorem pet_smul_right (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ h (fun τ => c * f τ) = c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  ring

theorem pet_smul_left (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ (fun τ => c * h τ) f = conj c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [map_mul]
  ring

theorem eig_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g →
    q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  intro k N q χ g hk hN hg hq hqN
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight N hN
  have hT : To k (ch χ q) q g = fun n => g q * g n := hg.eig q hq hqN
  have hadj := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k N N q χ ρ g g hk hN dvd_rfl hq hqN hρ hg.cf hg.cf.1
  have hne : g ≠ 0 := by
    intro h0
    have := hg.one
    rw [h0] at this
    simp at this
  have hP := GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm k N N χ ρ g hk hN dvd_rfl hρ hg.cf hne
  rw [hT, qs_smul, pet_smul_right, pet_smul_left] at hadj
  exact mul_right_cancel₀ hP (hadj.trans (by ring) : g q * pet k ρ (qs g) (qs g) = ch χ q * conj (g q) * pet k ρ (qs g) (qs g))

end GlobalTheory.EisMReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformEigenvalueEqCharMulConjStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depletedCuspEigenform_eigenvalue_eq_char_mul_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g → q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  first | exact @GlobalTheory.EisMReal.eig_conj | exact GlobalTheory.EisMReal.eig_conj | (intros; apply GlobalTheory.EisMReal.eig_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormLseriesExtendsEntire
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormLseriesExtendsEntire
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem div_le_half_sq_add {t x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    t / x ≤ (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 := by
  have key : (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 - t / x = (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by
    field_simp
    ring
  have : 0 ≤ (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by positivity
  linarith

theorem lseriesSummable_of_sq (a : ℕ → ℂ) (k : ℕ)
    (hsq : ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s))
    (s : ℂ) (hs : ((k : ℝ) + 1) / 2 < s.re) : LSeriesSummable a s := by
  set σ := s.re with hσ
  set δ : ℝ := σ - ((k : ℝ) + 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 : Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := hsq δ hδ0
  have h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + δ)) := Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · have : 0 ≤ ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := by positivity
    have : 0 ≤ (n : ℝ) ^ (-(1 + δ)) := by positivity
    linarith
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have e : (n : ℝ) ^ (-(1 + δ)) = (n : ℝ) ^ ((k : ℝ) + δ) * ((n : ℝ) ^ σ)⁻¹ * ((n : ℝ) ^ σ)⁻¹ := by
      rw [show -(1 + δ) = ((k : ℝ) + δ) + -σ + -σ by rw [hδ]; ring, Real.rpow_add hn', Real.rpow_add hn',
        Real.rpow_neg hn'.le]
    rw [e]
    exact div_le_half_sq_add (Real.rpow_pos_of_pos hn' σ) (Real.rpow_pos_of_pos hn' _)

theorem lseries_cusp_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  intro k L N ε g hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq k L N ε g hk hL hNL hcf
  have hcoef : ∀ n, (qExpansion 1 ⇑f).coeff n = g n := fun n => by
    have h := GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane g hcf.1.1 n
    rw [coef, ← hf] at h
    exact h
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hsq := (GlobalTheory.T.rankin_mean_square_cuspForm k L (ch ε) g hk hcf).2.2.1
  have hsum : ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s := lseriesSummable_of_sq g k hsq
  have habs : LSeries.abscissaOfAbsConv g ≤ (((((k : ℝ) + 1) / 2 : ℝ)) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hsum y (by simpa using hy)
  have hdiff : Differentiable ℂ (ModularForm.L hk0 f) := CuspForm.differentiable_L hk0 f

  have hagree : ∀ s : ℂ, (k : ℝ) / 2 + 1 < s.re → LSeries g s = ModularForm.L hk0 f s := by
    intro s hs
    have h := CuspForm.hasSum_L hk0 f (s := s) (by rw [Int.cast_natCast]; exact hs)
    simp only [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    have hs0 : s ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hs; have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    rw [LSeries, ← h.tsum_eq]
    congr 1
    funext n
    rw [LSeries.term_of_ne_zero' hs0, hcoef]
  refine ⟨ModularForm.L hk0 f, hdiff, fun s hs => ⟨hsum s hs, ?_⟩⟩
  set U : Set ℂ := {c : ℂ | ((k : ℝ) + 1) / 2 < c.re} with hU
  have hLU : AnalyticOnNhd ℂ (LSeries g) U := (LSeries_analyticOnNhd g).mono fun c hc => by
    simp only [Set.mem_setOf_eq, hU] at hc ⊢
    exact lt_of_le_of_lt habs (by exact_mod_cast hc)
  have hΛU : AnalyticOnNhd ℂ (ModularForm.L hk0 f) U := fun z _ => hdiff.analyticAt z
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  set z₀ : ℂ := (((k : ℝ) + 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = (k : ℝ) + 2 := by rw [hz₀, Complex.ofReal_re]
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hz₀U : z₀ ∈ U := by simp only [hU, Set.mem_setOf_eq, hz₀re]; linarith
  have hev : LSeries g =ᶠ[𝓝 z₀] ModularForm.L hk0 f := by
    have hopen : IsOpen {c : ℂ | (k : ℝ) / 2 + 1 < c.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp only [Set.mem_setOf_eq, hz₀re]; linarith)] with c hc
    exact hagree c hc
  exact hLU.eqOn_of_preconnected_of_eventuallyEq hΛU hconn hz₀U hev hs

end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormLseriesExtendsEntireStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_lseries_extends_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  first | exact @GlobalTheory.EisM.lseries_cusp_entire | exact GlobalTheory.EisM.lseries_cusp_entire | (intros; apply GlobalTheory.EisM.lseries_cusp_entire <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesNeZeroReGeOneOfPositivity
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOne
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem sub_one_mul_log_div_rpow_le (n : ℕ) (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    (x - 1) * (Real.log n / (n : ℝ) ^ x) ≤ 1 / n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have e : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
    rw [Real.rpow_sub_one hp.ne' x]; field_simp
  have hq : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hp _
  have hl : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1) := by
    rw [Real.rpow_def_of_pos hp]
    have := Real.add_one_le_exp (Real.log n * (x - 1))
    nlinarith [this]
  have hrw : (x - 1) * (Real.log n / (n : ℝ) ^ x) =
      ((x - 1) * Real.log n / (n : ℝ) ^ (x - 1)) * (1 / n) := by
    rw [e]; field_simp
  rw [hrw]
  refine mul_le_of_le_one_left (by positivity) ((div_le_one hq).2 hl)

theorem not_summable_one_div_primes_eq_neg_one :
    ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ =>
      if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  intro M hM hs
  haveI : NeZero M := ⟨hM.ne'⟩
  have hD := Formalism.HF.apLogDensity M (-1 : ZMod M) isUnit_one.neg
  unfold Formalism.HF.LogDensity at hD
  set S := {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod M) = -1}} with hS
  have h0 : Tendsto (fun x : ℝ => ∑' n : ℕ,
      (x - 1) * S.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) (𝓝[>] 1)
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_
    · by_cases hn : n ∈ S
      · simp only [Set.indicator_of_mem hn]
        have hp : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
        have hc : Continuous fun x : ℝ => (x - 1) * (Real.log n / (n : ℝ) ^ x) := by
          refine (continuous_id.sub continuous_const).mul (continuous_const.div ?_ ?_)
          · exact continuous_const.rpow continuous_id (fun _ => Or.inl hp.ne')
          · intro x; exact (Real.rpow_pos_of_pos hp x).ne'
        have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      · simp only [Set.indicator_of_notMem hn, mul_zero]
        exact tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx n
      have hx : (1 : ℝ) < x := hx
      by_cases hn : n ∈ S
      · have hc : n.Prime ∧ (n : ZMod M) = -1 := hn
        simp only [Set.indicator_of_mem hn, if_pos hc]
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hc.1.one_lt.le)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
          (div_nonneg hlog (Real.rpow_nonneg n.cast_nonneg _)))]
        exact sub_one_mul_log_div_rpow_le n hc.1.one_lt hx
      · have hc : ¬ (n.Prime ∧ (n : ZMod M) = -1) := hn
        simp only [Set.indicator_of_notMem hn, if_neg hc, mul_zero, norm_zero, le_refl]
  simp only [tsum_zero, tsum_mul_left] at h0
  have hu := tendsto_nhds_unique hD h0
  have ht : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 hM
  rw [one_div] at hu
  exact (inv_pos.2 ht).ne' hu

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOneStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_summable_inv_primes_congr_neg_one : ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ => if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  first | exact @GlobalTheory.not_summable_one_div_primes_eq_neg_one | exact GlobalTheory.not_summable_one_div_primes_eq_neg_one | (intros; apply GlobalTheory.not_summable_one_div_primes_eq_neg_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesNeZeroReGeOneOfPositivity
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem not_dvd_of_prime_of_eq_neg_one {M p : ℕ} (hp : p.Prime) (h : (p : ZMod M) = -1) :
    ¬ p ∣ M := by
  intro hpM
  have h1 : ((p + 1 : ℕ) : ZMod M) = 0 := by push_cast; rw [h]; ring
  have h1' : M ∣ p + 1 := (CharP.cast_eq_zero_iff (ZMod M) M (p + 1)).mp h1
  have : p ∣ p + 1 := hpM.trans h1'
  have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem lseries_ne_zero_edge : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  intro M b ω C Λ hM hb1 hb0 hmul hcop hrec hC hsum hsC hre hdiff hL w hw
  have G := fun s hs => GlobalTheory.T.global_positivity_ineq_multiplicative_coeff M b ω s C hs hb1 hb0 hmul hcop hrec hC (hsum s hs)
  rcases hw.lt_or_eq with hw | rfl
  · intro h0
    have hs : 0 < w - 1 := by linarith
    have := G (w - 1) hs 0
    have e : ((1 + (w - 1) : ℝ) : ℂ) = (w : ℂ) := by push_cast; ring
    rw [hL _ hs, e, h0] at this
    norm_num at this
  · intro h0
    rw [Complex.ofReal_one] at h0

    have hO := (hdiff 1).isBigO_sub
    have ht : Tendsto (fun s : ℝ => ((1 + s : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have : Continuous fun s : ℝ => ((1 + s : ℝ) : ℂ) := by fun_prop
      have h := this.tendsto 0
      simp only [add_zero, Complex.ofReal_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨c, hc, hcw⟩ := (hO.comp_tendsto ht).exists_pos
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧ ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s := by
      have h1 := hcw.bound
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
      have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ≤ 1 :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [h1, h2, h3] with s h1 h2 h3
      refine ⟨h2, h3, ?_⟩
      simp only [Function.comp, h0, sub_zero] at h1
      have : ((1 + s : ℝ) : ℂ) - 1 = (s : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2] at h1
      exact h1

    have hC0 : 0 ≤ C := by
      have := hsC 1 one_pos le_rfl
      refine le_trans ?_ this
      exact mul_nonneg zero_le_one (tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    set B : ℝ := 4 * c ^ 2 * C with hB
    let T : ℕ → Finset ℕ := fun X => (Finset.range X).filter (fun p => p.Prime ∧ (p : ZMod M) = -1)

    have key : ∀ X : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s →
        ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ B := by
      intro X s hs hs1 hΛ
      set S := ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hS
      have hS0 : 0 ≤ S := tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have g := G s hs X
      rw [hL s hs] at g
      set F := (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M)
      have hsub : T X ⊆ F := by
        intro p hp
        simp only [T, F, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1, not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2⟩
      have h1 : ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hre' := hre p hp.2.1 (not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2) hp.2.2
        have : (1 : ℝ) ≤ ‖1 + b p‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.one_re, hre', Complex.add_im, Complex.one_im]
          nlinarith [sq_nonneg (b p).im]
        exact div_le_div_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h2 : ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have h3 := Real.add_one_le_exp (∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s))
      have hL2 : ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 ≤ (c * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
      have hsS := hsC s hs hs1
      have h4 : 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S ≤ B := by
        calc 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S
            ≤ 2 * (1 + 1 / s) * (c * s) ^ 2 * S := by gcongr
          _ = 2 * (s + 1) * c ^ 2 * (s * S) := by field_simp
          _ ≤ 2 * (1 + 1) * c ^ 2 * C := by gcongr
          _ = B := by rw [hB]; ring
      linarith

    have hT : ∀ X : ℕ, ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ≤ B := by
      intro X
      have ht : Tendsto (fun s : ℝ => ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s)) (𝓝[>] (0 : ℝ))
          (𝓝 (∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + (0:ℝ)))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        apply tendsto_finsetSum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
        apply Continuous.tendsto
        exact continuous_const.div (continuous_const.rpow (continuous_const.add continuous_id) (fun _ => Or.inl hp0.ne'))
          (fun _ => (Real.rpow_pos_of_pos hp0 _).ne')
      simp only [add_zero, Real.rpow_one] at ht
      apply le_of_tendsto ht
      filter_upwards [hev] with s hs
      exact key X s hs.1 hs.2.1 hs.2.2
    apply GlobalTheory.T.not_summable_inv_primes_congr_neg_one M hM
    apply summable_of_sum_range_le (c := B)
    · intro n; split_ifs <;> positivity
    · intro X
      rw [← Finset.sum_filter]
      exact hT X

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesNeZeroReGeOneOfPositivityStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lseries_ne_zero_re_ge_one_of_positivity : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  first | exact @GlobalTheory.EisM.lseries_ne_zero_edge | exact GlobalTheory.EisM.lseries_ne_zero_edge | (intros; apply GlobalTheory.EisM.lseries_ne_zero_edge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdge
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZEdge

theorem isUnit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h2 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h2
  rw [ZMod.natCast_self, mul_zero, add_zero] at h2
  exact ⟨⟨(d : ZMod L), (u : ZMod L), by rw [mul_comm]; exact h2, h2⟩, rfl⟩

theorem changeLevel_int {n m : ℕ} (χ : DirichletCharacter ℂ n) (h : n ∣ m) (d : ℤ) (hd : IsUnit (d : ZMod m)) :
    DirichletCharacter.changeLevel h χ (d : ZMod m) = χ (d : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h hd.unit
  simp only [IsUnit.unit_spec] at this
  rw [this, ZMod.cast_intCast h]

theorem chi_neg_one (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (hk : Odd k) (hg : Prim k N χ g) :
    χ (-1) = -1 := by
  by_contra hne
  have hinv := hg.cf.1.2 (-1) (by simp)
  have hq : ∀ τ : ℍ, qs g τ = 0 := by
    intro τ
    have h1 := hinv τ
    have hs : (-1 : SL(2, ℤ)) • τ = τ := by rw [ModularGroup.SL_neg_smul, one_smul]
    rw [hs] at h1
    simp [ch, hk.neg_one_pow] at h1
    have h3 : qs g τ * (1 + χ (-1)) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd (by linear_combination h) hne
  have hq0 : qs g = qs 0 := by
    funext τ; rw [hq τ]; simp [qs]
  have hp0 : PolyB (0 : ℕ → ℂ) := ⟨0, 0, by simp⟩
  have := GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth g 0 hg.cf.1.1 hp0 hq0
  have h1 := hg.one
  rw [this] at h1
  simp at h1

end GlobalTheory.EisM.ZEdge

namespace GlobalTheory.EisM.ZEdge

theorem multiplier_agree (N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) :
    ∀ d : ℤ, IsCoprime d ((N * M ^ 2 : ℕ) : ℤ) →
      ch χ d * ch φ d ^ 2 = ch (DirichletCharacter.changeLevel (dvd_mul_right N (M ^ 2)) χ *
        (DirichletCharacter.changeLevel (Dvd.intro_left _ (pow_two M).symm |>.trans (dvd_mul_left _ N)) φ) ^ 2) d := by
  intro d hd
  have hu := isUnit_of_isCoprime hd
  simp only [ch, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  rw [changeLevel_int χ _ d hu, changeLevel_int φ _ d hu]

theorem exists_entire (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ)
    (hk : 1 ≤ k) (hN : 0 < N) (hM : 0 < M) (hg : CF k N (ch χ) g) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re →
      LSeries (fun n => φ n * g n) s = Λ s := by
  have ht := GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq k N M χ φ g hM hg
  have hmf := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * M ^ 2) _).2.2.2.1 _ _ (multiplier_agree N M χ φ) ht.1
  obtain ⟨Λ, h1, h2⟩ := GlobalTheory.T.cuspForm_lseries_extends_entire k (N * M ^ 2) (N * M ^ 2) _ _ hk (by positivity) dvd_rfl ⟨hmf, ht.2⟩
  exact ⟨Λ, h1, fun s hs => (h2 s hs).2⟩

theorem norm_b_sq (e n : ℕ) {M : ℕ} (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) :
    ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e) := by
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_pow, mul_pow, ← pow_mul, mul_comm e 2, mul_div_assoc]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) (DirichletCharacter.norm_le_one φ _))

theorem term_le (e n : ℕ) (s : ℝ) (hs : 0 < s) {M : ℕ} (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) :
    ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [show ((0 : ℕ) : ℝ) = 0 from Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by positivity), div_zero, div_zero]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc _ ≤ (‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e)) / (n : ℝ) ^ (1 + s) :=
          div_le_div_of_nonneg_right (norm_b_sq e n φ g) (by positivity)
      _ = _ := by
          rw [div_div]; congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_add hn']; congr 1; push_cast; ring

theorem lseries_shift (e : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    LSeries (fun n => a n / (n : ℂ) ^ e) z = LSeries a (z + e) := by
  unfold LSeries; congr 1; funext n
  simp only [LSeries.term]
  split_ifs with h
  · rfl
  · rw [cpow_add _ _ (Nat.cast_ne_zero.2 h), cpow_natCast, div_div, mul_comm]

end GlobalTheory.EisM.ZEdge

namespace GlobalTheory.EisM.ZEdge

theorem b_props (e N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ)
    (hN : 0 < N) (hg : Prim (2 * e + 1) N χ g) (hχ : χ (-1) = -1) (hg0 : g 0 = 0) :
    let b : ℕ → ℂ := fun n => φ n * g n / (n : ℂ) ^ e
    let ω : ℕ → ℂ := fun p => χ p * φ p ^ 2
    b 1 = 1 ∧ b 0 = 0 ∧ (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) ∧
    (∀ n, ¬ n.Coprime (N * M) → b n = 0) ∧
    (∀ p r : ℕ, p.Prime → ¬ p ∣ N * M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) ∧
    (∀ p : ℕ, p.Prime → ¬ p ∣ N * M → (p : ZMod (N * M)) = -1 → (b p).re = 0) := by
  intro b ω
  obtain ⟨hmul, hrec, -⟩ := GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hg
  refine ⟨by simp [b, hg.one], by simp [b, hg0], ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    simp only [b, Nat.cast_mul, map_mul, hmul m n hmn, mul_pow]
    ring
  · intro n hn
    simp only [b]
    by_cases hnN : n.Coprime N
    · have hnM : ¬ n.Coprime M := fun h => hn (Nat.Coprime.mul_right hnN h)
      rw [MulChar.map_nonunit φ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul, zero_div]
    · rw [hg.zero n hnN, mul_zero, zero_div]
  · intro p r hp hpd
    have hpN : ¬ p ∣ N := fun h => hpd (dvd_mul_of_dvd_left h M)
    have huN : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    refine ⟨?_, ?_⟩
    · simp only [ω, norm_mul, norm_pow]
      have h1 := DirichletCharacter.unit_norm_eq_one χ huN.unit
      simp only [IsUnit.unit_spec] at h1
      rw [h1, one_mul]
      have hpM : ¬ p ∣ M := fun h => hpd (dvd_mul_of_dvd_right h N)
      have huM : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      have h2 := DirichletCharacter.unit_norm_eq_one φ huM.unit
      simp only [IsUnit.unit_spec] at h2
      rw [h2, one_pow]
    · simp only [b, Nat.cast_pow, map_pow, hrec p r hp hpN, ω]
      rw [show 2 * e + 1 - 1 = 2 * e by omega]
      field_simp
      ring
  · intro p hp hpd hpm
    have hpN : ¬ p ∣ N := fun h => hpd (dvd_mul_of_dvd_left h M)
    have hcN : (p : ZMod N) = -1 := by
      have := congrArg (ZMod.castHom (dvd_mul_right N M) (ZMod N)) hpm
      simpa using this
    have hcM : (p : ZMod M) = -1 := by
      have := congrArg (ZMod.castHom (dvd_mul_left M N) (ZMod M)) hpm
      simpa using this
    have hreal := GlobalTheory.T.depletedCuspEigenform_eigenvalue_eq_char_mul_conj (2 * e + 1) N p χ g (by omega) hN hg hp hpN
    simp only [ch, Int.cast_natCast, hcN, hχ] at hreal
    have hre : (g p).re = 0 := by
      have := congrArg Complex.re hreal
      simp at this
      linarith
    have hφ : φ (-1) = 1 ∨ φ (-1) = -1 := by
      have h2 : φ (-1) ^ 2 = 1 := by rw [← map_pow]; simp
      have h3 : (φ (-1) - 1) * (φ (-1) + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · left; linear_combination h
      · right; linear_combination h
    simp only [b, hcM]
    rw [← Nat.cast_pow, Complex.div_natCast_re]
    rcases hφ with h | h <;> simp [h, hre]

end GlobalTheory.EisM.ZEdge

theorem GlobalTheory.EisM.twisted_lvalue_ne_zero_edge : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) (w : ℝ), Odd k → 0 < N → 0 < M → Prim k N χ g → ((k : ℝ) + 1) / 2 ≤ w → χ (-1) = -1 ∧ ∃ v : ℂ, v ≠ 0 ∧ Tendsto (fun s : ℝ => LSeries (fun n => φ n * g n) ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  intro k N M χ φ g w hk hN hM hg hw
  have hχ := GlobalTheory.EisM.ZEdge.chi_neg_one k N χ g hk hg
  refine ⟨hχ, ?_⟩
  obtain ⟨e, rfl⟩ := hk
  obtain ⟨Λ, hΛd, hΛ⟩ := GlobalTheory.EisM.ZEdge.exists_entire (2 * e + 1) N M χ φ g (by omega) hN hM hg.cf
  obtain ⟨hg0, ⟨C1, hC1⟩, hsum, ⟨C2, hC2⟩⟩ := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hg.cf
  obtain ⟨hb1, hb0, hbm, hbz, hbr, hbre⟩ := GlobalTheory.EisM.ZEdge.b_props e N M χ φ g hN hg hχ hg0
  have hkw : (e : ℝ) + 1 ≤ w := by push_cast at hw; linarith
  have hne : Λ w ≠ 0 := by
    have key := GlobalTheory.T.lseries_ne_zero_re_ge_one_of_positivity (N * M) (fun n => φ n * g n / (n : ℂ) ^ e) (fun p => χ p * φ p ^ 2) (max C1 C2)
      (fun z => Λ (z + e)) (by positivity) hb1 hb0 hbm hbz hbr ?_ ?_ ?_ hbre ?_ ?_ (w - e) (by linarith)
    · have hc : (((w - e : ℝ)) : ℂ) + (e : ℂ) = (w : ℂ) := by push_cast; ring
      simpa [hc] using key
    · intro n
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [hg0]
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        calc ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e) := GlobalTheory.EisM.ZEdge.norm_b_sq e n φ g
          _ ≤ C1 * (n : ℝ) ^ (2 * e + 1) / (n : ℝ) ^ (2 * e) := div_le_div_of_nonneg_right (hC1 n) (by positivity)
          _ = C1 * n := by field_simp; ring
          _ ≤ max C1 C2 * n := mul_le_mul_of_nonneg_right (le_max_left _ _) hn'.le
    · intro s hs
      exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g) (hsum s hs)
    · intro s hs hs1
      calc s * ∑' n : ℕ, ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 / (n : ℝ) ^ (1 + s)
          ≤ s * ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) := by
            apply mul_le_mul_of_nonneg_left _ hs.le
            exact Summable.tsum_le_tsum (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g)
              (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g) (hsum s hs)) (hsum s hs)
        _ ≤ C2 := hC2 s hs hs1
        _ ≤ max C1 C2 := le_max_right _ _
    · exact hΛd.comp (differentiable_id.add_const _)
    · intro s hs
      show LSeries (fun n => φ n * g n / (n : ℂ) ^ e) _ = Λ (_ + e)
      rw [GlobalTheory.EisM.ZEdge.lseries_shift e (fun n => φ n * g n)]
      apply hΛ
      simp
      push_cast
      linarith
  refine ⟨Λ w, hne, ?_⟩
  have hc : Tendsto (fun s : ℝ => Λ ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (Λ w)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun s : ℝ => Λ ((w + s : ℝ) : ℂ)) :=
      hΛd.continuous.comp (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))
    simpa using this.tendsto 0
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hΛ]
  simp
  push_cast
  have : (0 : ℝ) < s := hs
  linarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdgeStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) (w : ℝ), Odd k → 0 < N → 0 < M → Prim k N χ g → ((k : ℝ) + 1) / 2 ≤ w → χ (-1) = -1 ∧ ∃ v : ℂ, v ≠ 0 ∧ Tendsto (fun s : ℝ => LSeries (fun n => φ n * g n) ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  first | exact @GlobalTheory.EisM.twisted_lvalue_ne_zero_edge | exact GlobalTheory.EisM.twisted_lvalue_ne_zero_edge | (intros; apply GlobalTheory.EisM.twisted_lvalue_ne_zero_edge <;> assumption)
end
