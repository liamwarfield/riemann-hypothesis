module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchVol
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPeriod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.Separate
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.Occ
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.SchurFiniteDimensionality.IsFdOfSchurK
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.HolomorphicMoments.MomentHigherEstimateHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigOfLow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchInput
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchSmooth
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

open GlobalTheory.SepReal.ProjSm in
theorem UpperTheory.Lit.Branch.mapSmooth :
    MapSmooth := by
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ T hT v hv
  obtain ⟨-, -, -, -, -, -, hlie, hexp, -⟩ := GlobalTheory.T.unitary_stabiliser_embedding_norm_laws n e ε ε' hpar.signs
  intro k Xs hXs
  have key : (fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (T v)) =
      fun t => T (π ((List.ofFn fun i => NormedSpace.exp (t i • embL e (Xs i))).prod) v) := by
    funext t
    rw [← hT _ (list_mem _ (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact exp_mem (hXs i) (t i))), embH_list, List.map_ofFn]
    simp only [Function.comp_def, hexp]
  rw [key]
  exact (T.restrictScalars ℝ).contDiff.comp (hv k (fun i => embL e (Xs i)) fun i => hlie _ (hXs i))
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

private theorem two_le_big_one (n : ℕ) {B : ℝ} (hB : 1 ≤ B) : 2 ≤ big 1 n B := by
  unfold big
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h8 : (2 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  have hlog : Real.log 2 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_le_log (by norm_num) h8
  have hlog0 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := le_trans (Real.log_nonneg (by norm_num)) hlog
  have hp : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 4 := one_le_pow₀ hn
  have hx : Real.log 2 ≤ 1 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B) := by
    rw [one_mul]
    nlinarith
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ _ := Real.exp_le_exp.2 hx

private theorem vol_arith {V d r c b₁ b₂ b₃ : ℝ} (hd : 0 < d) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 2 ≤ b₃)
    (hV : V ≤ b₁ / d) (hr : 1 ≤ b₂ * r) (hc : r ^ 2 / (2 * d) ≤ c) : V ≤ b₁ * b₂ * b₂ * b₃ * c := by
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  have hr2 : 1 ≤ (b₂ * r) ^ 2 := one_le_pow₀ hr
  calc V ≤ b₁ / d := hV
    _ ≤ b₁ * (b₂ * r) ^ 2 / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact le_mul_of_one_le_right hb₁.le hr2
    _ = b₁ * b₂ * b₂ * 2 * (r ^ 2 / (2 * d)) := by
        field_simp
    _ ≤ b₁ * b₂ * b₂ * b₃ * c := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hb₃ (by positivity)) hc (by positivity)
        have : (0 : ℝ) ≤ b₃ := by linarith
        positivity

open GlobalTheory.SepReal.RealAsm in
theorem UpperTheory.Lit.Branch.realInputE :
    ProjLarge → EigMap → RealInputE := by
  intro hPL hEM
  unfold ProjLarge at hPL
  unfold EigMap at hEM
  obtain ⟨C1, hC1, hIB⟩ := GlobalTheory.T.translateCoefficientIntegralBounds_of_unitary_laws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws (GlobalTheory.T.boostDecompositionNormBound_of_embeddingLaws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws)
    (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound) GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay 10 (by norm_num)
  obtain ⟨C3, hC3, hDB⟩ := GlobalTheory.T.translateCoefficientDerivativeIntegralBounds_of_laws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound)
    GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay GlobalTheory.T.lowestKType_lieWord_normBound 10 (by norm_num)
  obtain ⟨C2, hC2, hVD⟩ := volDeg
  have hDR := GlobalTheory.T.formalDegree_loweringWeight_ratio_le
  have hMS := mapSmooth
  have hLBall := GlobalTheory.T.lowestKType_lieWord_normBound
  unfold ForPair at hPL hEM hIB hDB hVD hMS hDR
  unfold DegRatio at hDR
  unfold MapSmooth at hMS
  unfold LieBound ForDS at hLBall
  unfold RealInputE ForPair
  refine ⟨C1 + C3 + C2 + 201, by linarith, ?_⟩
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ
  have hB : 1 ≤ B := one_le_B hpar
  obtain ⟨⟨v₀, hv₀⟩, -, -⟩ := GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree (n + 1) ε lam H π hπ
  obtain ⟨j, P, hjP, g₀, hg₀, hg₀n, hbig⟩ := hPL n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀
  obtain ⟨d', hd'⟩ := (hDR n e ε lam ε' mu B hpar H H' π σ hπ hσ).1
  obtain ⟨⟨w₀, hw₀⟩, -, -⟩ := GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree n ε' mu H' σ hσ
  have hnn : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    gcongr
    linarith
  have hgap' : GapAtLeast ε' mu (1000 * (n : ℝ) ^ 3) := gap_mono (by linarith) hpar.gap'
  have hw₀int := integrable_low_coef GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound) ε' mu B hpar.three_le
    hpar.hmu hgap' hpar.bound.2 σ hσ w₀ hw₀
  have hIBv := hIB n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n
  have hvint : Integrable (fun h => ⟪π g₀ v₀, π (embH e (umat h)) (π g₀ v₀)⟫_ℂ) (muG ε') := by
    have hi := (hIBv.1 1 (one_mem ε)).1
    simpa using hi
  have hPv : P (π g₀ v₀) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hbig
    linarith
  obtain ⟨w, c, T, hw0, hcP, hcoef, hT, hTv⟩ :=
    hEM n e ε lam ε' mu B hpar H H' π σ hπ hσ d' hd' w₀ hw₀.1 hw₀int j P hjP (π g₀ v₀) hvint hPv
  have hd'pos : 0 < d' := hd'.1
  have hPvpos : 0 < ‖P (π g₀ v₀)‖ := norm_pos_iff.2 hPv
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hcP
  have hLB := hLBall (n + 1) ε lam B (by have := hpar.three_le; omega) hpar.hlam
    (by push_cast; exact hpar.gap) hpar.bound.1 H π hπ v₀ hv₀
  have hsmv : SmV (GlobalTheory.Ell.lieOf (Jm ε)) π (π g₀ v₀) := smV_translate hπ hg₀ hLB.1
  have hsmw : SmV (GlobalTheory.Ell.lieOf (Jm ε')) σ w := by
    rw [← hTv]
    exact hMS n e ε lam ε' mu B hpar H H' π σ hπ hσ T hT (π g₀ v₀) hsmv
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hw'n : ‖((‖w‖ : ℂ)⁻¹) • w‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hwn.le, inv_mul_cancel₀ hwn.ne']
  have hw'w' : ⟪((‖w‖ : ℂ)⁻¹) • w, ((‖w‖ : ℂ)⁻¹) • w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw'n]
    simp
  have hVb : ((muG ε') (nbh ε' (1 / 4))).toReal ≤ c * big (C2 + 100 + 100 + 1) n B := by
    have h1 := hVD n e ε lam ε' mu B hpar H H' π σ hπ hσ d' hd'
    have h2 := vol_arith hd'pos (big_pos C2 n B) (big_pos 100 n B) (two_le_big_one n hB) h1 hbig hcP
    rw [big_mul, big_mul, big_mul, mul_comm] at h2
    exact h2
  refine ⟨v₀, π g₀ v₀, g₀, ((‖w‖ : ℂ)⁻¹) • w, c, hv₀, hg₀, rfl, hsmv, smV_const_smul _ hsmw, hw'n, hcpos,
    ?_, ?_, ?_, hIBv.2⟩
  · intro b
    have hin : ∀ h : ↥(UJ ε'), ⟪b, σ (umat h) (((‖w‖ : ℂ)⁻¹) • w)⟫_ℂ = (‖w‖ : ℂ)⁻¹ * ⟪b, σ (umat h) w⟫_ℂ := by
      intro h
      rw [map_smul, inner_smul_right]
    simp_rw [hin, mul_left_comm _ ((‖w‖ : ℂ)⁻¹)]
    rw [integral_const_mul, hcoef b, hw'w', inner_smul_right]
    ring
  · intro g hg
    obtain ⟨hint, hle⟩ := hIBv.1 g hg
    refine ⟨hint, hle.trans ?_⟩
    have hcl : 0 ≤ colLen e g := by
      unfold colLen
      positivity
    have hX : 0 ≤ colLen e g ^ (-(2 * (n : ℝ) + 7)) := by
      first
        | exact Real.rpow_nonneg hcl _
        | exact zpow_nonneg hcl _
        | positivity
    apply mul_le_mul_of_nonneg_right _ hX
    calc ((muG ε') (nbh ε' (1 / 4))).toReal * big C1 n B
        ≤ c * big (C2 + 100 + 100 + 1) n B * big C1 n B :=
          mul_le_mul_of_nonneg_right hVb (big_pos _ _ _).le
      _ = c * big (C2 + 100 + 100 + 1 + C1) n B := by rw [mul_assoc, big_mul]
      _ ≤ c * big (C1 + C3 + C2 + 201) n B :=
          mul_le_mul_of_nonneg_left (big_mono (by linarith) n hB) hcpos.le
  · intro X hX hXn
    obtain ⟨hint, hle⟩ := hDB n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n X hX hXn
    refine ⟨hint, hle.trans ?_⟩
    calc ((muG ε') (nbh ε' (1 / 4))).toReal * big C3 n B
        ≤ c * big (C2 + 100 + 100 + 1) n B * big C3 n B :=
          mul_le_mul_of_nonneg_right hVb (big_pos _ _ _).le
      _ = c * big (C2 + 100 + 100 + 1 + C3) n B := by rw [mul_assoc, big_mul]
      _ ≤ c * big (C1 + C3 + C2 + 201) n B :=
          mul_le_mul_of_nonneg_left (big_mono (by linarith) n hB) hcpos.le
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.SeedBaseCases.SeedBOf
namespace PositivityTheory.RgHe.A.Pf

theorem seedB_of : PositivityTheory.RgHe.Seed → PositivityTheory.RgHe.Occ → PositivityTheory.RgHe.A.SchurEigenProjectionExists := by
  intro hS hO n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ hW
  have hG : PositivityTheory.RgHe.Gp ε lam ε' mu e :=
    ⟨hF, hP.two, hP.neg, hP.le, hP.hc, hP.hc', hP.gap, hP.gap'⟩
  have hj := hO n ε lam ε' mu e hG hW H H' π σ hπ hσ
  exact hS n ε lam ε' mu e hG H H' π σ ν hν hπ hσ hj

end PositivityTheory.RgHe.A.Pf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMatrixCoefficientIntertwiner
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquare
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSqIntegralSmulLe
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.Godement

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem inner_map {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨-, -, hnorm, -⟩ := hU
  exact (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y

theorem inner_orbit {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (v : B) (g h : Γ) :
    ⟪ρ g v, ρ h v⟫_ℂ = ⟪v, ρ (g⁻¹ * h) v⟫_ℂ := by
  rw [← GlobalTheory.CompanionTheory.Godement.inner_map hU g v (ρ (g⁻¹ * h) v)]
  obtain ⟨-, hmul, -, -⟩ := hU
  congr 1
  calc ρ h v = ρ (g * (g⁻¹ * h)) v := by rw [mul_inv_cancel_left]
    _ = ρ g (ρ (g⁻¹ * h) v) := by rw [hmul g (g⁻¹ * h), ContinuousLinearMap.mul_apply]

end Unitary

theorem mul_le_half_add (a b : ℝ≥0∞) : a * b ≤ 2⁻¹ * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.young_inequality a b Real.HolderConjugate.two_two
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.ofReal_ofNat] at h
  calc a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := h
    _ = 2⁻¹ * (a ^ 2 + b ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (a ^ 2), mul_comm (b ^ 2), mul_add]

theorem norm_sq_integral_smul_le : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ f : Γ → ℂ, Measurable f → Integrable f ν →
    Integrable (fun g => ‖f g‖ ^ 2) ν →
    ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 ≤ (∫ g, ‖f g‖ ^ 2 ∂ν) * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := by
  intro Γ _ _ _ _ _ _ _ ν _ _ B _ _ _ ρ hU v hφ f hf hfi hf2
  obtain ⟨-, -, -, hcont⟩ := id hU
  have hA : 0 ≤ ∫ g, ‖f g‖ ^ 2 ∂ν := integral_nonneg fun g => sq_nonneg _
  have hB : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun g => norm_nonneg _
  by_cases hF : Integrable (fun g => f g • ρ g v) ν
  swap
  · rw [integral_undef hF, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg hA hB
  have hψc : Continuous fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := (continuous_const.inner (hcont v)).enorm
  have hψ : Measurable fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := hψc.measurable
  have hfe : Measurable fun g : Γ => ‖f g‖ₑ ^ 2 := hf.enorm.pow_const 2
  have hswap : ∀ g h : Γ, ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ = ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ := by
    intro g h
    rw [← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v h g, ← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v g h,
      ← inner_conj_symm (ρ h v) (ρ g v), RCLike.enorm_conj]
  have hswapm : AEMeasurable (Function.uncurry fun h g : Γ =>
      2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) (ν.prod ν) := by
    apply Measurable.aemeasurable
    exact measurable_const.mul ((hfe.comp measurable_snd).mul
      (hψ.comp (measurable_fst.inv.mul measurable_snd)))
  have hm3 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν :=
    (measurable_const.mul hfe).mul_const _
  have hm4 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 := measurable_const.mul hfe
  have hII : ⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ =
      ∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν := by
    rw [← integral_inner hF]
    refine integral_congr_ae ?_
    filter_upwards with h
    rw [inner_smul_right, ← inner_conj_symm, ← integral_inner hF]
    simp only [inner_smul_right]
  have key : ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ₑ ≤
      (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [hII]
    calc ‖∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν‖ₑ
        ≤ ∫⁻ h, ‖f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν ∂ν := by
          refine lintegral_mono fun h => ?_
          beta_reduce
          rw [enorm_mul, RCLike.enorm_conj]
          calc ‖f h‖ₑ * ‖∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν‖ₑ
              ≤ ‖f h‖ₑ * ∫⁻ g, ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := by
                gcongr
                exact enorm_integral_le_lintegral_enorm _
            _ ≤ ∫⁻ g, ‖f h‖ₑ * ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := lintegral_const_mul_le _ _
            _ ≤ _ := by
                refine lintegral_mono fun g => ?_
                beta_reduce
                rw [enorm_mul, GlobalTheory.CompanionTheory.Godement.inner_orbit hU, ← mul_assoc]
                gcongr ?_ * _
                exact GlobalTheory.CompanionTheory.Godement.mul_le_half_add _ _
      _ = ∫⁻ h, (2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν +
            ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν) ∂ν := by
          refine lintegral_congr fun h => ?_
          have hm : Measurable fun g => ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ := hψ.comp (measurable_const_mul h⁻¹)
          have hm2 : Measurable fun g => 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ :=
            measurable_const.mul hm
          calc ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν
              = ∫⁻ g, (2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ +
                  2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) ∂ν :=
                lintegral_congr fun g => by ring
            _ = ∫⁻ g, 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν +
                  ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν :=
                lintegral_add_left hm2 _
            _ = _ := by
                rw [lintegral_const_mul _ hm,
                  lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) h⁻¹]
      _ = (∫⁻ h, 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν) +
            ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν :=
          lintegral_add_left hm3 _
      _ = 2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) +
            2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) := by
          congr 1
          · rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
          · rw [lintegral_lintegral_swap hswapm]
            calc ∫⁻ g, ∫⁻ h, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν
                = ∫⁻ g, 2⁻¹ * ‖f g‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν := by
                  refine lintegral_congr fun g => ?_
                  have hm : Measurable fun h => ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ :=
                    hψ.comp (measurable_const_mul g⁻¹)
                  simp_rw [hswap g]
                  rw [← lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) g⁻¹,
                    ← lintegral_const_mul _ hm]
                  exact lintegral_congr fun h => by ring
              _ = _ := by
                  rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
      _ = (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
          rw [← two_mul, ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hX : ENNReal.ofReal (∫ g, ‖f g‖ ^ 2 ∂ν) = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (Filter.Eventually.of_forall fun g => sq_nonneg _)]
    refine lintegral_congr fun g => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hY : ENNReal.ofReal (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) = ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hφ.norm (Filter.Eventually.of_forall fun g => norm_nonneg _)]
    exact lintegral_congr fun g => ofReal_norm_eq_enorm _
  have hL : ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 = ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hL, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB), ENNReal.ofReal_mul hA, hX, hY,
    ofReal_norm_eq_enorm]
  exact key

end GlobalTheory.CompanionTheory.Godement
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquare
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GodementCoeff

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure]
  [ν.IsMulRightInvariant] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

private theorem integrableOn_and_setIntegral_sq_le_of_isU (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) {s : Set Γ} (hs : MeasurableSet s)
    (hs' : ν s ≠ ⊤) :
    IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν ∧
      ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hcont : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hbd : ∀ g, ‖⟪b, ρ g v⟫_ℂ‖ ≤ ‖b‖ * ‖v‖ := fun g =>
    (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  have hc2 : IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν := by
    refine Measure.integrableOn_of_bounded (M := (‖b‖ * ‖v‖) ^ 2) hs'
      (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd g) 2
  set f : Γ → ℂ := s.indicator (fun g => starRingEnd ℂ ⟪b, ρ g v⟫_ℂ) with hfdef
  have hfm : Measurable f := ((Complex.continuous_conj.comp hcont).measurable).indicator hs
  have hfi : Integrable f ν := by
    refine (integrable_indicator_iff hs).mpr (Measure.integrableOn_of_bounded (M := ‖b‖ * ‖v‖) hs'
      (Complex.continuous_conj.comp hcont).aestronglyMeasurable (ae_of_all _ fun g => ?_))
    rw [Complex.norm_conj]
    exact hbd g
  have hfeq : (fun g => ‖f g‖ ^ 2) = s.indicator (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) := by
    funext g
    by_cases hg : g ∈ s <;> simp [hfdef, hg, norm_inner_symm]
  have hf2 : Integrable (fun g => ‖f g‖ ^ 2) ν := by
    rw [hfeq]
    exact (integrable_indicator_iff hs).mpr hc2
  have hG := GlobalTheory.CompanionTheory.Godement.norm_sq_integral_smul_le ν ρ hρ v hm f hfm hfi hf2
  rw [hfeq, integral_indicator hs] at hG
  have hint : Integrable (fun g => f g • ρ g v) ν :=
    hfi.smul_of_top_left (memLp_top_of_bound (hρ.cont v).aestronglyMeasurable ‖v‖
      (ae_of_all _ fun g => (hρ.norm g v).le))
  set I := ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν with hIdef
  set w := ∫ g, f g • ρ g v ∂ν with hwdef
  have hinner : ⟪b, w⟫_ℂ = (I : ℂ) := by
    have h := (innerSL ℂ b).integral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    rw [hwdef, ← h, hIdef, ← integral_indicator hs, ← integral_complex_ofReal]
    congr 1
    funext g
    by_cases hg : g ∈ s
    · rw [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem hg, inner_smul_right,
        Complex.conj_mul']
      push_cast
      rfl
    · simp [hfdef, hg]
  have hI0 : 0 ≤ I := setIntegral_nonneg hs fun _ _ => by positivity
  have hM0 : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  have h1 : I ≤ ‖b‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) b w
    rwa [hinner, Complex.norm_real, Real.norm_of_nonneg hI0] at h
  refine ⟨hc2, ?_⟩
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have h2 : I * I ≤ I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
      calc I * I ≤ (‖b‖ * ‖w‖) * (‖b‖ * ‖w‖) := mul_self_le_mul_self hI0 h1
        _ = ‖b‖ ^ 2 * ‖w‖ ^ 2 := by ring
        _ ≤ ‖b‖ ^ 2 * (I * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) := by gcongr
        _ = I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by ring
    exact le_of_mul_le_mul_left h2 hpos

theorem sq_integrable_and_bound (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) :
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
      ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hK : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 :=
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (sq_nonneg _)
  have hcont : Continuous fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 :=
    (continuous_const.inner (hρ.cont v)).norm.pow 2
  have key : ∀ s, MeasurableSet s → ν s ≠ ⊤ → ∫⁻ g in s, ‖‖⟪b, ρ g v⟫_ℂ‖ ^ 2‖ₑ ∂ν ≤
      ENNReal.ofReal ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
    intro s hs hs'
    obtain ⟨hi, hle⟩ := integrableOn_and_setIntegral_sq_le_of_isU ν ρ hρ v hm b hs hs'
    rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
    apply ENNReal.ofReal_le_ofReal
    simpa only [norm_pow, norm_norm] using hle
  have hInt : Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν :=
    integrable_of_forall_fin_meas_le _ ENNReal.ofReal_lt_top hcont.aestronglyMeasurable key
  refine ⟨hInt, ?_⟩
  have hle := lintegral_le_of_forall_fin_meas_le _ key
  rw [← ofReal_integral_norm_eq_lintegral_enorm hInt, ENNReal.ofReal_le_ofReal_iff hK] at hle
  simpa only [norm_pow, norm_norm] using hle

end GlobalTheory.CompanionTheory.GodementCoeff

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquareStatement
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_integrable_square : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ b : B,
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
    ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | exact GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | (intros; apply GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound <;> assumption)
end
end

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TMapPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem isU_inner (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (ρ g).toLinearMap (hU.norm g)).inner_map_map x y

theorem isU_apply_inv (hU : IsU ρ) (g : Γ) (x : A) : ρ g (ρ g⁻¹ x) = x := by
  have h := hU.mul g g⁻¹
  rw [mul_inv_cancel, hU.one] at h
  have h2 := congrArg (fun T : A →L[ℂ] A => T x) h
  simpa using h2.symm

theorem isU_inner_left (hU : IsU ρ) (k : Γ) (x y : A) : ⟪ρ k x, y⟫_ℂ = ⟪x, ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← isU_apply_inv hU k y]
  exact isU_inner hU k x _

end Unitary

theorem norm_integral_mul_sq_le {Γ : Type} [MeasurableSpace Γ] (ν : Measure Γ) (f g : Γ → ℂ) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) : ‖∫ x, f x * g x ∂ν‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂ν) * ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have h0 : ‖∫ x, f x * g x ∂ν‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂ν := by
    simpa using norm_integral_le_integral_norm (μ := ν) (fun x => f x * g x)
  simp only [Real.rpow_two] at h1
  have hP : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  have hQ : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  calc ‖∫ x, f x * g x ∂ν‖ ^ 2
      ≤ ((∫ x, ‖f x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ)) * (∫ x, ‖g x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h0.trans h1) 2
    _ = _ := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hP, Real.sq_sqrt hQ]

section Main

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
  [InnerProductSpace ℂ B] [CompleteSpace B] {σ : Γ → (A →L[ℂ] A)} {ρ : Γ → (B →L[ℂ] B)} {d : ℝ}


omit [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompleteSpace A] in
theorem coeff_sq (hσ : IsU σ) (hF : IsFd ν σ d) (w a : A) :
    MemLp (fun g => ⟪σ g w, a⟫_ℂ) 2 ν ∧ ∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν = ‖a‖ ^ 2 * ‖w‖ ^ 2 / d := by
  have key : ∀ g, ⟪a, σ g w⟫_ℂ * star ⟪a, σ g w⟫_ℂ = ((‖⟪σ g w, a⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inner_symm]
  obtain ⟨h1, h2⟩ := hF.2 w a w a
  simp only [key] at h1 h2
  have h3 : Integrable (fun g => ‖⟪σ g w, a⟫_ℂ‖ ^ 2) ν := by
    exact h1.re.congr (ae_of_all _ fun g => Complex.ofReal_re _)
  have hc : Continuous fun g => ⟪σ g w, a⟫_ℂ := (hσ.cont w).inner continuous_const
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 h3, ?_⟩
  have e : ∀ x : A, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [integral_complex_ofReal, e, e] at h2
  have h4 : ((∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖w‖ ^ 2 / d : ℝ) : ℂ) := by
    rw [h2]; push_cast; ring
  exact_mod_cast h4

omit [CompleteSpace A] in
theorem form_facts (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) (b : B) (a : A) :
    Integrable (fun g => ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) ν ∧
      ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ^ 2 ≤
        ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) * (‖a‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.matrix_coefficient_integrable_square ν ρ hρ v hv b
  have hc : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hφ : MemLp (fun g => ⟪b, ρ g v⟫_ℂ) 2 ν := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hb1
  obtain ⟨hψ, hψ2⟩ := coeff_sq ν hσ hF w a
  refine ⟨hφ.integrable_mul hψ, ?_⟩
  refine (norm_integral_mul_sq_le ν _ _ hφ hψ).trans ?_
  rw [hψ2]
  exact mul_le_mul_of_nonneg_right hb2 (div_nonneg (by positivity) hF.1.le)

theorem exists_matrix_coefficient_intertwiner (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) :
    ∃ T : B →L[ℂ] A, ∀ b a, ⟪T b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := by
  have hint := fun b a => (form_facts ν hρ hσ hF hv w b a).1
  have hM : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨K, hK0, hbd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ b a, ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ≤ K * ‖b‖ * ‖a‖ := by
    refine ⟨Real.sqrt ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d), Real.sqrt_nonneg _, fun b a => ?_⟩
    have hq : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d := div_nonneg (by positivity) hF.1.le
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine (form_facts ν hρ hσ hF hv w b a).2.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hq]
    ring
  let L : B → (A →L[ℂ] ℂ) := fun b => LinearMap.mkContinuous
    { toFun := fun a => ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν
      map_add' := fun a a' => by
        rw [← integral_add (hint b a) (hint b a')]
        congr 1; ext g; rw [inner_add_right, mul_add]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; ext g; rw [inner_smul_right]; ring } (K * ‖b‖) (fun a => hbd b a)
  let Tf : B → A := fun b => (InnerProductSpace.toDual ℂ A).symm (L b)
  have hT : ∀ b a, ⟪Tf b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := fun b a => by
    simp only [Tf, InnerProductSpace.toDual_symm_apply]
    rfl
  have hTb : ∀ b, ‖Tf b‖ ≤ K * ‖b‖ := fun b => by
    have h1 := hbd b (Tf b)
    rw [← hT, inner_self_eq_norm_sq_to_K] at h1
    by_cases h0 : ‖Tf b‖ = 0
    · rw [h0]; positivity
    · have h2 : 0 < ‖Tf b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h3 : ‖Tf b‖ * ‖Tf b‖ ≤ (K * ‖b‖) * ‖Tf b‖ := by
        simpa [sq] using h1
      exact le_of_mul_le_mul_right h3 h2
  refine ⟨LinearMap.mkContinuous
    { toFun := Tf
      map_add' := fun b b' => ext_inner_right ℂ fun a => by
        rw [inner_add_left, hT, hT, hT, ← integral_add (hint b a) (hint b' a)]
        congr 1; ext g; rw [inner_add_left, add_mul]
      map_smul' := fun t b => ext_inner_right ℂ fun a => by
        simp only [RingHom.id_apply]
        rw [inner_smul_left, hT, hT, ← integral_const_mul]
        congr 1; ext g; rw [inner_smul_left]; ring } K hTb, fun b a => ?_⟩
  exact hT b a

end Main

theorem tMap : TMap := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hF v hv w c hc h
  obtain ⟨T, hT⟩ := exists_matrix_coefficient_intertwiner ν hρ hσ hF hv w
  have hk : ∀ k b, T (ρ k b) = σ k (T b) := fun k b => ext_inner_right ℂ fun a => by
    rw [hT, isU_inner_left hσ k, hT]
    refine (integral_mul_left_eq_self (μ := ν) (fun g => ⟪ρ k b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) k).symm.trans
      (integral_congr_ae (ae_of_all _ fun g => ?_))
    simp only [hρ.mul, hσ.mul, ContinuousLinearMap.mul_apply]
    rw [isU_inner hρ, isU_inner_left hσ]
  have hv' : T v = (c : ℂ) • w := ext_inner_right ℂ fun a => by
    rw [hT, inner_smul_left, Complex.conj_ofReal]
    have h1 := congrArg (starRingEnd ℂ) (h a)
    rw [← integral_conj] at h1
    simp only [map_mul, inner_conj_symm, Complex.conj_ofReal, Complex.star_def] at h1
    exact h1
  refine ⟨(c : ℂ)⁻¹ • T, fun g x => ?_, ?_⟩
  · simp [hk]
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [ContinuousLinearMap.smul_apply, hv', smul_smul, inv_mul_cancel₀ hc', one_smul]

end GlobalTheory.CompanionTheory.RgHeA.TMapPf
end
end

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal
open scoped InnerProductSpace

namespace UpperTheory.Lit.Branch

variable {n : ℕ}

def sumNum (e : Option (Fin n) ≃ Fin (n + 1)) : Fin n ⊕ Unit ≃ Fin (n + 1) := (Equiv.optionEquivSumPUnit (Fin n)).symm.trans e

theorem emb_sumNum (e : Option (Fin n) ≃ Fin (n + 1)) (h : Mat n) : GlobalTheory.CompanionTheory.PairingAnalysis.emb (sumNum e) h = embH e h := by
  ext a b
  simp only [GlobalTheory.CompanionTheory.PairingAnalysis.emb, embH, sumNum, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> simp [Equiv.optionEquivSumPUnit]

variable {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
  {mu : Fin n → ℝ} {B : ℝ}

theorem fits_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.Fits ε ε' (sumNum e) := by
  refine ⟨?_, fun a => ?_⟩
  · simpa [GlobalTheory.CompanionTheory.PairingAnalysis.zi, sumNum, Equiv.optionEquivSumPUnit] using hP.signs.1
  · simpa [sumNum, Equiv.optionEquivSumPUnit] using hP.signs.2 a

theorem par_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.Par ε lam ε' mu B := by
  have hs := hP.signs
  refine ⟨by linarith [hP.three_le], ?_, ?_, hP.hlam, hP.hmu, hP.bound.1, hP.bound.2, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hP.neg
    exact ⟨e (some i), by rw [hs.2 i, hi]⟩
  · calc #{a | ε a = false} ≤ #{i | ε' i = false} := by
          refine Finset.card_le_card_of_surjOn (fun i => e (some i)) ?_
          intro a ha
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
          cases hsa : e.symm a with
          | none =>
            have : a = e none := by rw [← hsa, Equiv.apply_symm_apply]
            rw [this, hs.1] at ha
            exact absurd ha (by decide)
          | some i =>
            have : a = e (some i) := by rw [← hsa, Equiv.apply_symm_apply]
            refine ⟨i, ?_, this.symm⟩
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
            rw [← hs.2 i, ← this, ha]
      _ ≤ #{i | ε' i = true} := hP.pos
      _ ≤ #{a | ε a = true} := by
          refine Finset.card_le_card_of_injOn (fun i => e (some i)) ?_ ?_
          · intro i hi
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
            rw [hs.2 i, hi]
          · intro i _ j _ hij
            simpa using hij
  · intro a b hab
    have h1 := hP.gap a b hab
    have h2 : (0 : ℝ) ≤ (↑n + 1) ^ 3 := by positivity
    linarith
  · intro a b hab
    have h1 := hP.gap' a b hab
    have h2 : (0 : ℝ) ≤ (↑n + 1) ^ 3 := by positivity
    linarith

theorem heWord_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.HeWord ε lam ε' mu := by
  intro x y hxy hz
  have h := hP.word x y hxy hz
  simp only [ne_eq] at h
  tauto

private theorem exists_uj_umat_eq_of_mem_UJset {m : ℕ} {ε : Fin m → Bool} {h : Mat m} (hh : h ∈ UJset ε) :
    ∃ g : UJ ε, umat g = h := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  have h1 : (Jm ε * hᴴ * Jm ε) * h = 1 := by
    calc (Jm ε * hᴴ * Jm ε) * h = Jm ε * (hᴴ * Jm ε * h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh', hJ]
  exact ⟨⟨⟨h, Jm ε * hᴴ * Jm ε, mul_eq_one_comm.mp h1, h1⟩, hh⟩, rfl⟩

private theorem embH_mem_UJset_of_signs {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool}
    {ε' : Fin n → Bool} (hs : Signs e ε ε') {h : Mat n} (hh : h ∈ UJset ε') : embH e h ∈ UJset ε := by
  have hJ : Jm ε = embH e (Jm ε') := by
    ext a b
    have ha := e.apply_symm_apply a
    have hb := e.apply_symm_apply b
    simp only [embH, Formalism.REAL.Jm, Matrix.diagonal_apply]
    rcases hA : e.symm a with _ | i <;> rcases hB : e.symm b with _ | j <;> rw [hA] at ha <;>
      rw [hB] at hb <;> subst ha <;> subst hb <;> simp [hs.1, hs.2]
  have hC : (embH e h)ᴴ = embH e hᴴ := by
    ext a b
    simp only [embH, Matrix.conjTranspose_apply]
    rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> simp
  rw [GlobalTheory.SepReal.ProjSm.mem_iff] at hh ⊢
  rw [hC, hJ, ← embH_mul, ← embH_mul, hh]

private theorem isU_comp_umat_of_isURepOn {m : ℕ} {ε : Fin m → Bool} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {ρ : Mat m → K →L[ℂ] K} (hρ : IsURepOn (UJset ε) ρ) :
    GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε => ρ (umat g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ρ 1 = 1
    exact hρ.1.1
  · intro a b
    have h := hρ.1.2 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε a) _ (GlobalTheory.SepReal.RealAsm.umat_mem ε b)
    show ρ (umat a * umat b) = _
    rw [h]
    rfl
  · intro g x
    exact hρ.2.1 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε g) x
  · intro x
    exact (hρ.2.2 x).comp_continuous (GlobalTheory.SepReal.RealAsm.continuous_umat ε)
      (GlobalTheory.SepReal.RealAsm.umat_mem ε)

private theorem isURepOn_embH_of_signs {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool}
    {ε' : Fin n → Bool} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (hs : Signs e ε ε') {π : Mat (n + 1) → K →L[ℂ] K} (hπ : IsURepOn (UJset ε) π) :
    IsURepOn (UJset ε') (fun h => π (embH e h)) := by
  have hc : Continuous (embH e) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [embH]
    rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> first | fun_prop | exact continuous_const
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => hπ.2.1 _ (embH_mem_UJset_of_signs hs hg) v,
    fun v => (hπ.2.2 v).comp hc.continuousOn (fun h hh => embH_mem_UJset_of_signs hs hh)⟩
  · simp only [embH_one]
    exact hπ.1.1
  · simp only [embH_mul]
    exact hπ.1.2 _ (embH_mem_UJset_of_signs hs ha) _ (embH_mem_UJset_of_signs hs hb)

theorem projLarge_of (hS : PositivityTheory.RgHe.A.SchurEigenProjectionExists) (hB : PositivityTheory.RgHe.A.BigProjP) : ProjLarge := by
  unfold ProjLarge ForPair
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ v₀ hv₀
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS mu σ hσ
  have hK : PositivityTheory.RgHe.SchurK ε' σ (muG ε') d⁻¹ := by
    refine ⟨inv_pos.2 hd.1, fun v w v' w' => ⟨(hd.2 v w v' w').1, ?_⟩⟩
    refine (hd.2 v w v' w').2.trans ?_
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  obtain ⟨S, hKS⟩ := hσ.2.2.2.2.2.1
  obtain ⟨x, hxS, hx0, -⟩ := hKS.2.2.2.1
  have hxL : x ∈ lowKSub ε' mu σ := by
    unfold Formalism.MainNotions.S.lowKSub
    exact Submodule.mem_sSup_of_mem hKS hxS
  set w : H' := ((‖x‖ : ℂ)⁻¹) • x with hwdef
  have hwL : w ∈ lowKSub ε' mu σ := Submodule.smul_mem _ _ hxL
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
  have hfit := fits_of hP
  have hpar := par_of hP
  obtain ⟨hint, i, η, hiso, hieq, hη, hηi, hηa⟩ := hS n ε lam ε' mu B (sumNum e) H H' π σ (muG ε')
    inferInstance hfit hpar hπ hσ (heWord_of hP) d⁻¹ hK w hwL hw1
  obtain ⟨g₀, hg₀s, hg₀⟩ := hB n ε lam ε' mu B (sumNum e) H H' π σ (muG ε') inferInstance hfit hpar
    hπ hσ d⁻¹ hK w hwL hw1 hint i η hiso hieq hη hηi hηa v₀ hv₀.2 hv₀.1
  have hB1 := GlobalTheory.SepReal.RealAsm.one_le_B hP
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hX : 0 ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  refine ⟨i, ContinuousLinearMap.adjoint i,
    ⟨?_, hiso, fun v y => (ContinuousLinearMap.adjoint_inner_right i y v).symm⟩,
    umat g₀, GlobalTheory.SepReal.RealAsm.umat_mem ε g₀, ?_, ?_⟩
  · intro h hh y
    obtain ⟨g, rfl⟩ := exists_uj_umat_eq_of_mem_UJset hh
    have h2 := hieq g y
    rwa [emb_sumNum] at h2
  · rw [show (10 : ℝ) * ((n : ℝ) + 1) = ((10 * (n + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    show Real.sqrt (Formalism.REAL.hs (umat g₀)) ≤ _
    rw [← Real.sqrt_sq (pow_nonneg hX (10 * (n + 1)))]
    apply Real.sqrt_le_sqrt
    rw [← pow_mul]
    convert hg₀s using 2 <;> ring
  · have hL : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by nlinarith)
    have h1 : 1 ≤ big 100 n B *
        Real.exp (-(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * ((n : ℝ) + 1) * B))) := by
      unfold big
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have h3 : 100 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B) +
          -(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * ((n : ℝ) + 1) * B)) =
          100 * (((n : ℝ) + 1) ^ 3 * (n : ℝ) * Real.log (8 * ((n : ℝ) + 1) * B)) := by ring
      rw [h3]
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity) hn) hL)
    exact h1.trans (mul_le_mul_of_nonneg_left hg₀ (GlobalTheory.SepReal.RealAsm.big_pos _ _ _).le)

theorem eigMap_of (hE : PositivityTheory.RgHe.A.EigA) (hT : PositivityTheory.RgHe.A.TMap) : EigMap := by
  unfold EigMap ForPair
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ d hd w₀ hw₀ hint j P hjP v hv hPv
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  have hU' : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε' => σ (umat g)) := isU_comp_umat_of_isURepOn hσ.2.2.1
  have hU : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε' => π (embH e (umat g))) :=
    isU_comp_umat_of_isURepOn (ρ := fun h => π (embH e h)) (isURepOn_embH_of_signs hP.signs hπ.2.2.1)
  have hFd : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsFd (muG ε') (fun g : UJ ε' => σ (umat g)) d := hd
  have hiso : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsIsoMap (fun g : UJ ε' => σ (umat g)) (fun g => π (embH e (umat g))) j :=
    ⟨fun g x => hjP.1 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε' g) x, hjP.2.1⟩
  have hadj : ContinuousLinearMap.adjoint j = P := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [← inner_conj_symm, ← hjP.2.2 x y]
    exact inner_conj_symm _ _
  obtain ⟨w, c, hw0, hc, hb⟩ := hE (muG ε') (fun g : UJ ε' => σ (umat g))
    (fun g => π (embH e (umat g))) d hU' hU hFd w₀ hw₀ hint j hiso v hv
  rw [hadj] at hc
  have hcpos : 0 < c :=
    lt_of_lt_of_le (div_pos (pow_pos (norm_pos_iff.2 hPv) 2) (by linarith [hd.1])) hc
  obtain ⟨T, hT, hTv⟩ := hT (muG ε') (fun g : UJ ε' => σ (umat g)) (fun g => π (embH e (umat g))) d
    hU' hU hFd v hv w c hcpos.ne' (fun b => (hb b).2)
  refine ⟨w, c, T, hw0, hc, fun b => (hb b).2, ?_, hTv⟩
  intro h hh x
  obtain ⟨g, rfl⟩ := exists_uj_umat_eq_of_mem_UJset hh
  exact hT g x

end UpperTheory.Lit.Branch

end

namespace UpperTheory.Lit

theorem realInputE_holds : Branch.RealInputE :=
  Branch.realInputE
    (Branch.projLarge_of (PositivityTheory.RgHe.A.Pf.seedB_of PositivityTheory.RgHe.LowestKTypeModel.seed PositivityTheory.RgHe.occ)
      (PositivityTheory.RgHe.A.Pf.bigProjP PositivityTheory.RgHe.A.Pf.momentP CompanionTheory.Lime.T3.analytic_estimates))
    (Branch.eigMap_of GlobalTheory.CompanionTheory.RgHeA.eigA GlobalTheory.CompanionTheory.RgHeA.TMapPf.tMap)

end UpperTheory.Lit
