module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusMixedCoordinateSumLeSobolevSeminorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelSiegelSetLeTorusPowerHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaValueSiegelTorusElementLeSobolevSeminorm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusMixedCoordinateSumLeSobolevSeminormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_mixedCoordinate_sum_le_sobolev_seminorm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ (c : ℝ), 0 < c →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ α : Mx D r r, α.map (finPart D) = 1 →
        (∀ τ, compAt θ τ α = diagonal (fun i => (t i : ℂ))) →
        ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 k Ψ).toReal) := by
  first | exact @GlobalTheory.TorusMixedSum.sum_mixS_le | exact GlobalTheory.TorusMixedSum.sum_mixS_le | (intros; apply GlobalTheory.TorusMixedSum.sum_mixS_le <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaValueSiegelTorusElementLeSobolevSeminorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

namespace GlobalTheory.SiegelTorusTheta

theorem torus_bound : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf)
    (c : ℝ) (hc : 0 < c) (K₀ : Set (WO M X)) (hK₀ : K₀ ∈ nhds (0 : WO M X)) (hK₀c : IsCompact K₀)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO M X → ℂ, IsThetaFunO ψ (sgn ε M) X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ‖ω (a, 1) Ψ 0‖ ≤ C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal *
          ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  intro D ψ θ hθ ε M X χ χ' ω hω r Xf Yf hW c hc K₀ hK₀ hK₀c μ 𝓕 hμ
  obtain ⟨S₀, d, hA1⟩ := GlobalTheory.T.wittFrame_torus_eq_levi_element θ hθ ε M r Xf Yf hW
  obtain ⟨μ', 𝓕', hcov, hA2⟩ := GlobalTheory.T.leviThetaValue_le_det_mul_rational_sum ψ (sgn ε M) S₀ X r d χ χ' (ω.toSgn ε) hω
  obtain ⟨k, A, C, hC, hB⟩ := GlobalTheory.T.torus_mixedCoordinate_sum_le_sobolev_seminorm ψ (IsWeilDatumO.std hω) θ hθ (sgn ε M) X S₀ r d μ' 𝓕' hcov c hc K₀ hK₀ hK₀c μ 𝓕 hμ
  refine ⟨k, A, C, hC, fun n hn Ψ hΨ hlev t ht a ha => ?_⟩
  obtain ⟨α, hα1, hα2, hlevi⟩ := hA1 t ht.1 a ha
  have e : ω (a, 1) Ψ 0 = ω.toSgn ε (d.levi α, 1) Ψ 0 := by
    rw [← hlevi]
    show ω (a, 1) Ψ 0 = ω ((ofSgn ε M) ((ofSgn ε M).symm a), 1) Ψ 0
    rw [MulEquiv.apply_symm_apply]
  have hle := hA2 Ψ hΨ α
  rw [← e, GlobalTheory.T.halfPowerDetAbs_realDiagonal_torus θ hθ r X.rank t ht.1 α hα1 hα2] at hle
  have h2 := hB n hn Ψ hΨ hlev t ht α.1 hα1 hα2
  have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have hQ : 0 ≤ C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal :=
    mul_nonneg (mul_nonneg hC (pow_nonneg n.cast_nonneg _)) ENNReal.toReal_nonneg
  have h3 : ‖ω (a, 1) Ψ 0‖ₑ ≤ ENNReal.ofReal (C * (n : ℝ) ^ A *
      (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) := by
    refine hle.trans ((mul_le_mul' le_rfl h2).trans_eq ?_)
    rw [← ENNReal.ofReal_mul hP, mul_comm]
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hQ hP)).1 h3

end GlobalTheory.SiegelTorusTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaValueSiegelTorusElementLeSobolevSeminormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValue_siegelTorusElement_le_sobolevSeminorm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf)
    (c : ℝ) (hc : 0 < c) (K₀ : Set (WO M X)) (hK₀ : K₀ ∈ nhds (0 : WO M X)) (hK₀c : IsCompact K₀)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO M X → ℂ, IsThetaFunO ψ (sgn ε M) X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ‖ω (a, 1) Ψ 0‖ ≤ C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal *
          ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  first | exact @GlobalTheory.SiegelTorusTheta.torus_bound | exact GlobalTheory.SiegelTorusTheta.torus_bound | (intros; apply GlobalTheory.SiegelTorusTheta.torus_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelSiegelSetLeTorusPowerHeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SiegelThetaBound

theorem theta_le_torus_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (M X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω → ∀ (Φ : WO M X → ℂ), IsThetaFunO ψ (sgn ε M) X Φ → ∀ (r : ℕ) (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf → ∀ (Ω C₀ : Set (GA D M)) (K : Subgroup (GA D M)) (c : ℝ), IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GA D M)) → 0 < c → (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a → a⁻¹ * p * a ∈ C₀) → ∃ (N : ℕ) (C : ℝ), ∀ (h : GA D X), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a → ∀ k ∈ K, ‖thetaKO ω (p * a * k) h Φ‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hsub
  have hC₁ : IsCompact (C₀ * (K : Set (GA D M))) := hC₀.mul hK
  obtain ⟨K₀, hK₀n, hK₀c, m, e, hlev⟩ := GlobalTheory.T.weilTheta_level_polynomial_in_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ _ hC₁
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (sgn ε M) X
  obtain ⟨k, A, C, hC, hT⟩ := GlobalTheory.T.thetaValue_siegelTorusElement_le_sobolevSeminorm ψ θ hθ ε M X χ χ' ω hω r Xf Yf hW c hc K₀ hK₀n hK₀c μ 𝓕 hμ
  obtain ⟨N₂, C₂, hC₂, hU⟩ := GlobalTheory.T.sobolevSeminorm_weilTheta_polynomial_in_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ _ hC₁ μ 𝓕 hμ k
  refine ⟨e * A + N₂, C * |m| ^ A * C₂, fun h p hp t ht a ha k' hk' => ?_⟩
  have hy : a⁻¹ * p * a * k' ∈ C₀ * (K : Set (GA D M)) := Set.mul_mem_mul (hsub p hp t ht a ha) hk'
  have hΨ : IsThetaFunO ψ (sgn ε M) X (ω (a⁻¹ * p * a * k', h) Φ) := by
    have := hω.om_pres ((GlobalTheory.Grid.ofSgn ε M).symm (a⁻¹ * p * a * k'), h) Φ hΦ
    simpa [GlobalTheory.Grid.WRep.toSgn] using this
  obtain ⟨n, hn, hnle, hnlev⟩ := hlev _ hy h
  have key := hT n hn _ hΨ hnlev t ht a ha
  have hs := hU _ hy h
  have hsplit : thetaKO ω (p * a * k') h Φ = ω (a, 1) (ω (a⁻¹ * p * a * k', h) Φ) 0 := by
    have e1 : ((p * a * k', h) : GA D M × GA D X) = (a, 1) * (a⁻¹ * p * a * k', h) := by
      ext <;> simp [mul_assoc]
    unfold thetaKO
    rw [e1, map_mul]
    rfl
  rw [hsplit]
  refine key.trans ?_
  have hH : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := by
    exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ X h
  have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have hs0 : 0 ≤ (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (a⁻¹ * p * a * k', h) Φ)).toReal :=
    ENNReal.toReal_nonneg
  set H : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) with hHdef
  have hnA : (n : ℝ) ^ A ≤ |m| ^ A * H ^ (e * A) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (hnle.trans (mul_le_mul_of_nonneg_right (le_abs_self m)
      (pow_nonneg (zero_le_one.trans hH) e))) A
  calc C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (a⁻¹ * p * a * k', h) Φ)).toReal *
        ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)
      ≤ C * (|m| ^ A * H ^ (e * A)) * (C₂ * H ^ N₂) * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
        gcongr
    _ = C * |m| ^ A * C₂ * H ^ (e * A + N₂) * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
        rw [pow_add]; ring

end GlobalTheory.SiegelThetaBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelSiegelSetLeTorusPowerHeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_siegelSet_le_torusPower_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (M X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω → ∀ (Φ : WO M X → ℂ), IsThetaFunO ψ (sgn ε M) X Φ → ∀ (r : ℕ) (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf → ∀ (Ω C₀ : Set (GA D M)) (K : Subgroup (GA D M)) (c : ℝ), IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GA D M)) → 0 < c → (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a → a⁻¹ * p * a ∈ C₀) → ∃ (N : ℕ) (C : ℝ), ∀ (h : GA D X), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a → ∀ k ∈ K, ‖thetaKO ω (p * a * k) h Φ‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  first | exact @GlobalTheory.SiegelThetaBound.theta_le_torus_height | exact GlobalTheory.SiegelThetaBound.theta_le_torus_height | (intros; apply GlobalTheory.SiegelThetaBound.theta_le_torus_height <;> assumption)
end
end

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WeilConv

theorem weilConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.SquareSt.WeilConvergence := by
  intro D ψ θ hθ ε M X χ χ' ω hω p hsig hd ν 𝓕 hν Φ hΦ
  obtain ⟨τ, hτ⟩ := hsig
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have hν1 := hν.1
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram M)
  have hr : r ≤ p := GlobalTheory.T.hermitianWittIndex_le_negative_signature M hτ hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) M.rank M.gram (isHermND_gram M) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν1
  obtain ⟨N, C, hC⟩ := GlobalTheory.T.thetaKernel_siegelSet_le_torusPower_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  have hω' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hω
  have hcont : ∀ h, Continuous fun g => thetaKO ω g h Φ := fun h =>
    (hω'.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε M).prodMk continuous_const)
  have hinv : ∀ h, ∀ γ ∈ GQ M, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    have e1 : (((ofSgn ε M).symm (γ * g), h) : GA D (sgn ε M) × GA D X) =
        ((ofSgn ε M).symm γ, 1) * ((ofSgn ε M).symm g, h) := by simp
    show (ω.toSgn ε) ((ofSgn ε M).symm (γ * g), h) Φ 0 = (ω.toSgn ε) ((ofSgn ε M).symm g, h) Φ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (ofSgn_symm_mem_GQ ε hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hΦ)
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig M.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ M, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI := GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F M.rank r X.rank hc (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) with hIdef
  have key : ∀ h, ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤
      C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := fun h => by
    have hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
    calc ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤ ∫⁻ g in S, ‖thetaKO ω g h Φ‖ₑ ∂ν :=
          GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits (GQ M) ν hν.2 hSm hScov (hcont h).enorm.measurable
            (fun γ hγ g => by rw [hinv h γ hγ g])
      _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N *
            ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) := by
          refine hC₁ (fun g => ‖thetaKO ω g h Φ‖ₑ) _ (by fun_prop) fun q hq t ht a ha k hk => ?_
          have ht0 : ∀ i, 0 < t i := ht.1
          have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) :=
            Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
          rw [← ofReal_norm_eq_enorm]
          refine ENNReal.ofReal_le_ofReal ((hC h q hq t ht a ha k hk).trans ?_)
          have hH : 0 ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
          gcongr
          exact le_max_left _ _
      _ = C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := by
          rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
  refine ⟨N, (C₁ : ℝ) * max C 0 * I.toReal, fun h => ⟨⟨(hcont h).aestronglyMeasurable, ?_⟩, ?_⟩⟩
  · exact (key h).trans_lt (by finiteness)
  · rw [integral_norm_eq_lintegral_enorm (hcont h).aestronglyMeasurable]
    have hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
    refine (ENNReal.toReal_mono (by finiteness) (key h)).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.coe_toReal]
    ring

end GlobalTheory.WeilConv

end
