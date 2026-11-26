module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctional
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusLocalDataProductLocalWeights
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyRecursion
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBound
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentWeighted

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypotheses
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalSetupGap

theorem exists_seq {k : ℕ} (u : Fin k → ℝ) : ∃ U : ℕ → ℝ, ∀ i : Fin k, U (i.val + 1) = u i :=
  ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, fun i => by simp⟩

theorem exists_setup (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r}
    (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) (hS : SideG k r z π u μW μN μG νq) {c : ℝ} (hc : 0 < c)
    (hd : ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG (PI.BesselPeriodGGP.eps48 k r) mu →
      ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) :
    ∃ l : ∀ ν, (R ν).H → Wp,
      Setup lam u b bv ga h q0 z π μW μN μG νq R l (fun ν => c * fdegHC (fun a => lam a + (ν a : ℝ))) := by
  have hnum := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (h / 2) := hnum.1.2.2.2.2
  have hDG : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 →
      (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := by
    intro ν hν
    obtain ⟨hp, hds⟩ := hF ν hν
    exact ⟨hp, hds, h / 2, (hnum.2 ν hν).2.2.1, hok⟩
  have hex : ∀ ν : Fin (2 * r + k + 1) → ℤ,
      ∃ l : (R ν).H → Wp, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN l := by
    intro ν
    by_cases hν : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r (PI.BesselPeriodGGP.eps48 k r)
        (fun a => lam a + (ν a : ℝ)) (h / 2) (R ν) Wp z π u μW μN μG νq (hDG ν hν)
        (hnum.2 ν hν).2.2.1 hok hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hν⟩
  choose l hl using hex
  refine ⟨l, ?_⟩
  unfold Setup SideFam
  refine ⟨hN, hF, hS, fun ν hν => ⟨hl ν hν, ?_, ?_⟩⟩
  · exact mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hN ν hν).1
  · intro w hw
    exact hd _ (R ν) (hDG ν hν) w hw

theorem exists_setup_both : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt hzt R hR
  have := FiniteDimensional.complete ℂ W.Wp
  have := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨U, hU⟩ := exists_seq (uS D w τ)
  obtain ⟨U', hU'⟩ := exists_seq (uS D w' τ)
  obtain ⟨hNum, -, -⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w U hU
  obtain ⟨hNum', -, -⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w' U' hU'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := hZ.1
  obtain ⟨hπ, hπ', hzb, hzb', hT, hT', hμG, hμW, -, hμW', -, hμN, hνS, hνS'⟩ := hW
  have hTw : 0 < Tz D.R.k D.R.rS W.z := by
    rw [hT]
    unfold Tr
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hTT.2.2.1 : 0 < (D.mem w).A.T)
  have hTw' : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [hT']
    unfold Tr
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hTT.2.2.2.1 : 0 < (D.mem w').A.T)
  have hNH : PI.BesselPeriodGGP.IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hμN]
    refine GlobalTheory.haarLie_isHaarOn_Nset _ _ _ ?_ ENNReal.ofReal_lt_top
    unfold kapN
    exact ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ)
  have hS1 : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨hzb, hTw, ⟨_, hπ⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U _ _ hzb hTw hπ hU, hμW, hNH, hμG, hνS⟩
  have hS2 : SideG D.R.k D.R.rS W.z' W.π' U' W.μW' W.μN W.μG W.νS' :=
    ⟨hzb', hTw', ⟨_, hπ'⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U' _ _ hzb' hTw' hπ' hU', hμW', hNH, hμG,
      hνS'⟩
  have hM1 := (GlobalTheory.BesselMoveGap.bessel_move_gap hH D.R.k D.R.rS W.Wp W.z W.π U
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.μW W.μN W.μG W.νS t ht hNt
    (hzt W.z hzb).1 (hzt W.z hzb).2 hS1).1
  have hM2 := (GlobalTheory.BesselMoveGap.bessel_move_gap hH D.R.k D.R.rS W.Wq W.z' W.π' U'
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.μW' W.μN W.μG W.νS' t ht hNt
    (hzt W.z' hzb').1 (hzt W.z' hzb').2 hS2).1
  obtain ⟨c, hc, hsch⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 D.R.k D.R.rS
    (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) W.μG hμG
  obtain ⟨l, hl⟩ := exists_setup hH hNum hR hM1 hc (fun mu Q h => (hsch mu Q h).1)
  obtain ⟨l', hl'⟩ := exists_setup hH hNum' hR hM2 hc (fun mu Q h => (hsch mu Q h).1)
  exact ⟨U, U', l, l', _, hl, hl'⟩

end GlobalTheory.Amp.LocalSetupGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypothesesStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  first | exact @GlobalTheory.Amp.LocalSetupGap.exists_setup_both | exact GlobalTheory.Amp.LocalSetupGap.exists_setup_both | (intros; apply GlobalTheory.Amp.LocalSetupGap.exists_setup_both <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqSmulNormalisedAmplitudeLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqSmulNormalisedAmplitudeLargeGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpNormalGap

open GlobalTheory.AmpNormal

theorem one_side_gap (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} {dd m : ℝ}
    (hdg : R.IsDG ε mu) (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hc : c ≠ 0)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B)
    (hl : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l)
    (hbe : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hw : R.KFin w) (hm : 0 < m)
    (hmass : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) = ENNReal.ofReal m)
    (hd0 : 0 < dd) (hdd : ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) :
    (∃ v, R.KFin v ∧ l v ≠ 0) ∧ ∃ β : ℂ, (∀ v ∈ R.sm, B v = β • l v) ∧ m * dd = ‖β‖ ^ 2 * ‖w‖ ^ 2 := by
  have hds : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hdg
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨hmul, hone, hinn, hsm, hTKsm, hTK, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hKF k r ε mu R hds
  obtain ⟨hG1, hGm, hGi⟩ := uHGroup _ _ (det_hpk k r)
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hcomm, hpsi⟩ := hz z hS.1
  have htd : IsUnit t.det := (hGi t ht).1
  have hti : t⁻¹ ∈ GG k r := (hGi t ht).2
  have hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ := by
    refine ⟨⟨ContinuousLinearMap.ext hone, fun a ha b hb => ContinuousLinearMap.ext (hmul a ha b hb)⟩, fun g hg v => ?_,
      hcont⟩
    rw [@norm_eq_sqrt_re_inner ℂ, hinn g hg, ← @norm_eq_sqrt_re_inner ℂ]
  have e1 : ∀ v, R.σ t⁻¹ (R.σ t v) = v := fun v => by
    rw [← hmul _ hti _ ht, Matrix.nonsing_inv_mul _ htd, hone]
  have e2 : ∀ v, R.σ t (R.σ t⁻¹ v) = v := fun v => by
    rw [← hmul _ ht _ hti, Matrix.mul_nonsing_inv _ htd, hone]
  obtain ⟨hS', hR⟩ := GlobalTheory.BesselMoveGap.bessel_move_gap hH k r Wp z π u c μW μN μG νq t ht hN hcomm hpsi hS
  obtain ⟨hbes, hmove⟩ := hR R hU
  obtain ⟨l₁, hl₁⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp z π u μW _ μG _ hdg hgap hok hS'
  have hl₂ : IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) (fun v => l (R.σ t v)) := by
    refine ⟨(hbes l).1 hl, fun x hx v hv => ⟨(hl₁.2 x hx v hv).1, ?_⟩⟩
    rw [(hl₁.2 x hx v hv).2, ← hbe _ (hsm t ht x hx) _ (hTK t ht v hv),
      hmove l₁ hl₁ _ (hsm t ht x hx) _ (hTK t ht v hv), e1, e1]
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r :=
    (GlobalTheory.quotMeas_ae_mem_and_measurable hKF k r ε mu R Wp z π u μW μN μG νq hds hS).1
  have htr : ∀ F : R.H → Wp,
      PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) (fun g => F (R.σ t (R.σ g w))) =
        PI.BesselPeriodGGP.l2SG νq (fun g => F (R.σ g w)) := by
    intro F
    unfold PI.BesselPeriodGGP.l2SG
    refine (lintegral_map_equiv _ (lmulEquiv t htd)).trans (lintegral_congr_ae ?_)
    filter_upwards [hae] with x hx
    have : R.σ t (R.σ (Matrix.of (lmulEquiv t htd x)) w) = R.σ (Matrix.of x) w := by
      show R.σ t (R.σ (t⁻¹ * Matrix.of x) w) = _
      rw [hmul _ hti _ hx, e2]
    simp only [this]
  have hB₁ : IsBes R z π (fun v => B (R.σ t v)) := (hbes B).1 hB
  obtain ⟨v, hv, hv0⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r ε mu h R Wp z π u μW _ μG _ (fun v => B (R.σ t v))
    (fun v => l (R.σ t v)) w hds hgap hok hS' hB₁ hw
    (by rw [htr B, hmass]; exact (ENNReal.ofReal_pos.2 hm).ne') (by rw [htr B, hmass]; exact ENNReal.ofReal_ne_top) hl₂
  have hvs : v ∈ R.sm := hTKsm v (hKT v hv)
  have hnz : NzOn R (fun v => l (R.σ t v)) := ⟨v, hvs, hv0⟩
  refine ⟨GlobalTheory.exists_kFin_ne_zero_of_cwCont hKF k r ε mu R hds Wp l hl.1 hl.2.1 hl.2.2.2 ⟨_, hsm t ht v hvs, hv0⟩, ?_⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.besselMaps_proportional_discreteSeries_largeGap hH k r ε mu R Wp z π u μW _ μG _ _ _ hdg hS' hl₂.1 hnz hB₁
  have hβ' : ∀ v ∈ R.sm, B v = β • l v := fun v hv => by
    have := hβ _ (hsm _ hti v hv)
    simpa only [e2] using this
  refine ⟨β, hβ', ?_⟩
  have hws : w ∈ R.sm := hTKsm w (hKT w hw)
  have hiso := (Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH.1 k r ε mu h R Wp z π u μW _ μG _ _ dd hdg hgap hok hS' hl₂ hdd hnz).2 w hws
  have h2 := (htr fun v => ((Real.sqrt dd : ℝ) : ℂ) • l v).symm.trans hiso
  have h3 : ENNReal.ofReal dd * PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) =
      ENNReal.ofReal (‖β‖ ^ 2) * PI.BesselPeriodGGP.l2SG νq (fun g => ((Real.sqrt dd : ℝ) : ℂ) • l (R.σ g w)) := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have en : ∀ y : Wp, ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl
    rw [en, en, hβ' _ (hsm _ hx w hws), ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
      norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow,
      Real.sq_sqrt hd0.le]
    congr 1
    ring
  rw [hmass, h2, ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h3
  linarith

theorem amp_eq_smul_normalised_gap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  intro hH D τ w w' θ W lam A h l l' hθ hka hT hT' hW hA hgap hok hl hl' hbe hbe'
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW
  obtain ⟨hlam, hds, b1, b2, hsm0, hv0, ⟨P, hP, hlowK⟩, hc, l1, l2, -⟩ := hA
  set R : Rep D.R.k D.R.rS := ⟨A.H, A.σ⟩ with hR
  have hDS : R.IsDS (epsSH D.R) lam := ⟨hlam, hds⟩
  have hDG : R.IsDG (epsSH D.R) lam := ⟨hlam, hds, h, hgap, hok⟩
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨-, -, -, hsm, hTKsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF _ _ _ _ R hDS
  obtain ⟨-, hGm, -⟩ := uHGroup _ _ (det_hpk D.R.k D.R.rS)
  rw [hN] at q1 q2 hbe hbe'
  obtain ⟨U, hS⟩ := sideG_of ENNReal.ofReal_lt_top z1 (t1 ▸ hT) c1 w1 hG q1
  obtain ⟨U', hS'⟩ := sideG_of ENNReal.ofReal_lt_top z2 (t2 ▸ hT') c2 w2 hG q2
  have hcs : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have : 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = 2 * (D.host.ka / gg D) := by
      rw [mul_div_assoc]; rfl
    rw [this]
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * (D.host.ka / gg D)).ne'
  have hn : 0 < ‖A.v0‖ := norm_pos_iff.2 hv0
  set w0 : A.H := ((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0 with hw0
  have hw1 : ‖w0‖ = 1 := by rw [hw0, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hlow : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 :=
    ⟨P, hP, hw1, Submodule.smul_mem _ _ hlowK⟩
  have hv : A.v0 = ((‖A.v0‖ : ℝ) : ℂ) • w0 := by
    rw [hw0, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hvK : R.KFin A.v0 := by
    obtain ⟨S, h1, h2, h3⟩ := hwK
    exact ⟨S, h1, hv ▸ S.smul_mem _ h2, h3⟩
  have hws : w0 ∈ R.sm := hTKsm _ (hKT _ hwK)
  obtain ⟨c₀, hc₀, hdeg⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 _ _ (epsSH D.R) W.μG hG
  have hdd := (hdeg lam R hDG).1
  have hd0 : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC lam := mul_pos hc₀ (GlobalTheory.BesselNorm.fdegHC_pos lam hlam.1.injective)
  set dd := c₀ * Formalism.QuantumDeterminants.fdegHC lam
  have hp : (0 : ℝ) < Module.finrank ℂ W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact_mod_cast Module.finrank_pos
  have hq : (0 : ℝ) < Module.finrank ℂ W.Wq := by
    obtain ⟨g, -, hnt, -⟩ := c2
    exact_mod_cast Module.finrank_pos
  obtain ⟨nz1, β, hβ, e1⟩ := one_side_gap hH R (B := A.B) (l := l) hDG hgap hok hS hcs (isBesselMapSm_of b1) hl hbe hvK
    (mul_pos hc hp) l1 hd0 hdd
  obtain ⟨nz2, β', hβ', e2⟩ := one_side_gap hH R (B := A.B') (l := l') hDG hgap hok hS' hcs (isBesselMapSm_of b2) hl' hbe'
    hvK (mul_pos hc hq) l2 hd0 hdd
  refine ⟨nz1, nz2, w0, (A.cN : ℂ)⁻¹ * ((β * (‖A.v0‖ : ℝ)) * star (β' * (‖A.v0‖ : ℝ))), hlow, ?_, ?_⟩
  · have hw00 : w0 ≠ 0 := by rw [← norm_pos_iff, hw1]; exact one_pos
    rw [show PI.BesselPeriodGGP.fdegH W.μG A.σ w0 = dd from hdd w0 hw00]
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    simp only [norm_mul, norm_star, norm_inv, Complex.norm_real, norm_norm, Real.norm_of_nonneg hc.le]
    have e1' : ‖β‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wp * dd := e1.symm
    have e2' : ‖β'‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wq * dd := e2.symm
    rw [mul_pow, mul_pow, mul_pow, mul_pow, e1', e2']
    field_simp
  · intro ν γ hγ hν
    have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := hν
    unfold LocS.J amp ampJ
    rw [Complex.ofReal_one, inv_one, one_smul, mul_smul]
    congr 1
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have a1 : A.Φ (γ * Matrix.of x) = (β * (‖A.v0‖ : ℝ)) • l (A.σ (γ * Matrix.of x) w0) := by
      have hs := hsm _ (hGm _ hγ _ hx) w0 hws
      have hs' := hsm _ (hGm _ hγ _ hx) A.v0 hsm0
      unfold LocS.Φ
      rw [hβ _ hs', mul_smul, ← hl.2.1 _ _ hs, ← map_smul, ← hv]
    have a2 : A.Φ' (Matrix.of x) = (β' * (‖A.v0‖ : ℝ)) • l' (A.σ (Matrix.of x) w0) := by
      have hs := hsm _ hx w0 hws
      have hs' := hsm _ hx A.v0 hsm0
      unfold LocS.Φ'
      rw [hβ' _ hs', mul_smul, ← hl'.2.1 _ _ hs, ← map_smul, ← hv]
    rw [a1, a2]
    ext y
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.smul_apply,
      smul_smul]
    congr 1
    simp only [RCLike.star_def]
    ring

end GlobalTheory.AmpNormalGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqSmulNormalisedAmplitudeLargeGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_eq_smul_normalisedAmplitude_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  first | exact @GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap | exact GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap | (intros; apply GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusLocalDataProductLocalWeightsStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_genus_local_data_product_local_weights : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ d0 : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ V1 : ℝ, 0 < V1 ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → {p | d p ≠ d0 p}.Finite → massA F F' d = ENNReal.ofReal (V1 * ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) := by
  first | exact @GlobalTheory.Unfold.mass_genus_local_weights | exact GlobalTheory.Unfold.mass_genus_local_weights | (intros; apply GlobalTheory.Unfold.mass_genus_local_weights <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMajorantLengthMomentLowestKType
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMajorantLengthMomentLowestKType
noncomputable section

namespace GlobalTheory.MomOneGap

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

theorem lev_zero_of_wt (hH : HypsG) (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Q : Mx k r}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hE : R.IsE Q E) (S : Submodule ℂ R.H) (hfin : FiniteDimensional ℂ S)
    (hst : PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S)
    (hmax : ∀ (μ : Fin (2 * r + k + 1) → ℝ) (v : R.H), v ∈ S → v ≠ 0 →
      PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) μ v →
      PI.UpqRep.CDom ε μ (Formalism.QuantumDeterminants.lowK ε mu))
    (w : R.smSub) (hwS : (w : R.H) ∈ S)
    (hw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) (w : R.H)) :
    Lev ε E mu 0 w := by
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hDS : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hR
  obtain ⟨-, hS2⟩ := GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r ε mu R hDS Q hQ S hfin hst
  obtain ⟨hw1, hw2⟩ := GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R hDS Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w hw
  have hMod := Gp91.GlobalTheory.T.cayley_endomorphisms_modular hH k r ε mu R hk hR Q E hQ hE
  refine GlobalTheory.lev_zero_of_kHighest _ _ _ E _ w hMod.1 hMod.2.1 ⟨hw1, ?_⟩ ?_
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he _ hwS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨hwS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

theorem oneLength_moment_lowestType_largeGap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ)
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (ν : Fin (2 * r + k + 1) → ℤ) (q : ℕ)
    (hν : n1 ν + (r + 1) * q ≤ q0) (hq : (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2) (w : (R ν).H)
    (hw : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w)
    (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq
      ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ q) := by
  classical
  have hHG : HypsG := hH.1
  have hK : PI.KFinSmooth := hHG.1.2.2.1
  have hSG : SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg :=
    (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg).1 hS
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ, hw1, hwL⟩ := hw
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.smooth_gl_module hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := hSG.2.1 ν hν0
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 _ _ _ hDS Q hQ
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r _ _ (R ν) hDS
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hA' := mul_nonneg hA (by positivity : (0 : ℝ) ≤ (b ^ 2) ^ (2 * r))
  have hnum := GlobalTheory.MomNum.mom_num k r lam u b bv ga h q0 _ hNum hT
  have hsmS : ∀ S : Submodule ℂ (R ν).H, FiniteDimensional ℂ S →
      PI.UpqRep.IsKStableOn (PI.BesselPeriodGGP.eps48 k r) (fun g => (R ν).σ (Q⁻¹ * g * Q)) S → S ≤ (R ν).smSub :=
    fun S h1 h2 v hv => ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r _ _ (R ν) hDS Q hQ S h1 h2).1 v hv).2
  have key := GlobalTheory.MomOne.lintegral_le_of_highest (m := νq) hD.2.2.1 _ (R ν).smSub hsmS
    (fun v x => ((lenA k r z (Matrix.of x) a ^ q * Real.sqrt (dg ν) : ℝ) : ℂ) • l ν ((R ν).σ (Matrix.of x) v))
    ?_ ?_ ?_ ?_ (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ q) (pow_nonneg (hA'.trans hnum) q) ?_ w hwL hw1
  · simpa only [GlobalTheory.MomOne.norm_sq_scaled _ _ hdg.le] using key
  · intro v hv v' hv'
    filter_upwards [hG] with x hx
    simp only [Pi.add_apply]
    rw [map_add (f := _), hBeL.1.1 _ (hsm _ hx v hv) _ (hsm _ hx v' hv'), smul_add]
  · intro c v hv
    filter_upwards [hG] with x hx
    simp only [Pi.smul_apply]
    rw [map_smul, hBeL.1.2.1 c _ (hsm _ hx v hv), smul_comm]
  · intro v hv
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((((hlen a).pow_const q).mul_const _).aestronglyMeasurable)).smul (hmeas (l ν) hBeL.1 v hv)
  · intro g hg v hv
    obtain ⟨hgG, hgU⟩ := GlobalTheory.MomOne.conj_back hQ hg
    simp only [GlobalTheory.MomOne.norm_sq_scaled _ _ hdg.le]
    have := GlobalTheory.MomOne.lintegral_rmul hSide
      (fun x => lenA k r z x a ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ x v)‖ ^ 2))
      (((GlobalTheory.LengthCont.lenA_continuousOn k r z hSide.1 hT a).pow _).mul (continuousOn_const.mul
        ((GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r _ _ (R ν) hDS Wp (l ν) hBeL.1.1 hBeL.1.2.1 hBeL.1.2.2.2
          v hv).1.norm.pow 2))) ?_ hgG
    · rw [← this]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      rw [GlobalTheory.MomOne.lenA_mul_unitary z _ hgU, hmul _ hx _ hgG]
    · intro s hs x hx
      have e := (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.2 s hs a
      obtain ⟨h', hh, m, hmN, rfl⟩ := hs
      obtain ⟨u₀, hπ⟩ := hSide.2.2.1
      have hsG : h' * m ∈ GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hmN.1
      beta_reduce
      rw [e, hmul _ hsG _ hx, hBeL.1.2.2.1 h' hh m hmN _ (hsm _ hx v hv), norm_smul,
        Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm, one_mul, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h' hh]
  · intro S hfd hst hcd v hv hv1 hwt
    simp only [GlobalTheory.MomOne.norm_sq_scaled _ _ hdg.le]
    have hvs : v ∈ (R ν).sm := hsmS S hfd hst hv
    by_cases hnz : NzOn (R ν) (l ν)
    · have hLev := lev_zero_of_wt hHG hk hDG hQ (hE ν hν0).1 S hfd hst hcd ⟨v, hvs⟩ hv hwt
      have hv1' : ‖(⟨v, hvs⟩ : (R ν).smSub)‖ = 1 := hv1
      have hmain := GlobalTheory.MomOne.single_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r q (fun a x => lenA k r z (Matrix.of x) a)
        (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2)
        (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
        hlen
        (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
        (((hmeas (l ν) hBeL.1 v hvs).norm.aemeasurable.pow_const 2).const_mul _)
        (fun x => mul_nonneg hdg.le (by positivity))
        (by
          have := ((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hHG k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hSG ν hν0).2 hnz).2 v hvs
          simpa only [one_mul, hv1, one_pow, ENNReal.ofReal_one] using this)
        hA (one_le_pow₀ hb)
        (fun q' hq' => by
          have := Gp91.GlobalTheory.T.family_setup_cayley_recursion hHG k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hSG hQ hE
            q' ν (by omega) 0 (by omega) ⟨v, hvs⟩ hLev
          simpa only [hv1', one_pow, mul_one] using this)
        (fun a q' hq' => by
          have := Gp91.GlobalTheory.T.family_setup_cayley_bound hHG k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hSG hQ hE ν hν0
            0 q' (by omega) a ⟨v, hvs⟩ hLev
          simpa only [hv1', one_pow, mul_one] using this) a
      exact hmain.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hA' hnum _))
    · have hz : ∀ v ∈ (R ν).sm, l ν v = 0 := by
        intro v hv
        by_contra hne
        exact hnz ⟨v, hv, hne⟩
      refine le_of_eq_of_le ?_ bot_le
      rw [bot_eq_zero, ← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      rw [hz _ (hsm _ hx v hvs)]
      simp

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem moment_one_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν (q : ℕ), n1 ν + (r + 1) * q ≤ q0 → (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) :=
  fun hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν q hν hq w hw a =>
    oneLength_moment_lowestType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν q hν hq w hw a

end main

end GlobalTheory.MomOneGap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMajorantLengthMomentLowestKTypeStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMajorantLength_moment_lowestKType : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν (q : ℕ), n1 ν + (r + 1) * q ≤ q0 → (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) := by
  first | exact @GlobalTheory.MomOneGap.moment_one_gap | exact GlobalTheory.MomOneGap.moment_one_gap | (intros; apply GlobalTheory.MomOneGap.moment_one_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselExteriorPowerConstantBoundLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductMomentFirstLengthsLowestVector
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductMomentFirstLengthsLowestVector
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProdGap

theorem product_moment_first_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν hNz
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  obtain ⟨hG, -, -, -⟩ := hH
  have hKS : PI.KFinSmooth := by
    unfold BranchingSupport.HypsG BranchingSupport.InputsG at hG
    exact hG.1.2.2.1
  obtain ⟨hN, hFam, hSd, hSF⟩ := hS
  have hk : 1 ≤ k := by
    unfold BranchingSupport.Num at hN
    exact hN.1
  have hz : Formalism.QuantumDeterminants.inWb k r z := by
    unfold BranchingSupport.SideG at hSd
    exact hSd.1
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := by
    unfold BranchingSupport.SideG at hSd
    exact hSd.2.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  have hDS : ∀ ν' : Fin (2 * r + k + 1) → ℤ, n1 ν' ≤ q0 →
      (R ν').IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν' a : ℝ)) := by
    intro ν' h'
    unfold BranchingSupport.IsFam at hFam
    exact hFam ν' h'
  have hDG : ∀ ν' : Fin (2 * r + k + 1) → ℤ, n1 ν' ≤ q0 →
      (R ν').IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν' a : ℝ)) := by
    intro ν' h'
    have h2 := hSG
    unfold BranchingSupport.SetupG BranchingSupport.IsFamG at h2
    exact h2.2.1 ν' h'
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := by
    unfold PI.UpqRep.IsCayleyU at hQ
    exact ⟨⟨Q, star Q, Matrix.mem_unitaryGroup_iff.mp hQ.2, Matrix.mem_unitaryGroup_iff'.mp hQ.2⟩, rfl⟩
  have hEx : ∀ ν' : Fin (2 * r + k + 1) → ℤ, ∃ E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E' ∧ Formalism.REAL.GlRel E' := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E', h1, h2⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hKS k r _ _ (R ν') (hDS ν' h') Q hQu
      exact ⟨E', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hEx
  obtain ⟨w, hw1, -, hKH, hfin⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hKS k r _ _ (R ν) (hDS ν hν0) Q (E ν) hQ (hE ν hν0).1
  have hMod := Gp91.GlobalTheory.isMod_smooth_of_isDS hG k r _ _ (R ν) hk (hDG ν hν0) Q (E ν) hQ (hE ν hν0).1
  have hLev : BranchingSupport.Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w := by
    unfold BranchingSupport.IsMod at hMod
    exact GlobalTheory.lev_zero_of_kHighest _ _ _ _ _ _ hMod.1 hMod.2.1 hKH hfin
  have hq4 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have h1 : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hA : ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q) := by
    intro q hq
    have h1 := Gp91.GlobalTheory.Moment.moment_first_length hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ
      (fun ν' h' => hE ν' h') q ν (le_trans (Nat.add_le_add_left hq _) hν) 0 (hq4 q hq) w hLev
    rwa [hw1, one_pow, mul_one] at h1
  have hRr : ∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ /
      lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤
      ENNReal.ofReal ((b ^ 2) ^ (2 * q)) := by
    intro a q hq
    have h1 := Gp91.GlobalTheory.RatioMoment.ratio_moment hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ
      (fun ν' h' => hE ν' h') ν hν0 0 q (hq4 q hq) a w hLev
    rwa [hw1, one_pow, mul_one] at h1
  have hdg : 0 < dg ν := (hSF ν hν0).2.1
  have hmass : ∫⁻ x, ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) ∂νq = 1 := by
    have h1 := ((Gp91.GlobalTheory.MomMass.mom_mass hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν0).2
      hNz).2 (w : (R ν).H) w.2
    simp only [one_mul] at h1
    rw [h1]
    have h2 : ‖(w : (R ν).H)‖ = 1 := hw1
    rw [h2, one_pow, ENNReal.ofReal_one]
  obtain ⟨hae, -, hlenM, hbesM⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hKS k r _ _ (R ν) Wp z π u μW μN μG νq (hDS ν hν0) hSd
  obtain ⟨hIsBes, -⟩ := (hSF ν hν0).1
  have hPhM : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) νq :=
    ((hbesM (lb ν) hIsBes (w : (R ν).H) w.2).norm.aemeasurable.pow_const 2).const_mul (dg ν)
  have hpos : ∀ a, ∀ᵐ x ∂νq, 0 < lenA k r z (Matrix.of x) a := fun a =>
    hae.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hz hT (Matrix.of x) hx).2.2.1 a
  have hnf := (GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN).1
  have hb1 : 1 ≤ b := by
    have h1 := hnf.2.2.1
    have h2 : (0 : ℝ) ≤ 2 * r + k := by positivity
    linarith
  have hbv : 0 ≤ bv := by linarith [hnf.2.1]
  have hA0 : 0 ≤ ((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hT.le (by positivity))) (pow_nonneg (by linarith) _)
  have key := GlobalTheory.T.initial_lengths_product_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r l hl (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) ((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2) (fun a => hlenM a) hpos hPhM
    (fun x => mul_nonneg hdg.le (sq_nonneg _)) hmass hA0 (one_le_pow₀ hb1) hA hRr
  refine ⟨(w : (R ν).H), w.2, hw1, le_trans key (ENNReal.ofReal_le_ofReal ?_)⟩
  exact pow_le_pow_left₀ (mul_nonneg hA0 (by positivity))
    (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hN hT) l

end GlobalTheory.MomProdGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductMomentFirstLengthsLowestVectorStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productMoment_firstLengths_lowestVector : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  first | exact @GlobalTheory.MomProdGap.product_moment_first_gap | exact GlobalTheory.MomProdGap.product_moment_first_gap | (intros; apply GlobalTheory.MomProdGap.product_moment_first_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselExteriorPowerConstantBoundLargeGap
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapWedgeKappaL

theorem n1_add_eZ_le_add_card' {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : ∑ i, (eZ I i).natAbs = I.card := by
    have : ∀ i, (eZ I i).natAbs = if i ∈ I then 1 else 0 := by
      intro i; unfold eZ; split_ifs <;> rfl
    simp [this]
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem eZ_injective' {n : ℕ} : Function.Injective (eZ : Finset (Fin n) → Fin n → ℤ) := by
  intro I J h
  ext i
  have := congrFun h i
  unfold eZ at this
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

theorem kappa_bound : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hyp := hH.1
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hSG
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := n1_add_eZ_le_add_card' ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) l => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r l
  have hdual := fun J : Sub (2 * r + k + 1) l =>
    Gp91.GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (lb ν) hDS hDSJ hF hT hG
      (fun s hs => (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances k r l hl z hG.1).1 s hs) (hSF ν hν0).1 hnz J
      (lb (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) l, ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, lb ν (ev (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • lb (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) l, 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg
    ((GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS)
  obtain ⟨w, hw, hw1, hint⟩ := GlobalTheory.T.productMoment_firstLengths_lowestVector hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) l) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply eZ_injective'
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := Gp91.GlobalTheory.T.tensor_moment_weighted hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • lb ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • lb (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : lb (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hHs : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hHs] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [(GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances k r l hl z hG.1).2 _ hx, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

end GlobalTheory.GapWedgeKappaL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselExteriorPowerConstantBoundLargeGapStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselExteriorPower_constant_bound_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  first | exact @GlobalTheory.GapWedgeKappaL.kappa_bound | exact GlobalTheory.GapWedgeKappaL.kappa_bound | (intros; apply GlobalTheory.GapWedgeKappaL.kappa_bound <;> assumption)
end
end
