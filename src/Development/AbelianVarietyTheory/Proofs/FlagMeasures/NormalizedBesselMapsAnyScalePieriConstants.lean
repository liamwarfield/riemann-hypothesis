module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselMoveGap

open GlobalTheory.BesselMove

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bessel_move_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  intro _ k r Wp _ _ _ _ z π u c μW μN μG νq t ht hN hc hψ hS
  obtain ⟨s1, s2, s3, s4, hW, hμN, hG, hq⟩ := hS
  have hti : t⁻¹⁻¹ = t := Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (unit_of ht))
  have hcan : ∀ n : MM k r, t * (t⁻¹ * n * t) * t⁻¹ = n := fun n => by
    simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one, mic ht]
  have hN' : ∀ n ∈ Nset k r, t⁻¹ * n * t ∈ Nset k r := fun n hn => by
    rw [hN, hcan]; exact hn
  have hc' : ∀ h ∈ UWset k r z, t⁻¹ * h = h * t⁻¹ := fun h hh => by
    calc t⁻¹ * h = t⁻¹ * (h * t) * t⁻¹ := by simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
      _ = h * t⁻¹ := by rw [← hc h hh, imc ht]
  refine ⟨⟨s1, s2, s3, s4, hW, haar_conj ht hN hμN, hG, ?_⟩, fun R hR => ⟨fun B => ⟨fun hB => ?_, fun hB => ?_⟩, ?_⟩⟩
  · have := quot_conj ht hG hq
    rw [← muS_conj ht hW hμN hc] at this
    exact this
  · exact bessel_transport hR ht (fun n hn => (hN n).mp hn) hc hψ hB
  · have h := bessel_transport (ψ' := psi k r z c) hR (inv_mem ht) (fun n hn => by rw [hti]; exact hN' n hn) hc'
      (fun n hn => by rw [hti, hψ _ (hN' n hn), hcan]) hB
    have e : (fun v => B (R.σ t (R.σ t⁻¹ v))) = B := by
      funext v
      rw [← sig_mul hR ht (inv_mem ht), mul_inv' ht, sig_one hR]
    rw [e] at h
    exact h
  · intro l₁ hl x hx v hv
    haveI := hW.1
    haveI := hμN.1
    rw [← (hl.2 _ (sig_sm hR (inv_mem ht) hx) _ (sig_TK hR (inv_mem ht) hv)).2]
    show _ = Formalism.FourierDecayAlt.ThreeDimData.be z cStd π R.σ μW (μN.map (conjE ht)) _ _
    unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [prod_conj ht, integral_map_equiv]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod hW hμN] with p hp
    show (⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) x⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ =
      (⟪R.σ t⁻¹ v, R.σ (Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t)) (R.σ t⁻¹ x)⟫_ℂ *
        star (psi k r z cStd (t⁻¹ * Matrix.of p.2 * t))) • π (Matrix.of p.1)⁻¹
    rw [hψ _ (hN' _ hp.2), hcan, ← sig_inner hR (inv_mem ht) v,
      ← sig_mul hR (inv_mem ht) (mul_mem' hp.1.1 hp.2.1),
      ← sig_mul hR (mul_mem' hp.1.1 (hN' _ hp.2).1) (inv_mem ht)]
    have e : Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t) * t⁻¹ = t⁻¹ * (Matrix.of p.1 * Matrix.of p.2) := by
      simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← hc' _ hp.1, Matrix.mul_assoc]
    rw [e]

end GlobalTheory.BesselMoveGap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstantsStatement
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  first | exact @GlobalTheory.BesselMoveGap.bessel_move_gap | exact GlobalTheory.BesselMoveGap.bessel_move_gap | (intros; apply GlobalTheory.BesselMoveGap.bessel_move_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypotheses
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapSetup

theorem isFamG_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) :
    IsFamG lam q0 R := by
  have H := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  intro ν hν
  have hd := hF ν hν
  exact ⟨hd.1, hd.2, ⟨h / 2, (H.2 ν hν).2.2.1, H.1.2.2.2.2⟩⟩

theorem families_gap : (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → IsFamG lam q0 R) ∧ ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg ↔ SetupG lam u b bv ga h q0 z π μW μN μG νq R lb dg := by
  refine ⟨isFamG_of_num, ?_⟩
  intro k r Wp _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg
  constructor
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, isFamG_of_num k r lam u b bv ga h q0 R hN hF, hS, hSF⟩
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, fun ν hν => GlobalTheory.isDS_of_isDG (hF ν hν), hS, hSF⟩

end GlobalTheory.GapSetup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.families_have_largeGap_of_numericalHypotheses : (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → IsFamG lam q0 R) ∧ ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg ↔ SetupG lam u b bv ga h q0 z π μW μN μG νq R lb dg := by
  first | exact @GlobalTheory.GapSetup.families_gap | exact GlobalTheory.GapSetup.families_gap | (intros; apply GlobalTheory.GapSetup.families_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TFrameOfRanksRowThree
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem tFrame_of_ranksRow_three : ∀ 𝒞 : FamClass,
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) →
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro 𝒞 h
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := Formalism.L2.SG.OwnFacts.FD.factDsigHC
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  exact Formalism.L2.SG.Pf.SzHypFam.hTF_of_ranks 3 (𝒞 := 𝒞) h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapsProportionalDiscreteSeriesLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapsProportionalDiscreteSeriesLargeGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapLine

theorem psi_const_gap : Formalism.FourierDecayAlt.ThreeDimData.PsiConst := by
  intro k r z c g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

theorem line_of_uniqGap (hU : GlobalTheory.GapIn.UniqGap) {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ} {σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hk : 1 ≤ k) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h)
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {B0 B : H → Wp}
    (h0 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B0)
    (h1 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B)
    {x0 : H} (hx0 : x0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hne : B0 x0 ≠ 0) :
    ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x = κ • B0 x := by
  have hpsi : Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) := funext (psi_const_gap k r z c)
  rw [hpsi] at h0 h1
  obtain ⟨a, b, hab, hrel⟩ :=
    hU k r ε lam h H σ z (fun _ => c) u Wp π hk hg hh hl hσ hz hT (fun _ => hc) hπ B B0 h1 h0
  have ha : a ≠ 0 := by
    rintro rfl
    have hb : b ≠ 0 := hab.resolve_left (fun h => h rfl)
    have := hrel x0 hx0
    simp only [zero_smul, zero_add] at this
    exact hne ((smul_eq_zero.mp this).resolve_left hb)
  refine ⟨-(b / a), fun x hx => ?_⟩
  have h' : a • B x = -(b • B0 x) := eq_neg_of_add_eq_zero_left (hrel x hx)
  calc B x = a⁻¹ • (a • B x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = -(b / a) • B0 x := by rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem bessel_line_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  intro hH k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l l₁ hDG hS hl hnz hl₁
  obtain ⟨w, hw, hne⟩ := hnz
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  obtain ⟨h, hgap, hk, hh, -, -⟩ := hDG.gap
  have hc : Formalism.QuantumDeterminants.cStd ≠ 0 := by
    unfold Formalism.QuantumDeterminants.cStd
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact line_of_uniqGap hH.2.1 hk hgap hh hDG.hc hDG.ds hz hT hc hπ hl hl₁ hw hne

end GlobalTheory.GapLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapsProportionalDiscreteSeriesLargeGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselMaps_proportional_discreteSeries_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  first | exact @GlobalTheory.GapLine.bessel_line_gap | exact GlobalTheory.GapLine.bessel_line_gap | (intros; apply GlobalTheory.GapLine.bessel_line_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselPeriodNonzeroGap

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity GlobalTheory.BesselPeriodNonzero


set_option maxHeartbeats 1600000 in
theorem nzOn_of_mass (hy : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {R : Rep k r}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} (hR : R.IsDS ε mu)
    (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hB : IsBes R z π B) (hwK : R.KFin w) {c : ℝ} (hc : 0 ≤ c)
    (hiso : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = ENNReal.ofReal (c * ‖v‖ ^ 2))
    (h0 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0) (hl : IsBeL R z π μW μN l) :
    ∃ v ∈ R.sm, l v ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hK : PI.KFinSmooth := hy.1.1.2.2.1
  have hRG : R.IsDG ε mu := ⟨hR.1, hR.2, ⟨h, hgap, hok⟩⟩
  obtain ⟨hmul, hone, hun, hsm, hTK, hTKs, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hwT := hKT w hwK
  have hw := hTK w hwT
  have hΦ := fun v hv => (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε mu R hR Wp B hB.1 hB.2.1 hB.2.2.2 v hv).1
  have hS' := hS
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hWh, hNh, hGh, hq⟩ := hS'
  have := hWh.1; have := hNh.1; have := hGh.1
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_id
  have hSeq : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN = (μW.prod μN).map (fun p => mulMt p.1 p.2) := rfl
  have hsf : SFinite (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by rw [hSeq]; infer_instance
  have hGm : MeasurableSet {y : Mt k r | Matrix.of y ∈ GG k r} := (isClosed_UH.preimage hof).measurableSet
  have hSae : ∀ᵐ s ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN), Matrix.of s ∈ GG k r := by
    rw [hSeq]
    refine (ae_map_iff measurable_mulMt.aemeasurable hGm).2 ?_
    filter_upwards [hPae] with p hp
    exact Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hS0 : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN ≠ 0 := GlobalTheory.SideCompare.muS_ne_zero hWh.2.1 hNh.2.1
  have hνae := GlobalTheory.BesselNorm.quot_ae hq hGae hSae hS0
  have hνs : SigmaFinite νq := GlobalTheory.SideCompare.sigmaFinite_of_isQuotMeas hS0 hq
  have hSC : SecondCountableTopology Wp := by
    have := FiniteDimensional.proper ℂ Wp
    infer_instance
  have one_mem : (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) ∈ GG k r := by
    show (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp
  have memDD : ∀ g ∈ GG k r, R.σ g w ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have wDD : w ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w := by
    have := memDD 1 one_mem; rwa [hone] at this
  have DDsm : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, v ∈ R.sm := by
    intro v hv
    refine hTK v (Submodule.span_le.2 ?_ hv)
    rintro _ ⟨g, hg, rfl⟩
    exact hTKs g hg w hwT
  have hnorm : ∀ g ∈ GG k r, ‖R.σ g w‖ = ‖w‖ := fun g hg => (sigma_facts hR.2).2 g hg w
  have hcw : c * ‖w‖ ^ 2 ≠ 0 := by
    intro h1; apply h0; rw [hiso w wDD, h1, ENNReal.ofReal_zero]
  have hmeas : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      AEStronglyMeasurable (fun y : Mt k r => B (R.σ (Matrix.of y) v)) νq := fun v hv =>
    aesm_of_contOn ((hΦ v (DDsm v hv)).comp hof.continuousOn fun y hy => hy) hGm hνae
  have hsq : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      Integrable (fun y : Mt k r => ‖B (R.σ (Matrix.of y) v)‖ ^ 2) νq ∧
        ∫ y : Mt k r, ‖B (R.σ (Matrix.of y) v)‖ ^ 2 ∂νq = c * ‖v‖ ^ 2 := fun v hv =>
    sq_int (hmeas v hv) (by positivity) (hiso v hv)

  have hpair : ∀ a ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, ∀ b ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      Integrable (fun y : Mt k r => ⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ) νq ∧
      ∫ y : Mt k r, ‖⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ‖ ∂νq ≤ c * ‖a‖ ^ 2 + c * ‖b‖ ^ 2 ∧
      (∫ y : Mt k r, ⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ ∂νq).re = c * (⟪a, b⟫_ℂ).re := by
    intro a ha b hb
    obtain ⟨i1, i2, i3⟩ := inner_int (hmeas a ha) (hmeas b hb) (hsq a ha).1 (hsq b hb).1
    have e : ∫ y : Mt k r, ‖B (R.σ (Matrix.of y) a) + B (R.σ (Matrix.of y) b)‖ ^ 2 ∂νq = c * ‖a + b‖ ^ 2 := by
      rw [← (hsq (a + b) (Submodule.add_mem _ ha hb)).2]
      apply integral_congr_ae
      filter_upwards [hνae] with y hy
      rw [map_add (f := _), hB.1 _ (hsm _ hy a (DDsm a ha)) _ (hsm _ hy b (DDsm b hb))]
    rw [(hsq a ha).2, (hsq b hb).2] at i2 i3
    rw [e, norm_add_sq (𝕜 := ℂ)] at i3
    refine ⟨i1, i2, ?_⟩
    simp only [RCLike.re_to_complex] at i3
    linarith

  set m : Mt k r → ℂ := fun g => ⟪w, R.σ (Matrix.of g) w⟫_ℂ with hm
  have hmc : ContinuousOn m {y : Mt k r | Matrix.of y ∈ GG k r} :=
    continuousOn_const.inner ((hcont w).comp hof.continuousOn fun y hy => hy)
  have hmi : Integrable m μG := by
    obtain ⟨C, Ws, -, hd⟩ := Gp91.GlobalTheory.BesselDecay.decay_TK hy.1 k r ε mu h R hRG hgap hok w hwT
    obtain ⟨-, -, t1, t2⟩ := GlobalTheory.thresholds_of_gapOK k r h hok
    have hg := GlobalTheory.gN_rpow_neg_integrable_haar k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hGh (by linarith)
    refine (hg.const_mul (C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum)).mono'
      (aesm_of_contOn hmc hGm hGae) ?_
    filter_upwards [hGae] with y hy
    rw [neg_sub]
    exact hd w hw _ hy

  set F : Mt k r × Mt k r → ℂ := fun q =>
    star (m q.1) * ⟪B (R.σ (Matrix.of q.2) w), B (R.σ (Matrix.of q.2 * Matrix.of q.1) w)⟫_ℂ with hF
  have hFm : AEStronglyMeasurable F (μG.prod νq) := by
    have c1 : Continuous (fun q : Mt k r × Mt k r => (Matrix.of q.1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_fst
    have c2 : Continuous (fun q : Mt k r × Mt k r => (Matrix.of q.2 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_snd
    refine aesm_of_contOn (s := {q : Mt k r × Mt k r | Matrix.of q.1 ∈ GG k r ∧ Matrix.of q.2 ∈ GG k r}) ?_
      ((isClosed_UH.preimage c1).inter (isClosed_UH.preimage c2)).measurableSet
      ((Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hνae))
    let hs : Set (Mt k r × Mt k r) := {q | Matrix.of q.1 ∈ GG k r ∧ Matrix.of q.2 ∈ GG k r}
    exact (continuous_star.comp_continuousOn (hmc.comp (s := hs) continuous_fst.continuousOn fun q hq => hq.1)).mul
      (((hΦ w hw).comp (s := hs) c2.continuousOn fun q hq => hq.2).inner
        ((hΦ w hw).comp (s := hs) (c2.matrix_mul c1).continuousOn fun q hq => Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hq.2 hq.1))
  have hF1 : ∀ g : Mt k r, Matrix.of g ∈ GG k r → (fun y => F (g, y)) =ᵐ[νq] fun y =>
      star (m g) * ⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ := by
    intro g hg
    filter_upwards [hνae] with y hy
    simp only [hF]
    rw [hmul _ hy _ hg]
  have hF2 : ∀ g : Mt k r, Matrix.of g ∈ GG k r → (fun y => F (g, y)) =ᵐ[νq] fun y =>
      ⟪B (R.σ (Matrix.of y) (m g • w)), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ := by
    intro g hg
    filter_upwards [hνae, hF1 g hg] with y hy h1
    rw [h1, map_smul, hB.2.1 _ _ (hsm _ hy w hw), inner_smul_left]
    rfl
  have hFi : Integrable F (μG.prod νq) := by
    rw [integrable_prod_iff hFm]
    constructor
    · filter_upwards [hGae] with g hg
      exact ((hpair w wDD _ (memDD _ hg)).1.const_mul _).congr (hF1 g hg).symm
    · refine (hmi.norm.mul_const (c * ‖w‖ ^ 2 + c * ‖w‖ ^ 2)).mono' hFm.norm.integral_prod_right' ?_
      filter_upwards [hGae] with g hg
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      have e : ∫ y, ‖F (g, y)‖ ∂νq = ‖m g‖ *
          ∫ y : Mt k r, ‖⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ‖ ∂νq := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hF1 g hg] with y hy
        rw [hy, norm_mul, norm_star]
      rw [e]
      have := (hpair w wDD _ (memDD _ hg)).2.1
      rw [hnorm _ hg] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

  have hzero : ∫ q, F q ∂(μG.prod νq) = 0 := by
    rw [integral_prod_symm F hFi]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hνae, hFi.prod_left_ae] with y hy hi
    set f : Mt k r → ℂ := fun g => star ⟪R.σ (Matrix.of y) w, R.σ (Matrix.of g) w⟫_ℂ *
      ⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of g) w)⟫_ℂ with hf
    have hfc : ContinuousOn f {y : Mt k r | Matrix.of y ∈ GG k r} :=
      (continuous_star.comp_continuousOn (continuousOn_const.inner
        ((hcont w).comp hof.continuousOn fun y hy => hy))).mul
        (continuousOn_const.inner ((hΦ w hw).comp hof.continuousOn fun y hy => hy))
    have hfm : AEStronglyMeasurable f (μG.map (lmulM (Matrix.of y))) := by
      rw [hGh.2.2.2 _ hy]; exact aesm_of_contOn hfc hGm hGae
    have hlm : Measurable (lmulM (k := k) (r := r) (Matrix.of y)) :=
      measurable_mulMt.comp (measurable_const.prodMk measurable_id : Measurable fun x : Mt k r => (y, x))
    have e : (fun g => F (g, y)) =ᵐ[μG] f ∘ lmulM (Matrix.of y) := by
      filter_upwards [hGae] with g hg
      show star ⟪w, R.σ (Matrix.of g) w⟫_ℂ * _ = star ⟪R.σ (Matrix.of y) w, R.σ (Matrix.of y * Matrix.of g) w⟫_ℂ * _
      rw [hmul _ hy _ hg w, hun _ hy, ← hmul _ hy _ hg w]
      rfl
    have hfi : Integrable f μG := by
      rw [← hGh.2.2.2 _ hy]
      exact (integrable_map_measure hfm hlm.aemeasurable).2 (hi.congr e)
    have e2 : ∫ g, F (g, y) ∂μG = ∫ g, f g ∂μG := by
      rw [integral_congr_ae e]
      conv_rhs => rw [← hGh.2.2.2 _ hy]
      exact (integral_map hlm.aemeasurable hfm).symm
    rw [e2]
    refine unfold_zero hK hR hS hB hw (fun x hx => ?_) _ hfi
    obtain ⟨j1, j2⟩ := hl.2 x hx _ (hTKs _ hy w hwT)
    refine ⟨j1, ?_⟩
    rw [j2, hcon x hx]
    ext ξ; simp

  obtain ⟨d, hd, hSch⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hy.1 k r ε μG hGh
  obtain ⟨s1, s2⟩ := (hSch mu R hRG).2 w w w w
  have hdpos : 0 < d * fdegHC mu := mul_pos hd (GlobalTheory.BesselNorm.fdegHC_pos mu hR.1.1.injective)
  have hre : (∫ q, F q ∂(μG.prod νq)).re = c * (∫ g, m g * star (m g) ∂μG).re := by
    rw [integral_prod F hFi]
    have a1 := integral_re hFi.integral_prod_left
    have a2 := integral_re s1
    simp only [RCLike.re_to_complex] at a1 a2
    rw [← a1, ← a2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hGae] with g hg
    rw [integral_congr_ae (hF2 g hg), (hpair _ (Submodule.smul_mem _ _ wDD) _ (memDD _ hg)).2.2, inner_smul_left,
      mul_comm ((starRingEnd ℂ) (m g))]
    rfl
  rw [hzero, s2, inner_self_eq_norm_sq_to_K] at hre
  have e3 : (((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / ((d * fdegHC mu : ℝ) : ℂ))).re =
      ‖w‖ ^ 2 * ‖w‖ ^ 2 / (d * fdegHC mu) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre' : 0 = c * (‖w‖ ^ 2 * ‖w‖ ^ 2 / (d * fdegHC mu)) := by rw [← e3]; exact hre
  have hw2 : ‖w‖ ^ 2 ≠ 0 := right_ne_zero_of_mul hcw
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcw
  exact mul_ne_zero hc0 (div_ne_zero (mul_ne_zero hw2 hw2) hdpos.ne') hre'.symm

theorem exists_kFin_period_ne_zero : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B l : R.H → Wp) (w : R.H), R.IsDS ε mu → GapAtLeast ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → SideG k r z π u μW μN μG νq → IsBes R z π B → R.KFin w → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0 → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → IsBeL R z π μW μN l → ∃ v, R.KFin v ∧ l v ≠ 0 := by
  intro hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq B l w hR hgap hok hS hB hwK h0 hfin hl
  have hK : PI.KFinSmooth := hy.1.1.2.2.1
  have hw : w ∈ R.sm := hK k r ε mu R.H R.σ hR.1 hR.2 w hwK
  obtain ⟨c, hc, hiso⟩ := GlobalTheory.T.exists_l2SG_translates_eq_const_mul_norm_sq k r ε mu R Wp z π u μW μN μG νq B w hR hS hB hw hfin
  exact GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r ε mu R hR Wp l hl.1.1 hl.1.2.1 hl.1.2.2.2
    (nzOn_of_mass hy hR hgap hok hS hB hwK hc hiso h0 hl)

end GlobalTheory.BesselPeriodNonzeroGap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B l : R.H → Wp) (w : R.H), R.IsDS ε mu → GapAtLeast ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → SideG k r z π u μW μN μG νq → IsBes R z π B → R.KFin w → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0 → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → IsBeL R z π μW μN l → ∃ v, R.KFin v ∧ l v ≠ 0 := by
  first | exact @GlobalTheory.BesselPeriodNonzeroGap.exists_kFin_period_ne_zero | exact GlobalTheory.BesselPeriodNonzeroGap.exists_kFin_period_ne_zero | (intros; apply GlobalTheory.BesselPeriodNonzeroGap.exists_kFin_period_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepChoiceConstantsCOfSiegelWeilAtInfinity
namespace GlobalTheory.St

theorem stepChoiceDataC_of_siegelWeil_inInfinity :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
    (∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word),
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.RealObj.InInfinityX X u u' 1) →
    Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC :=
  fun h hI => Formalism.L2.SG.Pf.choice_massData (GlobalTheory.St.swxs_of_siegelWeil h)
    Formalism.L2.SG.Pf.ProdConvCut2.prodConv_onTied hI

end GlobalTheory.St
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizes
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizes
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg.CritVand

theorem thrE_add_one_lt (R : Formalism.BasicNotions.Ranks) (h : 1801 ≤ R.r) :
    Formalism.MainNotions.GapDS.thrE (epsSH R) + 1 < 16 * (R.r : ℝ) ^ 19 := by
  have hd : ((2 * R.rS + R.k + 1 : ℕ) : ℝ) = R.r := by exact_mod_cast dimS_eq R
  have hx : (1801 : ℝ) ≤ R.r := by exact_mod_cast h
  have h1 := Formalism.MainNotions.GapDS.thrE_le (epsSH R) (by rw [hd]; linarith)
  rw [hd] at h1
  have h3 : (1 : ℝ) ≤ (R.r : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have h16 : (R.r : ℝ) ^ 3 ≤ (R.r : ℝ) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

theorem vv_eq_vand_of_sizes : ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl →
    Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
  refine ⟨29, fun D large₂ C' Cl Cg cb Cu cT CT hC' hCl hT hH _ τ => ?_⟩
  have hG := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hgap := Formalism.L2.SG.Pf.WuBL.gapAtLeast_of D.R (D.hc τ) (hG.2 τ)
  have hds := GlobalTheory.T.formalDegree_eq_harishChandra_of_gap D hT τ _ (Formalism.L2.Col.lamSH_isHCParam (D.hc τ)) hgap (thrE_add_one_lt D.R hG.1)
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hds, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq D.R]
  exact div_mul_cancel₀ _ hSF.ne'

end GlobalTheory.Core.Deg.CritVand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizesStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes : ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
  first | exact @GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes | exact GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes | (intros; apply GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumDegreeEqMulFormalDegreeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumDegreeEqMulFormalDegreeGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.GapDegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem deg_eq_mul_fdegH : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → (∃ h : ℝ, GapAtLeast (epsSH D.R) lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW
  have hμ : PI.BesselPeriodGGP.IsHaarOn (GG D.R.k D.R.rS) W.μG := hW.2.2.2.2.2.2.1
  by_cases hQ : ∃ Q, IsCayley D.R.k D.R.rS (epsSH D.R) Q
  swap
  · refine ⟨1, one_pos, fun lam A hA _ => absurd ?_ hQ⟩
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  obtain ⟨a, ha0, hat, ha⟩ := GlobalTheory.BesselDegree.haar_eq_smul hQd hQ.2 W.μG hμ
  set s : ℝ≥0∞ := ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ≥0∞) with hs
  have hs0 : s ≠ 0 := ENNReal.coe_ne_zero.2 (D.s.cdScale_pos _ _).ne'
  have hst : s ≠ ∞ := ENNReal.coe_ne_top
  have hb0 : a / s ≠ 0 := (ENNReal.div_pos ha0 hst).ne'
  have hbt : a / s ≠ ∞ := (ENNReal.div_lt_top hat hs0).ne
  have hκ : 0 < (a / s).toReal := ENNReal.toReal_pos hb0 hbt
  refine ⟨(a / s).toReal, hκ, fun lam A hA _ v hv => ?_⟩
  obtain ⟨P, hP, hd, hS⟩ := hA.2.2.2.2.2.2.2.2.2.2
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hme : MeasurableEmbedding (phi (epsSH D.R) P) :=
    (phi_closedEmbedding (ε := epsSH D.R) Formalism.REAL.isClosedEmbeddingMatrix hPd).measurableEmbedding
  have hb : W.μG = (a / s) • (s • Formalism.REAL.muG (epsSH D.R)).map (phi (epsSH D.R) P) := by
    rw [Measure.map_smul, smul_smul, ENNReal.div_mul_cancel hs0 hst, GlobalTheory.DegreeTie.map_phi_eq hP hQ]
    · exact ha
    · exact hme.measurable.aemeasurable
  have hf : PI.BesselPeriodGGP.fdegH W.μG A.σ v = A.deg / (a / s).toReal := by
    refine Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq (div_pos hd hκ) (fun v w v' w' => ?_) hv
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [hb]
    constructor
    · refine Integrable.smul_measure ?_ hbt
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, A.σ (Matrix.of (phi (epsSH D.R) P g)) v⟫_ℂ *
          star ⟪w', A.σ (Matrix.of (phi (epsSH D.R) P g)) v'⟫_ℂ
          ∂(s • Formalism.REAL.muG (epsSH D.R)) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((A.deg : ℝ) : ℂ) := h2
      rw [h3, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  refine ⟨?_, hd⟩
  rw [hf]
  field_simp

end GlobalTheory.GapDegreeTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumDegreeEqMulFormalDegreeGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumDegree_eq_mul_formalDegree_gap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → (∃ h : ℝ, GapAtLeast (epsSH D.R) lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  first | exact @GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH | exact GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH | (intros; apply GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGap
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpOrbGap

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt

theorem ampKF : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 := by
  intro hH k r L h μG w l l' hOne γ μR νR ν hD b hb0 hb hint v v' hv hv' ξ ξ'
  have H := hH.1
  obtain ⟨⟨hgap, hok, -, hw, hμ, -, -⟩, hl, hl'⟩ := hOne
  obtain ⟨hγ, -, -, hrel, hR, hQ, hQG⟩ := hD
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  let R : Rep k r := ⟨L.Hs, L.σ⟩
  have hDS : R.IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  obtain ⟨hmul, hone, huni, -⟩ := GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r L.ε L.lam R hDS
  have hsm := H.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ w (PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw)
  obtain ⟨C, Ws, -, hC⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  obtain ⟨C', Ws', -, hC'⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v' hv'
  have hw1 : ‖w‖ = 1 := hw.choose_spec.2.1
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨c, -, hc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg H k r L.ε μG hμ
  have hDG : R.IsDG L.ε L.lam := ⟨L.hlam, hσ, h, hgap, hok⟩
  obtain ⟨hd, hS⟩ := hc L.lam R hDG
  have hd' : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw0
  have hS' : ∀ y y' : L.Hs, ∫ x, ⟪y, L.σ (Matrix.of x) w⟫_ℂ * star ⟪y', L.σ (Matrix.of x) w⟫_ℂ ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ * ⟪y, y'⟫_ℂ := fun y y' => by
    refine (hS w y w y').2.trans ?_
    have : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
    rw [hd']
    show ⟪w, w⟫_ℂ * ⟪y, y'⟫_ℂ / _ = _
    rw [this, one_mul, div_eq_inv_mul]
  haveI : SigmaFinite μG := hμ.1
  haveI : SigmaFinite μR := hR.1
  haveI : SFinite (pairMeas L) := by
    have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
    have : SigmaFinite L.μW := L.hμW.1.1
    have : SigmaFinite L.μW' := L.hμW'.1.1
    unfold pairMeas; infer_instance
  have aG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.2.2.1
  have aR : ∀ᵐ y ∂μR, Matrix.of y ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
  have aν := ae_quot L hR hQ
  haveI : SFinite ν := sfinite_of_lintegral ν (fun p => ‖pairMaj γ b p‖ₑ) hint.1.enorm
    (aν.mono fun p hp => by
      have : 0 < pairMaj γ b p :=
        Real.rpow_pos_of_pos (one_pos.trans_le (PI.PolynomialProperness.GN.gN_ge_one (point_mem L hγ hp))) _
      simpa using this.ne') hint.2.ne
  have hRc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (hG.unit _ hγ)
  have hinv : μR.map GlobalTheory.SgInf.invM = μR :=
    (GlobalTheory.UnipUnimod.isUnimod_of_subset_Nset (S := RStab k r γ)
      ⟨fun a ha => ha.1.1, hRc.closed, hRc.one_mem, hRc.mul_mem, hRc.inv_mem⟩ (fun a ha => ha.1) hR).2
  have mi : Measurable (GlobalTheory.SgInf.invM (k := k) (r := r)) := Formalism.FourierDecayAlt.P.B7.measurable_invM
  let cj : Mt k r → Mt k r := fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j
  have mc : Measurable cj :=
    meas_mul (g := fun _ => γ) (meas_mul (f := fun _ => (γ⁻¹ : MatKR k r)) measurable_const measurable_id)
      measurable_const
  let a₂ : Mt k r → Mt k r → Mt k r := fun a x => Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x)
  have m2 : Measurable fun q : Mt k r × Mt k r => a₂ q.2 q.1 :=
    meas_mul (mc.comp (mi.comp measurable_snd)) measurable_fst
  have hW2 : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ a, f (a₂ a x) ∂μR) ∂νR := by
    intro f hf
    rw [hQG f hf]
    refine lintegral_congr fun x => ?_
    have mf : Measurable fun s : Mt k r => f fun i j => (Matrix.of s * Matrix.of x) i j :=
      hf.comp (meas_mul measurable_id measurable_const)
    rw [lintegral_map mf mc]
    conv_lhs => rw [← hinv]
    rw [lintegral_map (f := fun s => f fun i j => (Matrix.of (cj s) * Matrix.of x) i j) (mf.comp mc) mi]
    rfl
  haveI : SFinite νR := sfinite_of_weil μG νR μR hR.2.1 a₂ m2 hW2
  have m1 : Measurable fun q : PairSp k r × Mt k r => stabAct γ (Matrix.of q.2) q.1 :=
    (measurable_fst.fst.fst.prodMk (meas_mul measurable_snd measurable_fst.fst.snd)).prodMk
      (measurable_fst.snd.fst.prodMk (meas_mul (mc.comp measurable_snd) measurable_fst.snd.snd))
  have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := hG.closed
  have aνR : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
    refine ae_of_weil μG νR μR a₂ _ hcl.measurableSet aG hR.2.1 hW2 ?_
    filter_upwards [aR] with a ha x hx
    have h1 := hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hγ) _ (hG.inv_mem _ ha.1.1)) _ hγ
    have h3 : γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x ∈ UH (Hpk k r) := hx
    have h2 := hG.mul_mem _ (hG.inv_mem _ h1) _ h3
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hG.unit _ h1)] at h2
    exact h2
  have hI := integrable_ker L hγ w v v' ξ ξ' hμ aν (e := Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hb0 (by linarith) hint
    (fun x hx => by rw [neg_sub]; exact hC w hsm x hx) (fun x hx => by rw [neg_sub]; exact hC' w hsm x hx)
  have key := double_weil (pairMeas L) ν μG νR μR (fun a p => stabAct γ (Matrix.of a) p) a₂
    (mp_of_weil _ _ _ (fun a p => stabAct γ (Matrix.of a) p) m1 hQ) (mp_of_weil _ _ _ a₂ m2 hW2)
    (ker L γ w v v' ξ ξ') (aesm_ker L hγ w v v' ξ ξ' _ _ (ae_pairMeas L) aνR) hI (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((Measure.quasiMeasurePreserving_fst.ae aν).and
        (Measure.quasiMeasurePreserving_snd.ae aR))] with t ht
      exact ker_act L hγ hrel w v v' ξ ξ' ht.2 ht.1 t.2)
  unfold ampJ OrbInt
  rw [Complex.ofReal_one, inv_one, one_smul, ← integral_smul, ← integral_smul]
  refine Eq.trans (integral_congr_ae ?_) (key.trans (integral_congr_ae ?_))
  · filter_upwards [aνR] with x hx
    rw [integral_ker_pair L hok.1 hγ hmul w v v' ξ ξ' hx,
      hl _ (Submodule.subset_span ⟨_, hG.mul_mem _ hγ _ hx, rfl⟩) v hv,
      hl' _ (Submodule.subset_span ⟨_, hx, rfl⟩) v' hv']
    ext η
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inner_smul_left, inner_conj_symm]
    congr 1
    ring
  · filter_upwards [aν] with p hp
    exact integral_ker_group L hγ hmul hone huni aG hS' v v' ξ ξ' hp

end GlobalTheory.AmpOrbGap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGapStatement
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 := by
  first | exact @GlobalTheory.AmpOrbGap.ampKF | exact GlobalTheory.AmpOrbGap.ampKF | (intros; apply GlobalTheory.AmpOrbGap.ampKF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermsSameInnerLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermsSameInnerLattices
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.lat_gmap {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T}
    {F0' : LFlag (D.sp.Y 0) D.R.rS T'} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G)
    (σ τ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    c.lat σ (Formalism.HermitianLatticesTheory.gmap τ Λ) = c.lat (σ * τ) Λ := by
  unfold GCoord.lat Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem GFrames.datOf_N_fst (G : GFrames A r k) {g : G.GLV} (hg : g ∈ G.N) (Γ : G.Lt) (p) :
    (G.datOf (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) p).1 = (G.datOf Γ p).1 := by
  have hloc : ∀ q, ∃ g' ∈ (G.S q).N, A.Ext q g g' := hg
  obtain ⟨g', hgN, hext⟩ := hloc p
  unfold Places.Ext at hext
  have := (A.loc p).lf
  have := (A.loc p).char0
  have hmove : g' • A.lat p Γ = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    unfold Places.lat
    rw [Submodule.smul_span, Submodule.map_coe, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    apply congrArg (fun f => f '' (Γ : Set G.V))
    funext x
    simp [hext]
  unfold GFrames.datOf
  rw [← hmove]
  exact (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries (A.L p) r k (G.S p)).2.2.1 g' hgN (A.lat p Γ)

theorem GFrames.datOf_N'_snd (G : GFrames A r k) {g : G.GLV} (hg : g ∈ G.N') (Γ : G.Lt) (p) :
    (G.datOf (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) p).2.1 = (G.datOf Γ p).2.1 := by
  have hloc : ∀ q, ∃ g' ∈ (G.S q).N', A.Ext q g g' := hg
  obtain ⟨g', hgN, hext⟩ := hloc p
  unfold Places.Ext at hext
  have := (A.loc p).lf
  have := (A.loc p).char0
  have hmove : g' • A.lat p Γ = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    unfold Places.lat
    rw [Submodule.smul_span, Submodule.map_coe, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    apply congrArg (fun f => f '' (Γ : Set G.V))
    funext x
    simp [hext]
  unfold GFrames.datOf
  rw [← hmove]
  exact (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries (A.L p) r k (G.S p)).2.2.2.1 g' hgN (A.lat p Γ)
end Loc

theorem datOf_dcoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).1 = (G.datOf (c.lat ρ t₀.lam) p).1 ∧ (G.datOf (c.lat (ρ * n) t.lam) p).2.1 = (G.datOf (c.lat ρ t₀.lam) p).2.1 := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hB G c t₀ ρ U U' hmv t n m hlam hlam' hnm p
  obtain ⟨hn, hm, hlin⟩ := hnm
  obtain ⟨P1, P2, P3, -⟩ := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hB G c t₀ ρ U U' hmv

  have hrel : ∀ s : TauC Y u u', Formalism.HermitianLatticesTheory.gmap (GTerm.lin s) s.lam' = s.lam :=
    fun s => (Quot.out s.cls).property.2.2.1
  constructor
  · rw [P3, hlam]
    exact GFrames.datOf_N_fst G ((P1 n).1 hn) _ p
  · have e1 : c.lat (ρ * n) t.lam = (c.lat (ρ * GTerm.lin t₀) t₀.lam').map
        (((c.grp (ρ * GTerm.lin t₀) m : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) := by
      rw [← P3, ← hrel t, GCoord.lat_gmap, hlin, hlam']
      congr 1
      group
    have e2 : c.lat (ρ * GTerm.lin t₀) t₀.lam' = c.lat ρ t₀.lam := by
      rw [← GCoord.lat_gmap, hrel t₀]
    rw [e1, ← e2]
    exact GFrames.datOf_N'_snd G ((P2 m).1 hm) _ p

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermsSameInnerLatticesStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_terms_same_innerLattices : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).1 = (G.datOf (c.lat ρ t₀.lam) p).1 ∧ (G.datOf (c.lat (ρ * n) t.lam) p).2.1 = (G.datOf (c.lat ρ t₀.lam) p).2.1 := by
  first | exact @GlobalTheory.HL.datOf_dcoset | exact GlobalTheory.HL.datOf_dcoset | (intros; apply GlobalTheory.HL.datOf_dcoset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEq
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.DatEq

theorem row_eq_iff_datOf_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ↔ G.datOf (c.lat (ρ * n) t.lam) = G.datOf (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hA := GlobalTheory.T.doubleCoset_terms_same_innerLattices D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hI := GlobalTheory.T.identificationCompat_iff_localGraphs D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hD := Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t₀ t hl.symm hl'.symm
  have hrow : ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) ↔
      iotaOf Y.TR (Y.cs u) (Y.cs u') t₀ = iotaOf Y.TR (Y.cs u) (Y.cs u') t := by
    show ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t) : Rw _ _ Y.TR) =
        (⟨t₀.lam, t₀.mem⟩, ⟨t₀.lam', t₀.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t₀) ↔ _
    constructor
    · intro h
      exact (congrArg (fun r => r.2.2) h).symm
    · intro h
      rw [h]
      ext <;> simp [hl, hl']
  rw [hrow, hD, hI]
  constructor
  · intro h
    funext p
    exact Prod.ext (hA p).1 (Prod.ext (hA p).2 (h p))
  · intro h p
    exact congrArg (fun d => (d p).2.2) h

end GlobalTheory.HL.DatEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEqStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ↔ G.datOf (c.lat (ρ * n) t.lam) = G.datOf (c.lat ρ t₀.lam)) := by
  first | exact @GlobalTheory.HL.DatEq.row_eq_iff_datOf_eq | exact GlobalTheory.HL.DatEq.row_eq_iff_datOf_eq | (intros; apply GlobalTheory.HL.DatEq.row_eq_iff_datOf_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PgFrameAtRecord
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem pgFrame_at_record : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → Formalism.L2.SG.RowsConc.TFrameAt D ∧ UnitaryVolumeMass.cTvA D ∧ UnitaryVolumeMass.cTvD D 1 ∧ ∀ w τ, (D.R.k : ℝ) ^ (3 * D.R.rS) ≤ gg D ^ (-(D.R.m : ℝ)) * Tcrit D w τ := by
  intro hSM hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT h h40 hCu hk hR
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hyp : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT := ⟨h.2.1, h.1, h.2.2⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hg : LocalBesselAndTopKernel.MidVolumeChain D large₂ (1 / 3) 0 :=
    Formalism.L2.SG.Pf.SzHypFam.midVolumeChain_of_standingHypotheses hT h.1 (by nlinarith) (by norm_num) le_rfl
  have hD : UnitaryVolumeMass.cTvD D 1 :=
    Formalism.MainNotions.BridgeLemma.critical_level_lower_bound (C3' := 1) h40 (by norm_num) le_rfl hyp hg
  have hA : UnitaryVolumeMass.cTvA D :=
    Formalism.MainNotions.BridgeLemma.degree_ratio_formula_statement D large₂ C0 C' Cl Cg cb Cu cT CT
      (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hSM D) (Formalism.MainNotions.BridgeLemma.mass_two_bound_single_holds D) hR hyp
  have F := Formalism.MainNotions.BridgeLemma.tfFacts_of h
  have hm : 2 * (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; norm_num; exact_mod_cast this
  exact ⟨fun w => F.tframe (by linarith) hm hCu hA hD hk w, hA, hD,
    fun w τ => F.tcritLow (by linarith) hm hCu hD w τ⟩

end GlobalTheory
end
