module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairSpaceMajorantIntegrableBigCell
public import CompanionTheory.AutomorphicTheory.RankOneTori.MatGroupOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellTrivialStabiliserAndMeasures
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellTrivialStabiliserAndMeasures
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.AmpTK

theorem bigCell_data : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ Formalism.MainNotions.S.IsRelStab L (Formalism.QuantumDeterminants.bigCell k r c μ) ∧ IsHaarOn (Formalism.MainNotions.S.RStab k r (Formalism.QuantumDeterminants.bigCell k r c μ)) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) ∧ Formalism.MainNotions.S.IsOrbQuot L (Formalism.QuantumDeterminants.bigCell k r c μ) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) (Formalism.MainNotions.S.pairMeas L) ∧ PI.BesselPeriodGGP.IsQuotMeas μG ((MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)).map (fun x => fun i j => ((Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ * Matrix.of x * Formalism.QuantumDeterminants.bigCell k r c μ) i j)) μG := by
  intro k r L μG hk hκt hκ hc hG c μ hca hμ
  have hg : bigCell k r c μ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.bigCellMem k r c μ hca hμ
  have hinv : (bigCell k r c μ)⁻¹ * bigCell k r c μ = 1 :=
    Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg)
  have hR := GlobalTheory.AmpNorm.rStab_bigCell c μ hca hg
  set g := bigCell k r c μ
  have h1 : (Matrix.of fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) = 1 := rfl
  refine ⟨hg, ?_, ⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    rw [ha, mul_one, hinv]
    unfold psi
    rw [Model.ell_one k r L.z L.hz.1, Model.ell_one k r L.z' L.hz'.1]
  · exact IsProbabilityMeasure.ne_zero _
  · rw [Measure.dirac_apply]
    have : (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) ∉
        {x : Mt k r | Matrix.of x ∉ RStab k r g} := by
      intro h
      apply h
      rw [h1, hR]; rfl
    simp [Set.indicator_of_notMem this]
  · intro s hs
    rw [hR, Set.mem_singleton_iff] at hs
    subst hs
    have : (lmulM (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Mt k r → Mt k r) = id := by
      funext x; simp [lmulM]; rfl
    rw [this, Measure.map_id]
  · intro f hf
    have e : ∀ x : PairSp k r,
        (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂(Measure.dirac
          (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j))) = f x := by
      intro x
      rw [lintegral_dirac, h1]
      have : stabAct g 1 x = x := by
        unfold stabAct
        rw [mul_one, hinv]
        simp only [one_mul]
        rfl
      rw [this]
    simp_rw [e]
  · intro f hf
    rw [Measure.map_dirac, h1, mul_one, hinv]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, h1, one_mul]
    rfl

end GlobalTheory.AmpTK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellTrivialStabiliserAndMeasuresStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCell_trivialStabiliser_and_measures : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ Formalism.MainNotions.S.IsRelStab L (Formalism.QuantumDeterminants.bigCell k r c μ) ∧ IsHaarOn (Formalism.MainNotions.S.RStab k r (Formalism.QuantumDeterminants.bigCell k r c μ)) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) ∧ Formalism.MainNotions.S.IsOrbQuot L (Formalism.QuantumDeterminants.bigCell k r c μ) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) (Formalism.MainNotions.S.pairMeas L) ∧ PI.BesselPeriodGGP.IsQuotMeas μG ((MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)).map (fun x => fun i j => ((Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ * Matrix.of x * Formalism.QuantumDeterminants.bigCell k r c μ) i j)) μG := by
  first | exact @GlobalTheory.AmpTK.bigCell_data | exact GlobalTheory.AmpTK.bigCell_data | (intros; apply GlobalTheory.AmpTK.bigCell_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorant
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.CellPts

theorem cell_points : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), Formalism.MainNotions.S.ThB.Gpt (Formalism.QuantumDeterminants.Tz k r L.z) (Formalism.QuantumDeterminants.Tz k r L.z') γ ≠ 0 → Formalism.MainNotions.S.IsPtRep L γ g → Formalism.MainNotions.S.IsRelStab L g → Formalism.MainNotions.S.IsRootMeas L γ g μR → Formalism.MainNotions.S.IsOrbQuot L g μR ν → IsHaarOn (Formalism.MainNotions.S.RStab k r g) μR ∧ (∃ νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (g⁻¹ * Matrix.of x * g) i j)) νR) ∧ ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj g b) ν := by
  intro k r L h μG hO hC h1 h0 hc hμG γ g μR ν hG hrep hrel hroot hq
  have hR := Formalism.MainStatements.RankOne.root_haar hO.1 L hc hrep hroot
  have hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' g) :=
    ⟨Formalism.MainNotions.BigCellDensity.wPt γ, Formalism.MainNotions.BigCellDensity.dPt γ, Formalism.MainNotions.BigCellDensity.dPt_ne γ, by
      rw [hrep.2, ← Formalism.MainNotions.BigCellDensity.ptMatN_swap, Formalism.MainNotions.BigCellDensity.ptMatN_mono]⟩
  have hpos : 0 < Gf k r L.z L.z' g := by
    refine lt_of_le_of_ne (gNonneg k r L.z L.z' L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 g hrep.1) fun e => hG ?_
    rw [← Formalism.MainNotions.BigCellDensity.gTie k r L.z L.z' γ g hrep.1 hrep.2, ← e]
  obtain ⟨νR, hν⟩ := Formalism.MainStatements.RankOne.quot_exists hrep.1 hμG hR
  refine ⟨hR, ⟨νR, hν⟩, ?_⟩
  exact GlobalTheory.CellMaj.cellConv k r L h μG g μR νR ν h1 hO hC ⟨hrep.1, hpos, hmono, hrel, hR, hq, hν⟩ hmono

end GlobalTheory.CellPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorantStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallCell_relevant_points_haar_quotient_majorant : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), Formalism.MainNotions.S.ThB.Gpt (Formalism.QuantumDeterminants.Tz k r L.z) (Formalism.QuantumDeterminants.Tz k r L.z') γ ≠ 0 → Formalism.MainNotions.S.IsPtRep L γ g → Formalism.MainNotions.S.IsRelStab L g → Formalism.MainNotions.S.IsRootMeas L γ g μR → Formalism.MainNotions.S.IsOrbQuot L g μR ν → IsHaarOn (Formalism.MainNotions.S.RStab k r g) μR ∧ (∃ νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (g⁻¹ * Matrix.of x * g) i j)) νR) ∧ ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj g b) ν := by
  first | exact @GlobalTheory.CellPts.cell_points | exact GlobalTheory.CellPts.cell_points | (intros; apply GlobalTheory.CellPts.cell_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstant
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapConstant

set_option maxHeartbeats 2000000 in
theorem gap_thresholds (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
              (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
      GlobalTheory.CellAmp.GapCell k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have h3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  have hNdef : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hs, h3]
  set P : ℝ := (r : ℝ) + 1 with hPdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNd
  have hP1 : 1 ≤ P := by linarith
  have hN2 : 2 * P ≤ N := by rw [hNdef]; linarith
  have hN1 : 1 ≤ N := by linarith
  have h2P : 0 < 2 * P := by linarith
  have hsq : 0 < Real.sqrt (2 * P) := Real.sqrt_pos.mpr h2P
  have hsq1 : 1 ≤ Real.sqrt (2 * P) := Real.one_le_sqrt.mpr (by linarith)
  have hrp : (2 * P) ^ ((9 : ℝ) / 2) = (2 * P) ^ 4 * Real.sqrt (2 * P) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add h2P]
    norm_num
  rw [hrp]
  set X : ℝ := 3 * P * N ^ 2 + N ^ 3 with hX
  have ha : Formalism.FourierDecayAlt.ThreeDimData.aOf r (1000 * ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X) = 2000 * P ^ 4 * X := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [← hPdef]
    field_simp
    ring

  have hAS : Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * P * N ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
    have e : ((2 * r + k : ℕ) : ℝ) = 2 * (r : ℝ) + k := by push_cast; ring
    rw [e]
    have hd0 : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 := by nlinarith
    have hd : (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 ≤ 2 * P * N := by
      rw [hNdef]; nlinarith
    have hm : 2 * (r : ℝ) + k ≤ N := by rw [hNdef]; linarith
    calc (2 * (r : ℝ) + k) * ((r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2)
        ≤ N * (2 * P * N) := mul_le_mul hm hd hd0 (by linarith)
      _ = 2 * P * N ^ 2 := by ring
  have hAS0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
    apply mul_nonneg (Nat.cast_nonneg _); nlinarith
  have hAG : Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * N * P := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have : (k : ℝ) + r ≤ N := by rw [hNdef]; linarith
    nlinarith
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hM : Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ 2 * P ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; rw [hPdef]; nlinarith
  have hM0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r := by unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity

  have hP35 : P ^ 3 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP15 : P ≤ P ^ 5 := by simpa using pow_le_pow_right₀ hP1 (show 1 ≤ 5 by norm_num)
  have hP25 : P ^ 2 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP5 : 1 ≤ P ^ 5 := one_le_pow₀ hP1
  have hN12 : N ≤ N ^ 2 := by nlinarith
  have hN21 : 1 ≤ N ^ 2 := by nlinarith
  have hN2_0 : 0 ≤ N ^ 2 := by positivity
  have hP50 : 0 ≤ P ^ 5 := by positivity
  have hbig : 6000 * P ^ 5 * N ^ 2 ≤ 2000 * P ^ 4 * X := by
    rw [hX]
    have : 0 ≤ P ^ 4 * N ^ 3 := by positivity
    nlinarith
  have m1 : P ^ 3 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP35 hN2_0
  have m2 : P ^ 3 * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP35 hN12 (by positivity) hP50
  have m3 : P * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP15 hN12 (by positivity) hP50
  have m4 : (1 : ℝ) ≤ P ^ 5 * N ^ 2 := one_le_mul_of_one_le_of_one_le hP5 hN21
  have m5 : P * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP15 hN2_0
  have m6 : P ^ 2 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP25 hN2_0
  have hprod : Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul hM (show Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 2 * P * N ^ 2 + 4 * N * P by linarith)
      (add_nonneg hAS0 hAG0) (by nlinarith)
  have hprod2 : ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsqN : 0 ≤ (2 * P) ^ 4 * Real.sqrt (2 * P) - 1 := by
    have : 1 ≤ (2 * P) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  refine ⟨⟨hk, ?_, ?_, ?_⟩, ?_⟩
  · have hX3 : N ^ 3 ≤ X := by rw [hX]; nlinarith
    have hN3 : 0 ≤ N ^ 3 := by positivity
    have : X ≤ ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X := by nlinarith
    nlinarith
  · rw [ha]
    have e : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) =
      2 * (Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)) := by ring
    rw [e]
    have : (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) = 4 * (P ^ 3 * N ^ 2) + 8 * (P ^ 3 * N) := by ring
    nlinarith
  · rw [ha]
    have e : (9 : ℝ) * ((r : ℝ) + 1) * N ^ 2 = 9 * (P * N ^ 2) := by rw [← hPdef]; ring
    rw [e]
    nlinarith
  · unfold GlobalTheory.CellAmp.GapCell
    rw [ha]
    have e : 10 * ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) =
      10 * (((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)) := by ring
    rw [e]
    have : P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) = 2 * (P ^ 3 * N ^ 2) + 4 * (P ^ 3 * N) := by ring
    nlinarith

theorem gap_constant_exists : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  refine ⟨1000, fun D ε lam hg => ⟨_, hg, ?_⟩⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact gap_thresholds D.R.k D.R.rS hk

end GlobalTheory.GapConstant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstantStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_besselCell_gap_constant : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  first | exact @GlobalTheory.GapConstant.gap_constant_exists | exact GlobalTheory.GapConstant.gap_constant_exists | (intros; apply GlobalTheory.GapConstant.gap_constant_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselCoefficientNonzero
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKOne

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt GlobalTheory.AmpTK

variable {k r : ℕ}

theorem besselIntg_sum (L : LocBessel k r) {ι : Type} (s : Finset ι)
    (F : ι → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) :
    besselIntg L (fun q => ∑ a ∈ s, F a q) g p = ∑ a ∈ s, besselIntg L (F a) g p := by
  ext η
  set_option synthInstance.maxHeartbeats 100000 in
    simp [besselIntg, ContinuousLinearMap.sum_apply, map_sum, Finset.smul_sum]

end GlobalTheory.AmpTKOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapsLargeGapPeriodIdentities
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapsLargeGapPeriodIdentities
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKGap

variable {k r : ℕ}

theorem side_bessel (hH : GlobalTheory.GapIn.Hyp) (L : LocBessel k r) (h : ℝ) (hgap : GapAtLeast L.ε L.lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hc : L.c ≠ 0) (hκ0 : 0 < L.κN) (hκt : L.κN ≠ ⊤)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (u : Fin k → ℝ) (μW : Measure (Mt k r)) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hW : IsHaarOn (UWset k r z) μW) :
    ∃ l : L.Hs → Wp, (∀ x ∈ (GlobalTheory.AmpTK.rep L).sm, ∀ v ∈ (GlobalTheory.AmpTK.rep L).TK,
      Formalism.FourierDecayAlt.ThreeDimData.be z L.c π L.σ μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧ GlobalTheory.AmpTK.SmCW L l := by
  haveI := FiniteDimensional.complete ℂ Wp
  obtain ⟨μG, hG⟩ := GlobalTheory.SnMass.Inhab.exists_isHaarOn k r
  have hN := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN hκ0 hκt.lt_top
  obtain ⟨νq, hq⟩ := GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW L.μN μG hz hT hW hN hG
  obtain ⟨U, hS⟩ := GlobalTheory.AmpNormal.sideG_of hκt.lt_top hz hT hπ hW hG hq
  obtain ⟨t, ht, htN, htz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r L.c hc
  obtain ⟨-, htc, hψ⟩ := htz z hz
  have hR : Formalism.MainNotions.S.IsURepOn (GG k r) (GlobalTheory.AmpTK.rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  obtain ⟨hS', hB⟩ := GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π U L.c μW L.μN μG νq t ht htN htc hψ hS
  obtain ⟨-, hbe⟩ := hB (GlobalTheory.AmpTK.rep L) hR
  have hDG : (GlobalTheory.AmpTK.rep L).IsDG L.ε L.lam := ⟨L.hlam, L.hσ, h, hgap, hok⟩
  obtain ⟨l₁, hl₁⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r L.ε L.lam h (GlobalTheory.AmpTK.rep L) Wp z π U μW _ μG _ hDG hgap hok hS'
  have hti := GlobalTheory.BesselMove.inv_mem ht
  refine ⟨fun v => l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ v), fun x hx v hv => hbe l₁ hl₁ x hx v hv, ?_, ?_, ?_⟩
  · intro v hv w hw
    show l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ (v + w)) = _
    rw [map_add (f := _)]
    exact hl₁.1.1 _ (GlobalTheory.BesselMove.sig_sm hR hti hv) _ (GlobalTheory.BesselMove.sig_sm hR hti hw)
  · intro a v hv
    show l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ (a • v)) = _
    rw [map_smul]
    exact hl₁.1.2.1 _ _ (GlobalTheory.BesselMove.sig_sm hR hti hv)
  · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hti) hl₁.1.2.2.2

theorem exists_besselTK : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ),
    Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ →
    ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  intro hH k r L h hgap hok hc hκ0 hκt
  obtain ⟨l, hl, hsl⟩ := side_bessel hH L h hgap hok hc hκ0 hκt L.z L.π L.u L.μW L.hz.1 L.hz.2 L.hπ L.hμW.1
  obtain ⟨l', hl', hsl'⟩ := side_bessel hH L h hgap hok hc hκ0 hκt L.z' L.π' L.u' L.μW' L.hz'.1 L.hz'.2 L.hπ' L.hμW'.1
  exact ⟨l, l', ⟨hl, hl'⟩, hsl, hsl'⟩

end GlobalTheory.AmpTKGap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapsLargeGapPeriodIdentitiesStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_besselMaps_largeGap_periodIdentities : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ → ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  first | exact @GlobalTheory.AmpTKGap.exists_besselTK | exact GlobalTheory.AmpTKGap.exists_besselTK | (intros; apply GlobalTheory.AmpTKGap.exists_besselTK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIdentityTranslatesKFiniteLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIdentityTranslatesKFiniteLargeGap
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKOneGap

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt GlobalTheory.AmpTK

variable {k r : ℕ}

theorem fdeg_ne_zero (H : GlobalTheory.GapIn.Hyp) (L : LocBessel k r) (hDG : (rep L).IsDG L.ε L.lam) {μG : Measure (Mt k r)} (hμ : IsHaarOn (UH (Hpk k r)) μG)
    {w : L.Hs} (hw : w ≠ 0) : (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg H.1 k r L.ε μG hμ
  obtain ⟨hd, -⟩ := hc L.lam (rep L) hDG
  have e : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw
  rw [e]
  exact_mod_cast (mul_pos hc0 (GlobalTheory.BesselNorm.fdegHC_pos L.lam L.hlam.1.injective)).ne'

theorem ampTK_pt (H : GlobalTheory.GapIn.Hyp) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) (hgap : GapAtLeast L.ε L.lam h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hμ : IsHaarOn (UH (Hpk k r)) μG) (hBe : BeTK L l l') {w : L.Hs} (hw1 : ‖w‖ = 1)
    (hwK : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hR : IsHaarOn (RStab k r γ) μR)
    (hQ : IsOrbQuot L γ μR ν)
    (hQG : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b)
    (hint : Integrable (pairMaj γ b) ν) {v v' : L.Hs} (hv : v ∈ (rep L).TK) (hv' : v' ∈ (rep L).TK)
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν ∧
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  have hDG : (rep L).IsDG L.ε L.lam := ⟨L.hlam, hσ, h, hgap, hok⟩
  obtain ⟨hmul, hone, huni, hsmg, hTKsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS H.1.1.2.2.1 k r L.ε L.lam (rep L) hDS
  have hsm : w ∈ (rep L).sm := hTKsm w (hKT w hwK)
  obtain ⟨C, Ws, -, hC⟩ := Gp91.GlobalTheory.BesselDecay.decay_TK H.1 k r L.ε L.lam h (rep L) hDG hgap hok v hv
  obtain ⟨C', Ws', -, hC'⟩ := Gp91.GlobalTheory.BesselDecay.decay_TK H.1 k r L.ε L.lam h (rep L) hDG hgap hok v' hv'
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨c, -, hc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg H.1 k r L.ε μG hμ
  obtain ⟨hd, hS⟩ := hc L.lam (rep L) hDG
  have hd' : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw0
  have hS' : ∀ y y' : L.Hs, ∫ x, ⟪y, L.σ (Matrix.of x) w⟫_ℂ * star ⟪y', L.σ (Matrix.of x) w⟫_ℂ ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ * ⟪y, y'⟫_ℂ := fun y y' => by
    refine (hS w y w y').2.trans ?_
    have : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
    rw [hd']
    show ⟪w, w⟫_ℂ * ⟪y, y'⟫_ℂ / _ = _
    rw [this, one_mul, div_eq_inv_mul]
  have hfd := fdeg_ne_zero H L hDG hμ hw0
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
  have hgrp : ∀ᵐ p ∂ν, ∫ x, ker L γ w v v' ξ ξ' (p, x) ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ • besselIntg L (coefF L v v' ξ ξ') γ p := by
    filter_upwards [aν] with p hp
    exact integral_ker_group L hγ hmul hone huni aG hS' v v' ξ ξ' hp
  refine ⟨(hI.integral_prod_left.smul (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)).congr ?_, ?_⟩
  · filter_upwards [hgrp] with p hp
    rw [Pi.smul_apply, hp, smul_smul, mul_inv_cancel₀ hfd, one_smul]
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
      hBe.1 (L.σ (γ * Matrix.of x) w) (hsmg _ (hG.mul_mem _ hγ _ hx) w hsm) v hv,
      hBe.2 (L.σ (Matrix.of x) w) (hsmg _ hx w hsm) v' hv']
    ext η
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inner_smul_left, inner_conj_symm]
    congr 1
    ring
  · exact hgrp

theorem oneAt : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → GlobalTheory.AmpTK.BeTK L l l' → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → Formalism.MainNotions.S.IsRelStab L γ → IsHaarOn (Formalism.MainNotions.S.RStab k r γ) μR → Formalism.MainNotions.S.IsOrbQuot L γ μR ν → PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR → ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ b) ν → GlobalTheory.AmpTK.OneAt L l l' γ ν := by
  intro H k r L h μG l l' hgap hok _ hμ hBe γ μR νR ν hγ hrel hR hQ hQG b hb0 hb hint
  obtain ⟨-, -, -, -, -, -, -, ⟨w, hw1, hwK, -⟩, -⟩ :=
    GlobalTheory.rep_basic_of_isDS H.1.1.2.2.1 k r L.ε L.lam (rep L) ⟨L.hlam, L.hσ⟩
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  have hDG : (rep L).IsDG L.ε L.lam := ⟨L.hlam, L.hσ, h, hgap, hok⟩
  have hfd := fdeg_ne_zero H L hDG hμ hw0
  have key : ∀ {v v' : L.Hs}, v ∈ (rep L).TK → v' ∈ (rep L).TK → ∀ (ξ : L.Wp) (ξ' : L.Wq),
      Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν ∧
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν :=
    fun hv hv' ξ ξ' =>
      ampTK_pt H L h μG l l' hgap hok hμ hBe hw1 hwK γ μR νR ν hγ hrel hR hQ hQG b hb0 hb hint hv hv' ξ ξ'
  refine ⟨(PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) •
    ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ, ?_⟩
  rintro F s ⟨m, x, y, X, hxy, hF, rfl⟩
  have hc : ∀ i (ξ : L.Wp) (ξ' : L.Wq), OrbInt L (coefF L (x i) (y i) ξ ξ') γ ν =
      (⟪l (x i), ξ⟫_ℂ * ⟪ξ', l' (y i)⟫_ℂ) • (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) •
        ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ := by
    intro i ξ ξ'
    rw [smul_comm, (key (hxy i).1 (hxy i).2 ξ ξ').2, smul_smul, mul_inv_cancel₀ hfd, one_smul]
  let e := stdOrthonormalBasis ℂ L.Wq
  have hX : ∀ T : L.Wq →L[ℂ] L.Wp, T = ∑ j, (innerSL ℂ (e j)).smulRight (T (e j)) := by
    intro T
    ext η
    conv_lhs => rw [← e.sum_repr' η]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [ContinuousLinearMap.sum_apply, map_sum]
  have hFe : ∀ g ∈ UH (Hpk k r), F g = ∑ i, ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g := by
    intro g hg
    rw [hF g hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun j _ => coefF_eq L (x i) (y i) (X i (e j)) (e j) g, ← Finset.smul_sum]
    exact congrArg₂ (· • ·) rfl (hX (X i))
  have hae : ∀ᵐ p ∂ν, besselIntg L F γ p =
      ∑ i, ∑ j, besselIntg L (coefF L (x i) (y i) (X i (e j)) (e j)) γ p := by
    filter_upwards [ae_quot L hR hQ] with p hp
    have e1 : besselIntg L F γ p =
        besselIntg L (fun g => ∑ i, ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g) γ p := by
      unfold besselIntg
      rw [hFe _ (point_mem L hγ hp)]
    rw [e1]
    exact (GlobalTheory.AmpTKOne.besselIntg_sum L Finset.univ (fun i g => ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g) γ p).trans
      (Finset.sum_congr rfl fun i _ =>
        GlobalTheory.AmpTKOne.besselIntg_sum L Finset.univ (fun j g => coefF L (x i) (y i) (X i (e j)) (e j) g) γ p)
  have hi : ∀ i j, Integrable (besselIntg L (coefF L (x i) (y i) (X i (e j)) (e j)) γ) ν :=
    fun i j => (key (hxy i).1 (hxy i).2 _ _).1
  have e2 : OrbInt L F γ ν = ∑ i, ∑ j, OrbInt L (coefF L (x i) (y i) (X i (e j)) (e j)) γ ν := by
    unfold OrbInt
    rw [integral_congr_ae hae, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hi i j
  rw [e2, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hc]
  rw [← Finset.sum_smul]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← e.sum_repr' (l' (y i)), map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]

end GlobalTheory.AmpTKOneGap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIdentityTranslatesKFiniteLargeGapStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselAmplitude_identity_translates_kFinite_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → GlobalTheory.AmpTK.BeTK L l l' → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → Formalism.MainNotions.S.IsRelStab L γ → IsHaarOn (Formalism.MainNotions.S.RStab k r γ) μR → Formalism.MainNotions.S.IsOrbQuot L γ μR ν → PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR → ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ b) ν → GlobalTheory.AmpTK.OneAt L l l' γ ν := by
  first | exact @GlobalTheory.AmpTKOneGap.oneAt | exact GlobalTheory.AmpTKOneGap.oneAt | (intros; apply GlobalTheory.AmpTKOneGap.oneAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinCoefTorusNe
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapAmpTK

open GlobalTheory.AmpTK

private theorem exists_kFinCoef_torus_ne_of_kfin : PI.KFinSmooth → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro hK k r L l l' κ τ hκ hτ hl hl' hxe hye
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, L.hσ⟩
  obtain ⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩ :=
    GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v) := hmul0
  have hone : ∀ v : L.Hs, L.σ 1 v = v := hone0
  have hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := hinn0
  have hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  have hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ
  have hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ
  have hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v := by
    intro v
    rw [← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]
  have side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V),
      SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) →
      ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0 := by
    intro V _ _ _ m hm ⟨x, hxT, hx⟩
    haveI := FiniteDimensional.complete ℂ V
    refine GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V
      (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_
    · intro v hv w hw
      exact (congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans
        (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))
    · intro a v hv
      exact (congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))
    · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2
    · refine ⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩
      exact fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)
  obtain ⟨x₀, hx₀, hx₀'⟩ := side l hl hxe
  obtain ⟨y₀, hy₀, hy₀'⟩ := side l' hl' hye
  set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ
  set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'
  let P : L.Hs →L[ℂ] L.Wp := (innerSL ℂ x₀).smulRight ξ
  let Q : L.Wq →L[ℂ] L.Hs := (innerSL ℂ ξ').smulRight y₀
  let X : L.Wq →L[ℂ] L.Wp := (innerSL ℂ ξ').smulRight ξ
  have hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ := fun v => rfl
  have hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀ := fun w => rfl
  have hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ := fun w => rfl
  refine ⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩
  · intro w
    obtain ⟨S, hS, hyS, hSK⟩ := hy₀
    refine ⟨S, hS, ?_, hSK⟩
    rw [hQ]
    exact S.smul_mem _ hyS
  · intro v
    have hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀ := by
      apply ext_inner_right ℂ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    rw [hadj]
    obtain ⟨S, hS, hxS, hSK⟩ := hx₀
    exact ⟨S, hS, S.smul_mem _ hxS, hSK⟩
  · refine ⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀,
      fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩
    · intro g hg
      have key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) =
          (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ))) := by
        ext v
        show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _
        rw [hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]
        rfl
      have key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ =
          ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ := by
        intro u
        rw [← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]
      ext w
      simp only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX,
        map_smul, key2, inner_smul_right, smul_smul, mul_comm]
      exact congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)
    · simp only [Fin.sum_univ_one]
      rfl
  · rw [hX, inner_smul_right]
    exact mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')


theorem exists_kFinCoef_torus_ne : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H
  exact exists_kFinCoef_torus_ne_of_kfin H.1.1.2.2.1
end GlobalTheory.GapAmpTK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGap
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.AmpTKGap

theorem isCoef_kfin_and_torus_translate : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  intro H k r L l l' κ τ hκ hτ f hf
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hDS : (GlobalTheory.AmpTK.rep L).IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  have hmain := (GlobalTheory.isCoef_of_translate_smul_exists H.1.1.2.2.1 k r L.ε L.lam (GlobalTheory.AmpTK.rep L) L.Wp L.Wq l l' hDS).1
  have hd := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH (k := k) (r := r) hκ hτ
  have h1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ BranchingSupport.GG k r := by
    have := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd hdi
    rwa [Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ] at this
  obtain ⟨P, Q, hQ, hP, h⟩ := hf
  refine ⟨hmain f ⟨1, h1, 1, h1, P, Q, hQ, hP, fun g => ?_⟩, hmain _ ⟨_, hd, _, hdi, P, Q, hQ, hP, fun g => ?_⟩⟩
  · exact (congrArg f (by simp : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * g * 1 = g)).trans (h g)
  · exact (congrArg f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj_cjI hκ hτ g)).trans (h g)

end GlobalTheory.AmpTKGap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGapStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFiniteCoef_and_torusTranslate_isBesselCoef_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  first | exact @GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | exact GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | (intros; apply GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorOfHyps
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselCoefficientNonzeroExists
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.AmpTK

theorem exists_kFinCoef_torus_ne : BranchingSupport.Hyps → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H
  exact _root_.GlobalTheory.GapAmpTK.exists_kFinCoef_torus_ne_of_kfin H.1.2.2.1
end GlobalTheory.AmpTK
end

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem kfin_zero {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ 0 :=
  ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩

theorem isCoef_zero {k r : ℕ} (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) :
    IsCoef (rep L) l l' (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp, by simp⟩

end GlobalTheory.AmpTK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTKGapOne

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp GlobalTheory.AmpTK

theorem oneBesselTor_of_gapHyp : GlobalTheory.GapIn.Hyp → ∃ Cgf : ℝ, ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf := by
  intro H
  obtain ⟨Cgf, hCgf⟩ := GlobalTheory.T.exists_besselCell_gap_constant
  refine ⟨Cgf, fun D => ?_⟩
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  obtain ⟨h, hg, hok, hgc⟩ := hCgf D L.ε L.lam hgap
  have hc0 : L.c ≠ 0 := by
    rw [hc]; unfold cOfDpsi
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hκ₀.ne')
  obtain ⟨μG, hμG⟩ := GlobalTheory.SnMass.Inhab.exists_isHaarOn D.R.k D.R.rS
  obtain ⟨l, l', hBe, hl, hl'⟩ := GlobalTheory.T.exists_besselMaps_largeGap_periodIdentities H _ _ L h hg hok hc0 hκN hκNt
  have hBig : ∀ (c : Fin D.R.rS → ℂ) (μ : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μᴴ * Hb D.R.k * μ = Hb D.R.k → OneAt L l l' (bigCell D.R.k D.R.rS c μ) (pairMeas L) := by
    intro c μ hc' hμ
    obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.T.bigCell_trivialStabiliser_and_measures _ _ L μG hok.1 hκNt hκN hc0 hμG c μ hc' hμ
    obtain ⟨b, hb0, hb, hint⟩ := GlobalTheory.T.pair_space_majorant_integrable_big_cell _ _ L h hok hgc hκNt hκN hc0 c μ hc' hμ
    exact GlobalTheory.T.besselAmplitude_identity_translates_kFinite_largeGap H _ _ L h μG l l' hg hok hc0 hμG hBe _ _ _ _ h1 h2 h3 h4 h5 b hb0 hb hint
  have hCell : ∀ (γ : Point ℂ (D.R.rS + 1)) (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)
      (μR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g →
      IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OneAt L l l' g ν := by
    intro γ g μR ν h0 h1 h2 h3 h4
    obtain ⟨hR, ⟨νR, hQ⟩, b, hb0, hb, hint⟩ := GlobalTheory.T.smallCell_relevant_points_haar_quotient_majorant _ _ L h μG hok hgc hκNt hκN hc0 hμG γ g μR ν h0 h1 h2 h3 h4
    exact GlobalTheory.T.besselAmplitude_identity_translates_kFinite_largeGap H _ _ L h μG l l' hg hok hc0 hμG hBe g μR νR ν h1.1 h2 hR h4 hQ b hb0 hb hint
  obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.T.kFiniteCoef_and_torusTranslate_isBesselCoef_largeGap H _ _ L l l' κ τ hκ hτ f hf
  by_cases hs0 : s = 0
  · subst hs0
    refine ⟨fun _ => 0, 1, one_ne_zero, ⟨0, 0, fun _ => by simpa using GlobalTheory.AmpTK.kfin_zero L.σ,
      fun _ => by simpa using GlobalTheory.AmpTK.kfin_zero L.σ, fun _ => by simp⟩, ?_, ?_⟩
    · intro c μ hc' hμ
      obtain ⟨A, hA⟩ := hBig c μ hc' hμ
      rw [J_eq_orbInt, J_eq_orbInt, hA _ 0 (GlobalTheory.AmpTK.isCoef_zero L l l'), hA f 0 hs]
      simp
    · intro γ g μR ν h0 h1 h2 h3 h4
      obtain ⟨A, hA⟩ := hCell γ g μR ν h0 h1 h2 h3 h4
      rw [hA _ 0 (GlobalTheory.AmpTK.isCoef_zero L l l'), hA f 0 hs]
      simp
  · have hs' := hs
    obtain ⟨m, x, y, X, hxy, -, hsdef⟩ := hs'
    have hx : ∃ x ∈ (rep L).TK, l x ≠ 0 := by
      by_contra hne
      push_neg at hne
      apply hs0
      rw [hsdef]
      exact Finset.sum_eq_zero fun i _ => by rw [hne _ (hxy i).1, inner_zero_left]
    have hy : ∃ y ∈ (rep L).TK, l' y ≠ 0 := by
      by_contra hne
      push_neg at hne
      apply hs0
      rw [hsdef]
      exact Finset.sum_eq_zero fun i _ => by rw [hne _ (hxy i).2, map_zero, inner_zero_right]
    obtain ⟨f₁, s₁, hf₁, hc₁, hs₁⟩ := GlobalTheory.GapAmpTK.exists_kFinCoef_torus_ne H _ _ L l l' κ τ hκ hτ hl hl' hx hy
    refine ⟨f₁, s₁ / s, div_ne_zero hs₁ hs0, hf₁, ?_, ?_⟩
    · intro c μ hc' hμ
      obtain ⟨A, hA⟩ := hBig c μ hc' hμ
      rw [J_eq_orbInt, J_eq_orbInt, hA _ _ hc₁, hA f s hs, smul_smul, div_mul_cancel₀ _ hs0]
    · intro γ g μR ν h0 h1 h2 h3 h4
      obtain ⟨A, hA⟩ := hCell γ g μR ν h0 h1 h2 h3 h4
      rw [hA _ _ hc₁, hA f s hs, smul_smul, div_mul_cancel₀ _ hs0]

end GlobalTheory.AmpTKGapOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneBessel_torusTranslates_largeGap : GlobalTheory.GapIn.Hyp → ∃ Cgf : ℝ, ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf := by
  first | exact @GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | exact GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | (intros; apply GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp <;> assumption)
end
