module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselPeriodAdjointPair
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolyTopOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundOnEarlierRegion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBesselScaleBound
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPair
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdsPositive
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalBuiltPlaces
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpqRepVocabularyAgree
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem upqRep_vocabulary_agree : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : B.Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), (Formalism.MainNotions.S.IsDSHpk k r ε lam σ ↔ PI.UpqRep.IsDSHpk k r ε lam σ) ∧ (∀ v, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v ↔ PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) ∧ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ = PI.UpqRep.smoothVecs (k := k) (r := r) σ ∧ (Formalism.QuantumDeterminants.IsHCParam lam ↔ PI.UpqRep.IsHCParam lam) ∧ (∀ P, Formalism.MainNotions.S.IsCayleyU k r ε P ↔ PI.UpqRep.IsCayleyU k r ε P) ∧ Formalism.MainNotions.S.lowKSub ε lam σ = PI.UpqRep.lowKSub ε lam σ := by
  intro k r H _ _ _ σ ε lam
  exact ⟨Iff.rfl, fun _ => Iff.rfl, rfl, Iff.rfl, fun _ => Iff.rfl, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalSectionBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTwoSidedHaarOfLeftInvariantProbabilityCompactUStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTwoSidedHaarOfLeftInvariantProbabilityCompact
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
open scoped ENNReal

namespace GlobalTheory.ThA

private lemma measurable_lmulM_flag_measures {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) a) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.measurable_sum _ fun l _ => measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply l))

private lemma measurable_rmulF' {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Measurable (B.rmulF a) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

private lemma measurableSet_lmulM_pair_mem {k r : ℕ} {A : Set (Mt k r)} (hA : MeasurableSet A) :
    MeasurableSet {p : Mt k r × Mt k r | lmulM (Matrix.of p.2) p.1 ∈ A} := by
  have hm : Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hm hA

theorem measure_eq_smul_of_left_right {k r : ℕ} {U : Set (B.Mat k r)} {μ ν : Measure (Mt k r)}
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, (Matrix.of x : B.Mat k r) ∈ U) (hν : ∀ᵐ x ∂ν, (Matrix.of x : B.Mat k r) ∈ U)
    (hl : ∀ a ∈ U, Measure.map (lmulM a) μ = μ) (hr : ∀ a ∈ U, Measure.map (B.rmulF a) ν = ν) :
    ν = ν Set.univ • μ := by
  ext A hA
  set S : Set (Mt k r × Mt k r) := {p | lmulM (Matrix.of p.2) p.1 ∈ A} with hSdef
  have hS : MeasurableSet S := measurableSet_lmulM_pair_mem hA

  have hx : (μ.prod ν) S = ν A := by
    rw [Measure.prod_apply hS]
    have hslice : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' S) = ν A := by
      filter_upwards [hμ] with x hx
      have hpre : Prod.mk x ⁻¹' S = B.rmulF (Matrix.of x) ⁻¹' A := rfl
      rw [hpre, ← Measure.map_apply (measurable_rmulF' _) hA, hr _ hx]
    rw [lintegral_congr_ae hslice, lintegral_const, measure_univ, mul_one]

  have hy : (μ.prod ν) S = μ A * ν Set.univ := by
    rw [Measure.prod_apply_symm hS]
    have hslice : ∀ᵐ y ∂ν, μ ((fun x => (x, y)) ⁻¹' S) = μ A := by
      filter_upwards [hν] with y hy
      have hpre : (fun x => (x, y)) ⁻¹' S = lmulM (Matrix.of y) ⁻¹' A := rfl
      rw [hpre, ← Measure.map_apply (measurable_lmulM_flag_measures _) hA, hl _ hy]
    rw [lintegral_congr_ae hslice, lintegral_const]
  rw [Measure.smul_apply, smul_eq_mul, ← hx, hy, mul_comm]

theorem haarW_twoSided_of_left : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  intro k r z μ _ _ hH h1
  obtain ⟨_, hne, hconc, hleft⟩ := hH
  haveI : IsProbabilityMeasure μ := ⟨h1⟩
  have hinvU : ∀ g ∈ UWset k r z, g⁻¹ ∈ UWset k r z ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 :=
    fun g hg => Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hg
  have hUm : MeasurableSet {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ UWset k r z} :=
    (show IsClosed {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ UWset k r z} from
      Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r z).measurableSet
  have hμU : ∀ᵐ x ∂μ, (Matrix.of x : B.Mat k r) ∈ UWset k r z := ae_iff.mpr hconc

  have hinvm : Measurable (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) := Formalism.FourierDecayAlt.P.HermitianFormFactor.invF_meas
  obtain ⟨ν, hνdef⟩ : ∃ ν : Measure (Mt k r), ν = μ.map (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) := ⟨_, rfl⟩
  have hmass : ν Set.univ = 1 := by
    rw [hνdef, Measure.map_apply hinvm MeasurableSet.univ, Set.preimage_univ, h1]
  haveI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hνU : ∀ᵐ x ∂ν, (Matrix.of x : B.Mat k r) ∈ UWset k r z := by
    rw [hνdef]
    refine (ae_map_iff hinvm.aemeasurable hUm).2 ?_
    filter_upwards [hμU] with x hx using (hinvU _ hx).1

  have hνr : ∀ a ∈ UWset k r z, Measure.map (B.rmulF a) ν = ν := by
    intro a ha
    obtain ⟨hai, haa, -⟩ := hinvU a ha
    rw [hνdef, Measure.map_map (measurable_rmulF' a) hinvm]
    have hcomp : (B.rmulF a ∘ (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1)))) = (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) ∘ lmulM a⁻¹ := by
      funext x
      show ((Matrix.of x)⁻¹ * a : B.Mat k r) = (a⁻¹ * Matrix.of x)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv haa]
    rw [hcomp]
    exact (Measure.map_map hinvm (measurable_lmulM_flag_measures a⁻¹)).symm.trans (congrArg (Measure.map _) (hleft _ hai))
  have hkey := measure_eq_smul_of_left_right (μ := μ) (ν := ν) hμU hνU hleft hνr
  rw [hmass, one_smul] at hkey
  refine ⟨hconc, hleft, fun a ha => ?_, fun K _ => measure_lt_top μ K, hne⟩
  have h := hνr a ha
  rwa [hkey] at h

end GlobalTheory.ThA
end

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  first | exact @GlobalTheory.ThA.haarW_twoSided_of_left | exact GlobalTheory.ThA.haarW_twoSided_of_left | (intros; apply GlobalTheory.ThA.haarW_twoSided_of_left <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatum
namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem exists_isStdOf (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hk : 1 ≤ k) (hsec : IsSection k r L.z L.z' μsec) :
    ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  obtain ⟨μG, hμG⟩ := P.unitary_group_haar_exists k r
  obtain ⟨χ, hχs, hχsupp, hχint⟩ := P.character_exists_alt
  have h1 := GlobalTheory.T.hcTypeW_continuous_unitary_irreducible k r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  have h1' := GlobalTheory.T.hcTypeW_continuous_unitary_irreducible k r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  have hW := GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary k r L.z L.μW L.hz.1 L.hz.2 L.hμW.1 L.hμW.2
  have hW' := GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary k r L.z' L.μW' L.hz'.1 L.hz'.2 L.hμW'.1 L.hμW'.2
  have hN := P.Dx2.MN.haar (k := k) r
  exact ⟨⟨L.z, L.z', L.π, L.π', μG, L.μW, D.muN k r, L.μW', μsec, χ, hk, L.hz.1, L.hz'.1, L.hz.2, L.hz'.2,
    h1.2.1, h1'.2.1, h1.2.2.2.1, h1'.2.2.2.1, h1.2.2.1, h1'.2.2.1, hμG, hW, hN, hW', hsec, hχs, hχsupp, hχint⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ThA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatumStatement
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_localBesselDatum : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k → IsSection k r L.z L.z' μsec → ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  first | exact @GlobalTheory.ThA.exists_isStdOf | exact GlobalTheory.ThA.exists_isStdOf | (intros; apply GlobalTheory.ThA.exists_isStdOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PlExists
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB GlobalTheory.ThA Finset NumberField MeasureTheory Formalism.QuantumDeterminants Matrix

namespace GlobalTheory.ThA

theorem plExists : PlExists := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs ν' m₀ l0 hl1 hl2 hk hW hW' hN hF hP

  obtain ⟨T, hz, hz', hπ, hπ', hTn⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have ez : (T.bs 0).z = Bs.z := hz
  have ez' : (T.bs 0).z' = Bs.z' := hz'
  have eπ : (T.bs 0).π = Bs.π := hπ
  have eπ' : (T.bs 0).π' = Bs.π' := hπ'

  let T' : D.LevTower P.k P.r Wp Wq :=
    { bs := fun j => Nat.rec (motive := fun j => B.RealPlaceData P.k (P.r - j) Wp Wq) Bs (fun n _ => T.bs (n + 1)) j
      z_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z_lev 0 hj
          rw [ez] at h0
          exact h0
        | succ n => exact (T.z_lev (n + 1) hj).trans ez
      z'_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z'_lev 0 hj
          rw [ez'] at h0
          exact h0
        | succ n => exact (T.z'_lev (n + 1) hj).trans ez'
      π_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π_lev 0 hj y
          rw [eπ] at h0
          exact h0
        | succ n => exact (T.π_lev (n + 1) hj y).trans (congrFun eπ _)
      π'_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π'_lev 0 hj y
          rw [eπ'] at h0
          exact h0
        | succ n => exact (T.π'_lev (n + 1) hj y).trans (congrFun eπ' _) }
  have hT'n : D.TowerNormalised T' := by
    intro j hj
    cases j with
    | zero => exact ⟨hW, hW', hN⟩
    | succ n => exact hTn (n + 1) hj

  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP
  obtain ⟨L, st, hXL, hQQ, hq, hinv, hstar, hstart⟩ :=
    Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP X l0
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k P.r Wp Wq Bs
  have hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 :=
    ⟨hP, hμ.1, hXL, hQQ, hq, hinv, hstar, hstart⟩
  obtain ⟨Θ, hΘ1, hΘ2⟩ := hTL Wp Wq P Bs X μ L st l0 hl1 hl2 hD

  obtain ⟨he1, he2, he3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts Bs ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' (m₀ *ᵥ ν') hP he1 he2 he3
  exact ⟨⟨l0, T', ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hT'n, hF, hP, ⟨X, μ, L, st, hD, hΘ1⟩⟩, rfl, rfl, rfl, rfl, hΘ2⟩

end GlobalTheory.ThA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceOfLocalBesselDatumInterlacing
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceOfLocalBesselDatumInterlacing
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory.PlaceOfLocalBesselType

theorem isType_of_isHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hU : ∀ i : Fin k, U (i.val + 1) = u i) : Q.IsType k r z π U := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', h1, h2, h3, h4, h5, -⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  exact ⟨h1, h2, h3, h4, h5, GlobalTheory.ThA.capParam_of_isHCTypeW k r z u U Wp π hz hT hπ hU⟩

noncomputable def ext {k : ℕ} (u : Fin k → ℝ) (i : ℕ) : ℝ := if h : i - 1 < k then u ⟨i - 1, h⟩ else 0

theorem ext_succ {k : ℕ} (u : Fin k → ℝ) (i : Fin k) : ext u (i.val + 1) = u i := by
  simp [ext]

theorem add_one_le {a b c l : ℝ} (ha : ∃ m : ℤ, a = m + c) (hb : ∃ m : ℤ, b = m + c) (h1 : a < l) (h2 : l < b) :
    a + 1 ≤ b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have h : (m : ℝ) < n := by linarith
  have h' : m + 1 ≤ n := by exact_mod_cast h
  have h'' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h'
  linarith

end GlobalTheory.PlaceOfLocalBesselType

namespace GlobalTheory

open PlaceOfLocalBesselType

theorem exists_place_of_locBessel : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  intro k r L μsec lam0 hk h2 hsec hI hI'
  have hk1 : 1 ≤ k := by omega
  obtain ⟨Bs, hBs⟩ := GlobalTheory.T.exists_normalised_localBesselDatum k r L μsec hk1 hsec
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of Bs
  have hT := isType_of_isHCTypeW k r L.z L.u (ext L.u) L.Wp L.π L.hz.1 L.hz.2 L.hπ (ext_succ L.u)
  have hT' := isType_of_isHCTypeW k r L.z' L.u' (ext L.u') L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ' (ext_succ L.u')
  have hZ := GlobalTheory.capelliParam_mem_int_add_half k r L.Wp L.z L.π _ L.hz.1 L.hz.2 hT
  have hZ' := GlobalTheory.capelliParam_mem_int_add_half k r L.Wq L.z' L.π' _ L.hz'.1 L.hz'.2 hT'
  have h1 : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨le_rfl, hk1⟩
  have hOK : (⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ : M.Par).OK := by
    refine ⟨hk1, L.hz.2, L.hz'.2, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ' i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      dsimp only at hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j + 1 < k := by omega
      have m1 : j + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have m2 : j + 1 + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      obtain ⟨a1, a2⟩ := hI.1 j hj
      obtain ⟨b1, b2⟩ := hI'.1 j hj
      rw [← ext_succ L.u] at a1 a2
      rw [← ext_succ L.u'] at b1 b2
      dsimp only at a1 a2 b1 b2
      have c1 := add_one_le (hZ _ m2) (hZ _ m1) a2 a1
      have c2 := add_one_le (hZ _ m2) (hZ' _ m1) a2 b1
      have c3 := add_one_le (hZ' _ m2) (hZ _ m1) b2 a1
      have c4 := add_one_le (hZ' _ m2) (hZ' _ m1) b2 b1
      simp only [M.Par.lo, M.Par.hi]
      rcases max_choice (ext L.u (j + 1 + 1)) (ext L.u' (j + 1 + 1)) with e | e <;>
        rcases min_choice (ext L.u (j + 1)) (ext L.u' (j + 1)) with e' | e' <;> rw [e, e'] <;> linarith
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hBs
  obtain ⟨Cb, hCb⟩ := GlobalTheory.ThA.plExists
  obtain ⟨p, -, hp, -⟩ := hCb L.Wp L.Wq ⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ Bs ν' m₀ 1 le_rfl hk1 h2
    (by rw [e5]; exact L.hμW.2) (by rw [e6]; exact L.hμW'.2) e7 hF
    (by rw [e1, e2, e3, e4]; exact ⟨hOK, L.hz.1, L.hz'.1, rfl, rfl, hT, hT'⟩)
  refine ⟨ext L.u, ext L.u', p, fun i => ⟨ext_succ _ i, ext_succ _ i⟩, ?_⟩
  rw [hp]
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceOfLocalBesselDatumInterlacingStatement
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_of_localBesselDatum_interlacing : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  first | exact @GlobalTheory.exists_place_of_locBessel | exact GlobalTheory.exists_place_of_locBessel | (intros; apply GlobalTheory.exists_place_of_locBessel <;> assumption)
end
end

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem pointwiseBound_at_place_of_locBessel : ThmBpDS → ∀ Ch : ℝ, ∃ C₄ Cg₀ : ℝ, 0 ≤ C₄ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq) (n₀ : ℕ), IsStdOf L μsec p.T.base ∧ n₀ ≤ 30 * (D.R.rS + 1) ^ 2 + 6 ∧ TBB.ThmBpAt p f b C₄ n₀ (2 * (D.R.rS + 1)) := by
  classical
  intro hT Ch
  obtain ⟨C₄, G₀, hC₄, h⟩ := hT Ch 2 (by norm_num)
  refine ⟨C₄, G₀, hC₄, fun Cg hCg D L lam0 f μsec ka b hL hg hf hsec => ?_⟩
  obtain ⟨-, hε, -, -, -, hS, -⟩ := hL
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨U, U', p, hU, hstd⟩ :=
    GlobalTheory.T.exists_place_of_localBesselDatum_interlacing D.R.k D.R.rS L μsec lam0 (by omega) hk hsec hS.2.1 hS.2.2.1
  have hu : (fun i : Fin D.R.k => U (i.val + 1)) = L.u := funext fun i => (hU i).1
  have hu' : (fun i : Fin D.R.k => U' (i.val + 1)) = L.u' := funext fun i => (hU i).2
  have he : L.ε = PI.BesselPeriodGGP.eps48 D.R.k D.R.rS := by
    rw [hε]; funext i; rfl
  obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
  have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
  refine ⟨U, U', p, if ∀ i ∈ Finset.Icc 1 D.R.k, U i = U' i then 30 * (D.R.rS + 1) ^ 2 + 6 else 0, hstd,
    by split_ifs <;> omega, ?_⟩
  refine h Cg hCg ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq p lam0 L.lam ka b _ _
    ⟨L.Hs, L.σ⟩ f ?_ hg ?_ ?_ (fun e => if_pos e) (fun e => if_neg e) ?_ ?_
  · show StdHyp Ch Cg D.R.k D.R.rS _ lam0 (fun i : Fin D.R.k => U (i.val + 1))
      (fun i : Fin D.R.k => U' (i.val + 1)) _ _ ka b
    rw [hu, hu', ← he]
    exact hS
  · show BranchingSupport.Rep.IsDS (k := D.R.k) (r := D.R.rS) ⟨L.Hs, L.σ⟩ (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) L.lam
    rw [← he]
    exact ⟨L.hlam, v1.1 L.hσ⟩
  · obtain ⟨P, Q, hQ, hP, hfe⟩ := hf
    exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
      simpa using hfe g⟩
  · show 3 * (D.R.rS + 1) ≤ 2 * (2 * (D.R.rS + 1))
    omega
  · show ((2 * (D.R.rS + 1) : ℕ) : ℝ) ≤ 2 * ((D.R.rS : ℝ) + 1) ^ 2
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    push_cast
    nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BpFormsOfThmBpDS
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenGapCoef
open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory

theorem eigDec_of_isKFinCoefT : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro H k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := H.1.2.2.1
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.isCoef_ckOn_inCC H k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDS hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.T.capelli_eigenvalue_kFinite_discreteSeries_coeff hsm H.2.2.1 k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.T.centredCapelliOperator_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory

end
end

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem bpNear_thresholds (k r : ℕ) (hk : 1 ≤ k) :
    2 * ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) + ThreeDimData.AG k r + 3 ≤
        31 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * ThreeDimData.AG k r + 3 ≤
        24 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
        2 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      1 ≤ ((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * r + k + 1 := by push_cast; ring
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hndef
  set s : ℝ := (r : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by linarith
  have hn1 : 1 ≤ n := by linarith
  have key : ∀ i j : ℕ, i ≤ 4 → j ≤ 3 → s ^ i * n ^ j ≤ s ^ 4 * n ^ 3 := fun i j hi hj =>
    mul_le_mul (pow_le_pow_right₀ hs1 hi) (pow_le_pow_right₀ hn1 hj) (by positivity) (by positivity)
  have hM : ThreeDimData.Mexp r ≤ 2 * s ^ 2 := by unfold ThreeDimData.Mexp; rw [hs]; nlinarith
  have hM0 : 0 ≤ ThreeDimData.Mexp r := by unfold ThreeDimData.Mexp; positivity
  have hG : ThreeDimData.AG k r ≤ 4 * n * s := by
    unfold ThreeDimData.AG; rw [← hs]
    have : (k : ℝ) + r ≤ n := by linarith
    nlinarith
  have hG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hd : ThreeDimData.dN k r ≤ 2 * s * n := by unfold ThreeDimData.dN; rw [hs, hn]; nlinarith [mul_nonneg hr hr]
  have hd0 : 0 ≤ ThreeDimData.dN k r := by unfold ThreeDimData.dN; nlinarith [mul_nonneg hr hr, mul_nonneg hr (by linarith : (0 : ℝ) ≤ k)]
  have hS : ThreeDimData.AS k r ≤ n * (2 * s * n) := by
    unfold ThreeDimData.AS
    refine mul_le_mul ?_ hd hd0 (by linarith)
    rw [hn]; push_cast; linarith
  have hS0 : 0 ≤ ThreeDimData.AS k r := by unfold ThreeDimData.AS; positivity
  have hP : ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ 2 * s ^ 2 * (n * (2 * s * n) + 4 * n * s) :=
    mul_le_mul hM (by linarith) (by linarith) (by positivity)
  have k32 := key 3 2 (by omega) (by omega)
  have k31 := key 3 1 (by omega) (by omega)
  have k11 := key 1 1 (by omega) (by omega)
  have k12 := key 1 2 (by omega) (by omega)
  have k20 := key 2 0 (by omega) (by omega)
  have k00 := key 0 0 (by omega) (by omega)
  have hrn : s ^ 2 * (r * n) ≤ s ^ 3 * n ^ 1 := by
    have : (r : ℝ) * n ≤ s * n := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    calc s ^ 2 * (r * n) ≤ s ^ 2 * (s * n) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = s ^ 3 * n ^ 1 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · simpa using k00

theorem bpNear_gapOK (k r : ℕ) (hk : 1 ≤ k) (c Cg : ℝ) (hC : 240 + 2 * |c| ≤ Cg) :
    ThreeDimData.GapOK k r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 2) ∧
    c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      ThreeDimData.aOf r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 2) - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := bpNear_thresholds k r hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hc : 0 ≤ |c| := abs_nonneg c
  have hm : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have hn0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((3 * (r + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hm]
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hndef
  set N : ℝ := ((3 * (r + 1) : ℕ) : ℝ)
  have hs1 : (1 : ℝ) ≤ 2 * ((r : ℝ) + 1) := by linarith
  have hpos : (0 : ℝ) < 2 * ((r : ℝ) + 1) := by linarith
  have hsq : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := Real.sqrt_pos.2 hpos
  have hpow : (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) =
      (2 * ((r : ℝ) + 1)) ^ 4 * Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [Real.sqrt_eq_rpow, show (9 : ℝ) / 2 = (4 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_natCast]
  have hge : 1 ≤ (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) := Real.one_le_rpow hs1 (by norm_num)
  have hZ : n ^ 3 ≤ N * n ^ 2 + n ^ 3 := by have : 0 ≤ N * n ^ 2 := by positivity
                                            linarith
  have hCg : 0 ≤ Cg := by linarith
  have ha : Cg * (((r : ℝ) + 1) ^ 4 * n ^ 3) ≤
      ThreeDimData.aOf r (Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) / 2) := by
    have e : ThreeDimData.aOf r (Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) / 2) =
        Cg * (((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3)) := by
      unfold ThreeDimData.aOf; rw [hpow]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ (by positivity)) hCg
  set Y : ℝ := ((r : ℝ) + 1) ^ 4 * n ^ 3 with hY
  have hCY : (240 + 2 * |c|) * Y ≤ Cg * Y := mul_le_mul_of_nonneg_right hC (by linarith)
  have hcY : 0 ≤ |c| * Y := mul_nonneg hc (by linarith)
  refine ⟨⟨hk, ?_, by linarith, by linarith⟩, ?_⟩
  · have e1 : 240 * 1 ≤ Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) :=
      mul_le_mul (by linarith) hge (by norm_num) hCg
    have e2 : 240 * 1 * n ^ 3 ≤ Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) :=
      mul_le_mul e1 hZ (by positivity) (by positivity)
    linarith
  · have e0 : 0 ≤ ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1) := by positivity
    have e1 : c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)) ≤ |c| * (2 * Y) :=
      mul_le_mul (le_abs_self c) h3 e0 hc
    nlinarith

theorem bpNear_gapAtLeast {n : ℕ} (ε : Fin n → Bool) (lam lam0 : Fin n → ℝ) (h : ℝ) (h0 : GapAtLeast ε lam0 h)
    (hg : AllGaps lam0 (200 * l1 lam lam0)) : GapAtLeast ε lam (h / 2) := by
  intro a b hab
  have hne : a ≠ b := fun e => hab (by rw [e])
  have h1 := h0 a b hab
  have h2 := hg a b hne
  have hd : ∀ s, |lam s - lam0 s| ≤ l1 lam lam0 := fun s =>
    Finset.single_le_sum (f := fun a => |lam a - lam0 a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have h3 : |lam0 a - lam0 b| ≤ |lam a - lam b| + |lam a - lam0 a| + |lam b - lam0 b| := by
    have e : lam0 a - lam0 b = (lam a - lam b) - (lam a - lam0 a) + (lam b - lam0 b) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith [abs_sub (lam a - lam b) (lam a - lam0 a)])
  linarith [hd a, hd b, abs_nonneg (lam0 a - lam0 b)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientSmoothDecayCapelliEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliDiscreteSeriesInfChar
namespace GlobalTheory

theorem capelliDiscreteSeriesInfChar : PI.DSInfCharCap.DSInfCharCap :=
  CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientSmoothDecayCapelliEigen
open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory

theorem eigDec_of_isKFinCoefT_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro hH k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := hH.1.1.2.2.1
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH.1 k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDG hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.CapelliEigenvalue.capEig hsm GlobalTheory.capelliDiscreteSeriesInfChar k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.ThA.centredCapelli_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientSmoothDecayCapelliEigenStatement
open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesCoefficient_smooth_decay_capelliEigen_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  first | exact @GlobalTheory.eigDec_of_isKFinCoefT_gap | exact GlobalTheory.eigDec_of_isKFinCoefT_gap | (intros; apply GlobalTheory.eigDec_of_isKFinCoefT_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem bp_forms_of_gapIn_thmBpDS : GlobalTheory.GapIn.Hyp → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  intro hH hT Ch
  obtain ⟨C₄, G₀, hC₄, hloc⟩ := GlobalTheory.pointwiseBound_at_place_of_locBessel hT Ch
  obtain ⟨c₃, hdict⟩ := GlobalTheory.ThA.BpDict.bpIneq_of_thmBpAt
  refine ⟨max (C₄ + 1) 10, max G₀ (240 + 2 * |c₃|), fun Cg hCg => ?_⟩
  have hG₀ : G₀ ≤ Cg := (le_max_left _ _).trans hCg
  have hG₁ : 240 + 2 * |c₃| ≤ Cg := (le_max_right _ _).trans hCg
  have main : ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D (max (C₄ + 1) 10) L f μsec b γ := by
    intro D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨U, U', p, n₀, hstd, hn₀, hB⟩ := hloc Cg hG₀ D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨hk, -, hc, hκ0, hκ, hS, -⟩ := hL
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -, -, hall, hgap, -⟩ := hS
    obtain ⟨hOK, hA⟩ := bpNear_gapOK D.R.k D.R.rS hk c₃ Cg hG₁
    obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
    have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
    have hE := GlobalTheory.T.discreteSeriesCoefficient_smooth_decay_capelliEigen_largeGap hH D.R.k D.R.rS L.ε L.lam _ ⟨L.Hs, L.σ⟩ L.Wp L.Wq f ⟨L.hlam, v1.1 L.hσ⟩
      (bpNear_gapAtLeast _ _ _ _ hgap hg) hOK (by
        obtain ⟨P, Q, hQ, hP, he⟩ := hf
        exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
          simpa using he g⟩)
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = 2 * ((D.R.rS : ℝ) + 1) := by push_cast; ring
    have hb3 : 3 ≤ b := by
      have h1 := hall ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      have h2 := abs_sub (lam0 ⟨0, by omega⟩) (lam0 ⟨1, by omega⟩)
      have h3 : (1 : ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by rw [hm]; linarith)
      have h4 : 240 * 1 ≤ Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul (by linarith [abs_nonneg c₃]) h3 (by norm_num) (by linarith [abs_nonneg c₃])
      linarith [hb ⟨0, by omega⟩, hb ⟨1, by omega⟩]
    refine hdict D L μsec U U' p f _ b C₄ _ n₀ _ hstd (hc.trans Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one) hκ0.ne' hκ hA (hE.2.1 1)
      hb3 (le_max_left _ _) ?_ hB
    have h1 : (n₀ : ℝ) ≤ 30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn₀
    have h2 : 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ max (C₄ + 1) 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    refine le_trans ?_ h2
    rw [hm]; push_cast; nlinarith
  refine ⟨main, ?_, ?_⟩
  · intro D L f μsec ka b hL hf hsec
    exact main D L L.lam f μsec ka b hL (fun s s' _ => by simp [l1]) hf hsec
  · intro D Cu Cg' hCu L lam0 f μsec ka b hL hR hf hsec _
    refine main D L lam0 f μsec ka b hL (fun s s' hs => le_trans ?_ (hR.1 s s' hs)) hf hsec
    have h1 := hR.2
    have h2 : 200 * Cu * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) ≤
        Cg' * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right hCu (by positivity)
    nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGapsStatement
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPointwiseBound_at_largeGaps : GlobalTheory.GapIn.Hyp → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  first | exact @GlobalTheory.bp_forms_of_gapIn_thmBpDS | exact GlobalTheory.bp_forms_of_gapIn_thmBpDS | (intros; apply GlobalTheory.bp_forms_of_gapIn_thmBpDS <;> assumption)
end
