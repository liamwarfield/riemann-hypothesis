module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelCoordinatesBijOnAndWeilLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMaximalCompactCharacterRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMatrixCoefficientEven
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMatrixCoefficientEven
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumEven

theorem cartan_laws {k p : ℕ} {G s B Y : Matrix (Fin k) (Fin k) ℂ} (hB : IsONBasis G s B p) (hY : IsPMat p Y) :
    (∃ κ, IsKMat p κ ∧ B * κ * B⁻¹ = s) ∧ (B * Y * B⁻¹)ᴴ * G + G * (B * Y * B⁻¹) = 0 ∧
      s * (B * Y * B⁻¹) = -(B * Y * B⁻¹ * s) := by
  obtain ⟨ε, hε, hBG, hsB⟩ := hB
  obtain ⟨hYh, hY0⟩ := hY

  have hEE : (diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hEh : (diagonal fun a => (ε a : ℂ))ᴴ = diagonal fun a => (ε a : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]

  have hEY : (diagonal fun a => (ε a : ℂ)) * Y = -(Y * diagonal fun a => (ε a : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · rw [hY0 i j hij]
      simp
    · rcases hε i with ⟨hi, hip⟩ | ⟨hi, hip⟩ <;> rcases hε j with ⟨hj, hjp⟩ | ⟨hj, hjp⟩
      · exact absurd (iff_of_true hip hjp) hij
      · rw [hi, hj]
        push_cast
        ring
      · rw [hi, hj]
        push_cast
        ring
      · exact absurd (iff_of_false (not_lt.2 hip) (not_lt.2 hjp)) hij
  have hoff : ∀ i j, ¬ (i.val < p ↔ j.val < p) → (diagonal fun a => (ε a : ℂ)) i j = 0 := by
    intro i j hij
    apply Matrix.diagonal_apply_ne
    intro h
    subst h
    exact hij Iff.rfl
  generalize (diagonal fun a => (ε a : ℂ)) = E at hEE hEh hEY hoff hBG hsB

  have hdet : IsUnit B.det := by
    have h1 : (Bᴴ * G * B * E).det = 1 := by rw [hBG, hEE, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul] at h1
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at h1
    simp at h1
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  have hc3 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBi', Matrix.conjTranspose_one]
  have hc4 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  have hc1 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, B⁻¹ * (B * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBi, Matrix.one_mul]
  have hc2 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Bᴴ * ((B⁻¹)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hc4, Matrix.one_mul]
  have hs : s = B * E * B⁻¹ := by
    calc s = s * B * B⁻¹ := by rw [Matrix.mul_assoc, hBi', Matrix.mul_one]
      _ = B * E * B⁻¹ := by rw [hsB]
  have hG : G = (B⁻¹)ᴴ * E * B⁻¹ := by
    rw [← hBG]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B⁻¹)ᴴ, hc3, Matrix.one_mul, hBi', Matrix.mul_one]
  subst hs hG
  refine ⟨⟨E, ⟨?_, hoff⟩, rfl⟩, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hEh, hEE]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hYh]
    simp only [Matrix.mul_assoc, hc1, hc2]
    rw [← Matrix.mul_assoc E Y, hEY]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
  · simp only [Matrix.mul_assoc, hc1]
    rw [← Matrix.mul_assoc E Y, hEY]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem atTau_oneP {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {s X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : IsCartanInv (gramAt D V τ) s) (hX : X ∈ lieAt V τ)
    (ha : s * X = -(X * s)) (t : ℝ) : atTau θ V τ s * oneP θ V τ X t = oneP θ V τ X (-t) * atTau θ V τ s := by
  obtain ⟨hss, hsU, -⟩ := hs
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hsU (GlobalTheory.Mem.Lift.exp_mem hX t),
    ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (GlobalTheory.Mem.Lift.exp_mem hX (-t)) hsU, GlobalTheory.FockKill.conj_exp hss ha t]

theorem ipO_smul_smul {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f g : Mx D m n → ℂ) :
    ipO μ 𝓕 (c • f) (c • g) = (Complex.normSq c : ℂ) * ipO μ 𝓕 f g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  rw [← Complex.mul_conj]
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem coeff_even : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → BS τ * YS * (BS τ)⁻¹ ∈ lieAt S τ ∧ BT τ * YT * (BT τ)⁻¹ ∈ lieAt T τ ∧ ∀ f g, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ t : ℝ, ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hpS hpT hcS hcT hbS hbT τ YS YT hYS hYT
  obtain ⟨⟨κS, hκS, hsS⟩, hlS, haS⟩ := cartan_laws (hbS τ) hYS
  obtain ⟨⟨κT, hκT, hsT⟩, hlT, haT⟩ := cartan_laws (hbT τ) hYT
  refine ⟨hlS, hlT, ?_⟩
  intro f g hf hvf hg hvg μ 𝓕 hμ t
  obtain ⟨mS, mT, hchar⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hom hθ τ
  have hUS : sS τ ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ) := by
    obtain ⟨-, h, -⟩ := hcS τ
    exact h
  have hUT : sT τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    obtain ⟨-, h, -⟩ := hcT τ
    exact h
  have hssS : sS τ * sS τ = 1 := by
    obtain ⟨h, -, -⟩ := hcS τ
    exact h
  have hssT : sT τ * sT τ = 1 := by
    obtain ⟨h, -, -⟩ := hcT τ
    exact h

  have hmul : ∀ a b φ, om a (om b φ) = om (a * b) φ := fun a b φ => by
    rw [map_mul, Module.End.mul_apply]

  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) φ) →
      om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) φ = c • φ :=
    ⟨_, fun φ hφ hvφ => hchar sS BS sT BT pS pT hpS hpT hcS hcT hbS hbT φ hφ hvφ κS κT hκS hκT _ _
      (by rw [hsS]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ hUS)
      (by rw [hsT]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ hUT)⟩
  by_cases hf0 : f = 0
  · subst hf0
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO]

  have hkk : om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) f) = f := by
    have h1 : ((1 : GA D S), (1 : GA D T)) = (1 : GA D S × GA D T) := rfl
    rw [hmul, Prod.mk_mul_mk, ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hUS hUS,
      ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hUT hUT, hssS, hssT, GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ,
      GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ, h1, map_one, Module.End.one_apply]
  rw [hc f hf hvf, map_smul, hc f hf hvf, smul_smul] at hkk
  have hcc : c * c = 1 := by
    by_contra hne
    apply hf0
    have h0 : (c * c - 1) • f = 0 := by rw [sub_smul, hkk, one_smul, sub_self]
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  have hn : (Complex.normSq c : ℂ) = 1 := by
    have h2 : Complex.normSq c * Complex.normSq c = 1 := by
      rw [← Complex.normSq_mul, hcc, Complex.normSq_one]
    have h3 : Complex.normSq c = 1 := by nlinarith [Complex.normSq_nonneg c]
    rw [h3, Complex.ofReal_one]

  have hconj : (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) *
      (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) =
      (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) *
      (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) := by
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, atTau_oneP hθ S τ (hcS τ) hlS haS (-t),
      atTau_oneP hθ T τ (hcT τ) hlT haT (-t), neg_neg]

  have hU : ∀ p φ φ', IsThetaFunO ψ S T φ → IsThetaFunO ψ S T φ' →
      ipO μ 𝓕 (om p φ) (om p φ') = ipO μ 𝓕 φ φ' := fun p φ φ' hφ hφ' =>
    GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hom μ 𝓕 hμ p φ φ' hφ hφ'
  calc ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g
      = ipO μ 𝓕 (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ))
          (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f))
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) g) := (hU _ _ g (hom.om_pres _ f hf) hg).symm
    _ = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t)
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) f))
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) g) := by
      congr 1
      rw [hmul, hmul, hconj]
    _ = ipO μ 𝓕 (c • om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) (c • g) := by
      rw [hc f hf hvf, hc g hg hvg, map_smul]
    _ = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
      rw [ipO_smul_smul, hn, one_mul]

end GlobalTheory.VacuumEven
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMatrixCoefficientEvenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_matrixCoefficient_even : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → BS τ * YS * (BS τ)⁻¹ ∈ lieAt S τ ∧ BT τ * YT * (BT τ)⁻¹ ∈ lieAt T τ ∧ ∀ f g, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ t : ℝ, ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
  first | exact @GlobalTheory.VacuumEven.coeff_even | exact GlobalTheory.VacuumEven.coeff_even | (intros; apply GlobalTheory.VacuumEven.coeff_even <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumOneParameterGeneratorCommutators
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumOneParameterGeneratorCommutators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceTensor.GenPair

theorem exists_pairing {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (G : BoundedContinuousFunction Z ℂ) :
    ∃ L : BoundedContinuousFunction Z ℂ →L[ℂ] ℂ, ∀ F, L F = ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν := by
  have hint : ∀ F : BoundedContinuousFunction Z ℂ, MeasureTheory.Integrable (fun w => F w * (starRingEnd ℂ) (G w)) ν :=
    fun F => (F * star G).integrable ν
  refine ⟨LinearMap.mkContinuous
    { toFun := fun F => ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν
      map_add' := fun F F' => by
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint F) (hint F')
      map_smul' := fun c F => by
        simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ } ((ν Set.univ).toReal * ‖G‖) fun F => ?_, fun F => rfl⟩
  have hb : ∀ w, ‖F w * (starRingEnd ℂ) (G w)‖ ≤ ‖F‖ * ‖G‖ := fun w => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (F.norm_coe_le_norm w) (G.norm_coe_le_norm w) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hb)
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc _ ≤ ‖F‖ * ‖G‖ * (ν Set.univ).toReal := by simpa [Measure.real] using this
    _ = _ := by ring

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.DefLift GlobalTheory.DefLift.Gen

theorem blk_sub_vecL {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} (Y : O → Matrix (Fin m) (Fin m) ℂ)
    (X : O → Matrix (Fin n) (Fin n) ℂ) (τ' : O) (u : Matrix (Fin m) (Fin n) ℂ) :
    (GlobalTheory.RealWeil.blk Y (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) X) *ᵥ
                 vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) =
      vecL (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext p
  obtain ⟨⟨i, j⟩, τ⟩ := p
  have key : ∀ (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ)
      (v : (Fin m × Fin n) × O → ℂ), (GlobalTheory.RealWeil.blk b a *ᵥ v) ((i, j), τ) = (b τ * cpt v τ * a τ) i j :=
    fun b a v => by rw [← cpt_blk]; rfl
  have hc : cpt (vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ)) τ = (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) τ := rfl
  rw [Matrix.sub_mulVec, Pi.sub_apply, key, key, hc]
  show _ = (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) τ i j
  by_cases h : τ = τ'
  · subst h
    simp
  · simp [h]

open scoped Classical

variable {D : D7} {θ : InfFam D}

theorem oneP_zero (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : oneP θ V τ X 0 = 1 := by
  have h := GlobalTheory.Mem.Lift.oneP_add hθ hX 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem oneP_inv (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel]
  exact GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX

theorem hasDerivAt_mM (hθ : IsInfFam θ) {S T : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hX : X ∈ lieAt S τ) {Y : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hY : Y ∈ lieAt T τ) (k l : GlobalTheory.RealWeil.Ix S T) :
    HasDerivAt (fun t : ℝ => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t) k l)
      ((GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X) :
        Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) k l) 0 := by
  obtain ⟨⟨i, j⟩, τ₁⟩ := k
  obtain ⟨⟨i', j'⟩, τ₂⟩ := l
  have hS : ∀ t : ℝ, (oneP θ S τ X t)⁻¹ = oneP θ S τ X (-t) := GlobalTheory.PlaceTensor.GenPair.oneP_inv hθ hX
  simp only [mM_apply, hS, GlobalTheory.RealWeil.blk, Matrix.sub_apply, Matrix.blockDiagonal_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h : τ₁ = τ₂
  · subst h
    simp only [if_true]
    have hb := hasDerivAt_comp hθ hY τ₁ i i'
    have ha0 := hasDerivAt_comp hθ hX τ₁ j' j
    have ha : HasDerivAt (fun t : ℝ => Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X t)) j' j)
        ((Pi.single τ X : D.what₂.Tau → _) τ₁ j' j) (-0) := by rw [neg_zero]; exact ha0
    have hT0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt T (oneP θ T τ Y 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]; exact compAt_fin (one_mem _) τ₁
    have hS0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX]; exact compAt_fin (one_mem _) τ₁
    refine (hb.mul (ha.scomp 0 (hasDerivAt_neg 0))).congr_deriv ?_
    simp only [Function.comp_apply, neg_zero, hT0, hS0, Matrix.one_apply]
    split_ifs <;> simp <;> ring
  · simp only [h, if_false, sub_zero]
    exact hasDerivAt_const _ _

theorem exists_generator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (τ : D.what₂.Tau), ∀ X ∈ lieAt S τ, ∀ Y ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (Y * u - u * X) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, oneP θ T τ Y t) f w) (Gn f w) 0) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g, IsThetaFunO ψ S T g → HasDerivAt (fun t : ℝ => ipO μ 𝓕 (om (oneP θ S τ X t, oneP θ T τ Y t) f) g) (ipO μ 𝓕 (Gn f) g) 0 := by
  intro D ψ θ S T χS χT om hW hθ τ X hX Y hY
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hweak : GlobalTheory.Ker.IsWeak ψ S T om := GlobalTheory.Ker.isWeak_of_datum hW
  have hcont : OmCont ψ S T om := hW.om_cont
  have hγc : Continuous fun t : ℝ => (oneP θ S τ X t, oneP θ T τ Y t) :=
    (GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
  have hγa : ∀ s t : ℝ, (oneP θ S τ X (s + t), oneP θ T τ Y (s + t)) =
      (oneP θ S τ X s, oneP θ T τ Y s) * (oneP θ S τ X t, oneP θ T τ Y t) := fun s t => by
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY]; rfl
  have hγm : ∀ t : ℝ, oneP θ S τ X t ∈ GinfC S ∧ oneP θ T τ Y t ∈ GinfC T := fun t =>
    ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩
  obtain ⟨lam, hlam⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ hσ ψ hψ S T om hweak hcont
    (fun t => (oneP θ S τ X t, oneP θ T τ Y t)) hγc hγa hγm _
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  have h0 : mM θ S T (oneP θ S τ X 0, oneP θ T τ Y 0) = 1 := by
    rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX, GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]
    exact (mM θ S T).map_one
  have hlie := GlobalTheory.Mem.Lift.GenZero.lie_of_path (HM S T)
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X))
    (fun t => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t)) h0 (fun t => mM_unitary hθ _)
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  obtain ⟨Gn, hGn⟩ := GlobalTheory.DefLift.Gen.exists_extension hσ hψ
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) lam
  refine ⟨Gn, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    ⟨GlobalTheory.RealWeil.toB hψ f hf, GlobalTheory.RealWeil.coe_toB hψ f hf⟩
  obtain ⟨hnt, hGF⟩ := hGn F hf
  have hAt : IsThetaFunO ψ S T ((nOp (rhoV hψ σ S T) (HM S T)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
      + lam • F).1 : WO S T → ℂ) := by
    rw [← GlobalTheory.DefLift.Gen.coe_add_smul]
    exact GlobalTheory.OrientedHeis.theta_add hnt (GlobalTheory.OrientedHeis.theta_smul lam hf)
  have hcomm : ∀ (τ' : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u F.1) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn F.1) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ'
        ((Pi.single τ Y : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) τ' * u -
          u * (Pi.single τ X : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) τ') F.1 := by
    intro τ' u
    have hdt := GlobalTheory.DefLift.Gen.theta_dH hσ hψ F hf
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    have e2 := (hGn _ hdt).2
    have e4 := nOp_add_comm HM_herm HM_det hlie (isHeis_rhoB hσ hψ) lam
      (GlobalTheory.RealWeil.sm_of_theta hσ hψ F hf) (GlobalTheory.RealWeil.sm_of_theta hσ hψ _ hnt)
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    rw [← GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' u, e2, hGF, ← GlobalTheory.DefLift.Gen.coe_dH hσ hψ _ hAt τ' u, e4,
      GlobalTheory.PlaceTensor.GenPair.blk_sub_vecL, GlobalTheory.DefLift.Gen.coe_add_sub]
    exact GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' _
  obtain ⟨u, hu1, hu2⟩ := hlam F hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hGF]; exact hAt
  · intro v
    rw [hcomm, Pi.single_eq_same, Pi.single_eq_same]
  · intro τ' h v
    have hc := hcomm τ' v
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.zero_mul, Matrix.mul_zero, sub_zero,
      GlobalTheory.DefLift.Gen.dRho_zero hσ hψ F hf] at hc
    exact sub_eq_zero.mp hc
  · intro w
    have h2 : HasDerivAt (fun t => ev _ _ w (u t)) (ev _ _ w (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F)) 0 :=
      ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [ev_apply, hu1] at h2
    rw [hGF]; exact h2
  · intro μ 𝓕 hμ g hg
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
      rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨L, hL⟩ := GlobalTheory.PlaceTensor.GenPair.exists_pairing (μ.restrict 𝓕) (GlobalTheory.RealWeil.toB hψ g hg).1
    have h2 : HasDerivAt (fun t => L (u t).1) (L (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F).1) 0 :=
      ((L.comp (BB ψ S T).subtypeL).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [hL, hu1, GlobalTheory.RealWeil.coe_toB] at h2
    rw [hGF]; exact h2

end GlobalTheory.PlaceTensor.GenPair

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumOneParameterGeneratorCommutatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_oneParameter_generator_commutators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (τ : D.what₂.Tau), ∀ X ∈ lieAt S τ, ∀ Y ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (Y * u - u * X) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, oneP θ T τ Y t) f w) (Gn f w) 0) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g, IsThetaFunO ψ S T g → HasDerivAt (fun t : ℝ => ipO μ 𝓕 (om (oneP θ S τ X t, oneP θ T τ Y t) f) g) (ipO μ 𝓕 (Gn f) g) 0 := by
  first | exact @GlobalTheory.PlaceTensor.GenPair.exists_generator | exact GlobalTheory.PlaceTensor.GenPair.exists_generator | (intros; apply GlobalTheory.PlaceTensor.GenPair.exists_generator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslatesSpanDenseThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslatesSpanDenseThetaFunctions
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisDense

theorem approx_periodic {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (Γ : AddSubgroup G)
    (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) {A : Type} [AddCommGroup A] (χ : A → G → ℂ)
    (hc : ∀ a, Continuous (χ a)) (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y)
    (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1) (hn : ∀ a x, ‖χ a x‖ = 1)
    (hker : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) (Φ : G → ℂ) (hΦ : Continuous Φ) (hper : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x)
    (ε : ℝ) (hε : 0 < ε) : ∃ p ∈ Submodule.span ℂ (Set.range χ), ∀ x, ‖Φ x - p x‖ ≤ ε := by
  have hπ : Continuous (QuotientAddGroup.mk : G → G ⧸ Γ) := QuotientAddGroup.continuous_mk
  have : CompactSpace (G ⧸ Γ) := ⟨by
    rw [show (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K from ?_]
    · exact hK.image hπ
    refine (Set.eq_univ_of_forall fun q => ?_).symm
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨γ, hγ, hk⟩ := hcov x
    refine ⟨γ + x, hk, QuotientAddGroup.eq.2 ?_⟩
    simpa using hγ⟩
  have desc : ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      ∃ p : C(G ⧸ Γ, ℂ), ∀ x : G, p (x : G ⧸ Γ) = f x := by
    intro f hf hp
    have hw : ∀ x y : G, (QuotientAddGroup.leftRel Γ) x y → f x = f y := by
      intro x y hxy
      rw [QuotientAddGroup.leftRel_apply] at hxy
      rw [← hp _ hxy x]
      congr 1
      abel
    exact ⟨⟨Quotient.lift f hw, hf.quotient_lift hw⟩, fun x => rfl⟩
  choose e he using fun a => desc (χ a) (hc a) fun γ hγ x => by rw [hx, (hker γ).2 hγ a, one_mul]
  obtain ⟨φ, hφ⟩ := desc Φ hΦ hper
  have ext : ∀ p q : C(G ⧸ Γ, ℂ), (∀ x : G, p (x : G ⧸ Γ) = q (x : G ⧸ Γ)) → p = q := by
    intro p q h
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact h x
  have hne : ∀ a x, χ a x ≠ 0 := fun a x h => by simpa [h] using hn a x
  have hmul : ∀ a b, ∃ c, e c = e a * e b := fun a b => ⟨a + b, ext _ _ fun x => by simp [he, ha]⟩
  have hstar : ∀ a, ∃ c, e c = star (e a) := fun a => ⟨-a, ext _ _ fun x => by
      have h1 : χ (-a) x * χ a x = 1 := by rw [← ha, neg_add_cancel, h0]
      have h2 : (starRingEnd ℂ) (χ a x) * χ a x = 1 := by simp [Complex.conj_mul', hn]
      simpa [he] using mul_right_cancel₀ (hne a x) (h1.trans h2.symm)⟩
  have hsep : ∀ z w, z ≠ w → ∃ a, e a z ≠ e a w := fun z w hzw => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective w
      by_contra hcon
      push Not at hcon
      refine hzw (QuotientAddGroup.eq.2 ((hker _).1 fun a => ?_))
      have h1 := hcon a
      rw [he, he] at h1
      have h2 : χ a x * χ a (-x + y) = χ a x * 1 := by rw [← hx, add_neg_cancel_left, mul_one, h1]
      exact mul_left_cancel₀ (hne a x) h2
  let V : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range e)
  have hV1 : (1 : C(G ⧸ Γ, ℂ)) ∈ V := Submodule.subset_span ⟨0, ext _ _ fun x => by simp [he, h0]⟩
  have hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V := by
    intro p hp q hq
    have : V * V ≤ V := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact hmul a b
    exact this (Submodule.mul_mem_mul hp hq)
  have hVstar : ∀ p ∈ V, star p ∈ V := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span (hstar a)
    | zero => rw [star_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq)
      star_mem' := fun {p} hp => hVstar p hp }
  have hS : S.topologicalClosure = ⊤ := by
    refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
    intro x y hxy
    obtain ⟨a, ha⟩ := hsep x y hxy
    exact ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ha⟩
  have hφS : φ ∈ closure (S : Set C(G ⧸ Γ, ℂ)) := by
    have : φ ∈ S.topologicalClosure := by rw [hS]; trivial
    exact this
  obtain ⟨q, hq, hd⟩ := Metric.mem_closure_iff.1 hφS ε hε
  have hq' : q ∈ V := hq
  refine ⟨fun x => q (x : G ⧸ Γ), ?_, fun x => ?_⟩
  · clear hd hq
    induction hq' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨a, funext fun x => (he a x).symm⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul c x _ hx => exact Submodule.smul_mem _ c hx
  · rw [← hφ, ← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist _).trans hd.le

theorem approx_abstract {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (Γ : AddSubgroup G)
    (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {R : Type} [CommRing R] [TopologicalSpace R] [ContinuousAdd R] (ψ : AddChar R ℂ) (hψc : Continuous ψ)
    (hψn : ∀ x, ‖ψ x‖ = 1) (H : G → G → R)
    (hl : ∀ x y z, H (x + y) z = H x z + H y z) (hr : ∀ x y z, H x (y + z) = H x y + H x z)
    (halt : ∀ x, H x x = 0) (hcont : Continuous fun q : G × G => H q.1 q.2)
    (hann : ∀ x, (∀ γ ∈ Γ, ψ (H x γ + H x γ) = 1) ↔ x ∈ Γ)
    (f₀ f : G → ℂ) (c₀ : Continuous f₀) (c : Continuous f)
    (q₀ : ∀ γ ∈ Γ, ∀ w, f₀ (γ + w) = ψ (-(H γ w)) * f₀ w) (q : ∀ γ ∈ Γ, ∀ w, f (γ + w) = ψ (-(H γ w)) * f w)
    (hne : f₀ ≠ 0) (g : G → G → ℂ) (hg : ∀ a x, g a x = ψ (H x a) * f₀ (x + a)) (ε : ℝ) (hε : 0 < ε) :
    ∃ f' ∈ Submodule.span ℂ (Set.range g), ∀ x, ‖f x - f' x‖ ≤ ε := by
  classical
  have hskew : ∀ x y : G, H y x = -H x y := by
    intro x y
    have h := halt (x + y)
    rw [hl, hr, hr, halt x, halt y] at h
    linear_combination h
  have hz : ∀ x : G, H x 0 = 0 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    linear_combination -h
  have hcy : ∀ y : G, Continuous fun x : G => H x y := fun y =>
    hcont.comp (continuous_id.prodMk continuous_const)
  have hψ0 : ∀ r, ψ r ≠ 0 := fun r h => by simpa [h] using hψn r
  have hst : ∀ r, ψ (-r) * star (ψ (-r)) = 1 := fun r => by
    rw [GlobalTheory.HeisTotal.star_char ψ hψn, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have gc : ∀ a, Continuous (g a) := fun a => by
    rw [show g a = _ from funext (hg a)]
    exact (hψc.comp (hcy a)).mul (c₀.comp (continuous_id.add continuous_const))
  have gq : ∀ a, ∀ γ ∈ Γ, ∀ x, g a (γ + x) = ψ (-(H γ x)) * g a x := fun a γ hγ x => by
    rw [hg, hg, add_assoc, q₀ γ hγ, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hl, hr]
    congr 2; ring
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ a x, ‖g a x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn c₀.continuousOn
    refine ⟨max C 1, lt_max_of_lt_right one_pos, fun a x => ?_⟩
    obtain ⟨γ, hγ, hk⟩ := hcov (x + a)
    have := hC _ hk
    rw [q₀ γ hγ, norm_mul, hψn, one_mul] at this
    rw [hg, norm_mul, hψn, one_mul]
    exact le_max_of_le_left this
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a => {x | g a x ≠ 0})
    (fun a => isOpen_ne_fun (gc a) continuous_const) fun x _ => Set.mem_iUnion.2 ⟨y - x, by
      show g (y - x) x ≠ 0
      rw [hg, add_sub_cancel]
      exact mul_ne_zero (hψ0 _) hy⟩
  let N : G → ℂ := fun x => ∑ a ∈ t, g a x * star (g a x)
  have Nc : Continuous N := continuous_finsetSum _ fun a _ => (gc a).mul (gc a).star
  have Np : ∀ γ ∈ Γ, ∀ x, N (γ + x) = N x := fun γ hγ x => Finset.sum_congr rfl fun a _ => by
    rw [gq a γ hγ, star_mul']
    linear_combination (g a x * star (g a x)) * hst (H γ x)
  have N0 : ∀ x, N x ≠ 0 := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    rw [← Np γ hγ]
    obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht hk)
    have e : N (γ + x) = ((∑ a ∈ t, ‖g a (γ + x)‖ ^ 2 : ℝ) : ℂ) := by
      simp [N, Complex.mul_conj']
    rw [e, Complex.ofReal_ne_zero]
    refine ne_of_gt (Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, ha, pow_pos (norm_pos_iff.2 h) 2⟩)
  have hn1 : (0 : ℝ) < t.card + 1 := Nat.cast_add_one_pos _
  have hδ : 0 < ε / ((t.card + 1) * C) := div_pos hε (mul_pos hn1 hC0)
  have key : ∀ a : G, ∃ p ∈ Submodule.span ℂ (Set.range fun (γ : Γ) (x : G) => ψ (H x γ + H x γ)),
      ∀ x, ‖f x * star (g a x) / N x - p x‖ ≤ ε / ((t.card + 1) * C) := by
    intro a
    refine approx_periodic Γ K hK hcov (fun (γ : Γ) x => ψ (H x γ + H x γ)) ?_ ?_ ?_ ?_ ?_ ?_
      (fun x => f x * star (g a x) / N x) ((c.mul (gc a).star).div Nc N0) ?_ _ hδ
    · intro γ
      exact hψc.comp ((hcy _).add (hcy _))
    · intro γ x y
      rw [← AddChar.map_add_eq_mul, hl]
      congr 1; ring
    · intro γ γ' x
      rw [← AddChar.map_add_eq_mul, AddSubgroup.coe_add, hr]
      congr 1; ring
    · intro x
      rw [AddSubgroup.coe_zero, hz, add_zero, AddChar.map_zero_eq_one]
    · intro γ x
      exact hψn _
    · intro x
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩
    · intro γ hγ x
      show f (γ + x) * star (g a (γ + x)) / N (γ + x) = f x * star (g a x) / N x
      rw [Np γ hγ, gq a γ hγ, q γ hγ, star_mul']
      congr 1
      linear_combination (f x * star (g a x)) * hst (H γ x)
  choose p hp hp' using key
  refine ⟨∑ a ∈ t, p a * g a, Submodule.sum_mem _ fun a _ => ?_, fun x => ?_⟩
  · have h := hp a
    generalize p a = r at h
    induction h using Submodule.span_induction with
    | mem r hr' =>
      obtain ⟨γ, rfl⟩ := hr'
      have e : (fun x : G => ψ (H x γ + H x γ)) * g a = ψ (H γ a) • g (γ + a) := by
        funext x
        rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hg, hg, add_left_comm x, q₀ γ γ.2]
        have e' : ψ (H x γ + H x γ) * ψ (H x a) =
            ψ (H γ a) * ψ (H x (γ + a)) * ψ (-(H γ (x + a))) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hr, hr, hskew x γ]
          congr 1; ring
        linear_combination f₀ (x + a) * e'
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul b u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu
  · have e : f x - (∑ a ∈ t, p a * g a) x = ∑ a ∈ t, (f x * star (g a x) / N x - p a x) * g a x := by
      have e1 : ∑ a ∈ t, f x * star (g a x) / N x * g a x = f x := by
        have : ∀ a, f x * star (g a x) / N x * g a x = f x / N x * (g a x * star (g a x)) := fun a => by ring
        simp only [this]
        rw [← Finset.mul_sum]
        exact div_mul_cancel₀ _ (N0 x)
      simp only [sub_mul, Finset.sum_sub_distrib, e1, Finset.sum_apply, Pi.mul_apply]
    rw [e]
    calc _ ≤ ∑ a ∈ t, ε / ((t.card + 1) * C) * C := norm_sum_le_of_le _ fun a _ => by
          rw [norm_mul]
          exact mul_le_mul (hp' a x) (hC a x) (norm_nonneg _) hδ.le
      _ = ε * (t.card / (t.card + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← div_div, div_mul_cancel₀ _ hC0.ne']
          ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one hn1).2 (le_add_of_nonneg_right zero_le_one)) hε.le
      _ = ε := mul_one _

theorem approx_uniform {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) (hf : IsThetaFunO ψ S T f) (ε : ℝ) (hε : 0 < ε) :
    ∃ f' ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T w f₀), ∀ x, ‖f x - f' x‖ ≤ ε := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x
  exact approx_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann f₀ f
    h₀.cont hf.cont (GlobalTheory.HeisTotal.quasi_of_mem h₀) (GlobalTheory.HeisTotal.quasi_of_mem hf) hne _ (fun _ _ => rfl) ε hε

theorem span_translates_dense : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ f' ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T w f₀), nrm2 μ 𝓕 (f - f') < ε := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ f hf ε hε
  obtain ⟨f', h1, h2⟩ := approx_uniform (base_std hb) (base_theta hb) (base_ne_zero hb) hf (Real.sqrt (ε / 2))
    (Real.sqrt_pos.2 (half_pos hε))
  refine ⟨f', h1, ?_⟩
  have h3 : μ 𝓕 = 1 := hμ.2.2
  have h4 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := 𝓕) (f := fun w => ‖(f - f') w‖ ^ 2) (C := ε / 2)
    (by rw [h3]; exact ENNReal.one_lt_top) fun x _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _), ← Real.sq_sqrt (half_pos hε).le]
      exact pow_le_pow_left₀ (norm_nonneg _) (h2 x) 2
  rw [Measure.real, h3, ENNReal.toReal_one, mul_one] at h4
  exact ((le_abs_self _).trans h4).trans_lt (half_lt_self hε)

end GlobalTheory.HeisDense

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslatesSpanDenseThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_translates_span_dense_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ f' ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T w f₀), nrm2 μ 𝓕 (f - f') < ε := by
  first | exact @GlobalTheory.HeisDense.span_translates_dense | exact GlobalTheory.HeisDense.span_translates_dense | (intros; apply GlobalTheory.HeisDense.span_translates_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanSquareNormWeilRepSub
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanSquareNormWeilRepSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilNormCont

theorem continuous_meanSquareNorm_weilRep_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  intro D ψ S T χS χT om μ 𝓕 hom hμ f₁ f₂ h₁ h₂
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b, hb⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₂ h₂ {1} isCompact_singleton
  have hb' : ∀ w, ‖f₂ w‖ ≤ b := fun w => by simpa using hb 1 rfl w
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₁ h₁ K hK
  unfold nrm2
  refine continuousAt_of_dominated (bound := fun _ => (c + b) ^ 2) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    exact ((((hom.om_pres p f₁ h₁).cont.sub h₂.cont).norm.pow 2).measurable).aestronglyMeasurable
  · filter_upwards [hK0] with p hp
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hc p hp w) (hb' w))) 2
  · refine Filter.Eventually.of_forall fun w => ?_
    exact (((hom.om_cont f₁ h₁ w).sub continuous_const).norm.pow 2).continuousAt

end GlobalTheory.WeilNormCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanSquareNormWeilRepSubStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_nrm2_om_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  first | exact @GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub | exact GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub | (intros; apply GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem unitary (D : D7) : Unitary D := by
  intro ψ S T χS χT om hW
  have hstd := hW.std
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨⟨(μ₀, 𝓕₀), h₀⟩, fun q hq f₁ f₂ hf₁ hf₂ => ?_⟩
  have L := GlobalTheory.T.theta_inner_product_hermitian D ψ S T q.1 q.2 hstd hq f₁ f₂ hf₁ hf₂
  refine ⟨fun c => GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul c hf₁) hf₂, L.1, L.2.2.2.2.2.1,
    L.2.2.2.2.2.2.2, fun w => ⟨?_, (L.2.2.2.2.2.2.1 w).1⟩, fun p => ⟨hW.om_pres p f₁ hf₁, ?_⟩,
    GlobalTheory.T.continuous_nrm2_om_sub D ψ S T χS χT om q.1 q.2 hW hq f₁ f₂ hf₁ hf₂⟩
  · exact (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₁ hf₁
  · exact GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW q.1 q.2 hq p f₁ f₂ hf₁ hf₂

theorem restrictedTensor (D : D7) : RestrictedTensor D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  have hstd := base_std hB
  have hinf := base_inf hB
  refine ⟨fun p f hf => ⟨((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hstd hinf f hf.1).2 p hf).1,
      GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW hinf p f hf⟩,
    fun x hx => GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x hx, fun f hf ε hε => ?_,
    fun x f hx => ⟨fun w => GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w,
      fun g h => GlobalTheory.T.weilRep_acts_on_pureTensors_placewise D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x f hx g h⟩⟩
  obtain ⟨f', hf', hlt⟩ := GlobalTheory.T.heisenberg_translates_span_dense_thetaFunctions D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ f hf ε hε
  refine ⟨f', Submodule.span_mono ?_ hf', hlt⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨_, GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ (fun _ => f₀) f₀
    (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1 w⟩

theorem coeffProduct (D : D7) : CoeffProduct D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ x₂ f₂ h₁ h₂ g h
  exact GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ x₂ _ f₂
    (GlobalTheory.T.weilRep_acts_on_pureTensors_placewise D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ h₁ g h) h₂

theorem cA_cA {D : D7} {e : AE D} {p : Place D} (h : e + cA D e = idem D p) : cA D (cA D e) = e := by
  have hp : cA D (idem D p) = idem D p := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p
  have h2 : cA D e + cA D (cA D e) = cA D e + e := by
    rw [← map_add (f := _), h, hp, ← h, add_comm]
  exact add_left_cancel h2

theorem isSplitIdem_cA {D : D7} {e : AE D} {p : Place D} (he : IsSplitIdem D e) (h : e + cA D e = idem D p) :
    IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, hε⟩ := he
  have hcc := cA_cA h
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [hcc, mul_comm, h2]
  · rw [hcc, add_comm, hε]

theorem splitModel (D : D7) : SplitModel D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := GlobalTheory.T.splitPlace_matrix_coordinate_on_half D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  refine ⟨(GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB v e he.1 he.2.1).1, fun Tm hTm => ?_⟩
  have M := GlobalTheory.T.schrodingerModel_coordinates_bijOn_and_weil_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e e he.1 he.2.1 (Or.inl rfl)
    T.rank S.rank (mapCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalf_eq_pull]
  exact ⟨M.1, fun ν hν => GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v e he.1 T.rank S.rank
    (mapCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ S BS g) (grpCo φ T BT h) (fun t => hC.2 g h t) Φ hΦ⟩

theorem splitModelAdj (D : D7) : SplitModelAdj D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := GlobalTheory.T.splitPlaceAdjointMatrix_isCoordinate_equivariant D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hs : IsSplitIdem D (cA D e) := isSplitIdem_cA he.1 he.2.1
  have hsum : cA D e + cA D (cA D e) = idem D (.inl v) := by
    rw [cA_cA he.2.1, add_comm]
    exact he.2.1
  refine ⟨(GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB v (cA D e) hs hsum).1, fun Tm hTm => ?_⟩
  have M := GlobalTheory.T.schrodingerModel_coordinates_bijOn_and_weil_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e (cA D e) he.1 he.2.1 (Or.inr rfl)
    S.rank T.rank (adjCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalfAdj_eq_pull]
  exact ⟨M.1, fun ν hν => GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v (cA D e) hs S.rank T.rank
    (adjCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ T BT h) (grpCo φ S BS g) (fun t => hC.2 g h t) Φ hΦ⟩

theorem deriv_eq_zero_of_even {c : ℝ → ℂ} {a : ℂ} (h : HasDerivAt c a 0) (he : ∀ t, c (-t) = c t) : a = 0 := by
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id' (0 : ℝ)).neg
  have h0 : HasDerivAt c a (-(0 : ℝ)) := by rwa [neg_zero]
  have h1 := h0.scomp (0 : ℝ) hn
  have h2 : (c ∘ fun t : ℝ => -t) = c := funext fun t => he t
  rw [h2] at h1
  have h3 := h.unique h1
  rw [neg_one_smul] at h3
  linear_combination h3 / 2

private theorem exists_conj_mul_eq_mul {ι : Type*} {n : ℕ} (C C' : ι → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i, C i * C' i = 1)
    (s B : ι → Matrix (Fin n) (Fin n) ℂ) :
    ∃ s' B' : ι → Matrix (Fin n) (Fin n) ℂ, (∀ i, s' i * C i = C i * s i) ∧ ∀ i, B' i = C i * B i := by
  refine ⟨fun i => C i * s i * C' i, fun i => C i * B i, fun i => ?_, fun i => rfl⟩
  have h' : C' i * C i = 1 := mul_eq_one_comm.mp (h i)
  simp only [Matrix.mul_assoc, h', Matrix.mul_one]

theorem fockModel (D : D7) : FockModel D := by
  intro ψ θ S T χS χT om hW hθ τ
  obtain ⟨mS, mT, hm⟩ := GlobalTheory.T.fockVacuum_maximalCompact_character_realPlace D ψ θ S T χS χT om hW hθ τ
  refine ⟨mS, mT, ?_⟩
  intro sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac P
  have hstd := hW.std
  have hPT : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) := by
    intro Q
    obtain ⟨sS', BS', hS', hBS'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D S)) sS BS
    obtain ⟨sT', BT', hT', hBT'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D T)) sT BT
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS' BS BS' sT sT' BT BT' 1 1
      hS' hT' hBS' hBT' f hf Q).1
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨hPT P, fun μ 𝓕 hμ Q => GlobalTheory.T.fockVectors_inner_eq_fockInnerProduct_mul_norm D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT
      f hf hvac μ 𝓕 hμ P Q,
    fun κS κT hκS hκT g h hg hh => GlobalTheory.T.maximalCompact_acts_on_fockVectors_by_substitution D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT
      hBS hBT f hf τ κS κT hκS hκT g h hg hh _
      (hm sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac κS κT hκS hκT g h hg hh) P,
    fun YS YT hYS hYT w => ?_⟩
  have hL := GlobalTheory.T.fockVacuum_matrixCoefficient_even D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT
  obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_oneParameter_generator_commutators D ψ θ S T χS χT om hW hθ τ _ hL.1 _ hL.2.1

  have key := GlobalTheory.T.fock_operator_acts_by_noncompact_quadratic_ops D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT μ₀ 𝓕₀ h₀ Gn
    (fun f' hf' => ⟨(hGn f' hf').1, (hGn f' hf').2.1, (hGn f' hf').2.2.1⟩) f hf hvac
    (fun g hg hgv => deriv_eq_zero_of_even ((hGn f hf).2.2.2.2 μ₀ 𝓕₀ h₀ g hg)
      (fun t => hL.2.2 f g hf hvac hg hgv μ₀ 𝓕₀ h₀ t)) P
  rw [← key]
  exact (hGn _ (hPT P)).2.2.2.1 w

theorem placeModels : ∀ D : D7, PlaceModels D := fun D =>
  ⟨unitary D, restrictedTensor D, coeffProduct D, splitModel D, splitModelAdj D, GlobalTheory.T.splitPlace_thetaLattice_halves_selfDual_frames D, GlobalTheory.T.inert_place_stabilizers_fix_weil_lattice_vacuum D,
    GlobalTheory.T.splitPlace_latticeStabilisers_fix_weilVacuum D, fockModel D, GlobalTheory.T.fockVectors_pureTensors D, GlobalTheory.T.definiteThetaLift_localVector D, GlobalTheory.T.thetaChainStepVector_localPureTensor D⟩

end GlobalTheory.PlaceTensor
