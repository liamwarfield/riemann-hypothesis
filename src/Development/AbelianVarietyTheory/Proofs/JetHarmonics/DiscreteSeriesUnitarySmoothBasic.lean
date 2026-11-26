module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexifiedDerivedActionLieHomGramAdjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedCutoffStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_isLowUnitH_of_isDSHpk {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε mu σ) : ∃ w, ‖w‖ = 1 ∧ PI.UpqRep.IsLowUnitH k r ε mu σ w := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hn : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
    rw [norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, hn, P, hP, hn, ?_⟩
  exact Submodule.smul_mem _ _ (le_sSup (s := {S | PI.UpqRep.IsKTypeOf ε (fun g => σ (P⁻¹ * g * P))
    (PI.UpqRep.lowK ε mu) S}) hS hvS)

theorem rep_basic_of_isDS : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  intro hK k r ε mu R hR
  obtain ⟨hmu, hσ⟩ := hR
  obtain ⟨h1, hunit⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hσ
  have hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v) := by
    intro g hg h hh v
    rw [Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hg hh]; rfl
  have hone : ∀ v, R.σ 1 v = v := fun v => by rw [h1]; rfl
  have hsm : ∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm := fun g hg v hv =>
    Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hσ hv hg
  refine ⟨hmul, hone, ?_, hsm, ?_, ?_, ?_, ?_, fun v => Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ v⟩
  · intro g hg
    exact (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 (hunit g hg)
  · have : R.TK ≤ R.smSub := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, hg, v₀, hv₀, rfl⟩
      exact hsm g hg v₀ (hK k r ε mu R.H R.σ hmu hσ v₀ hv₀)
    exact fun v hv => this hv
  · intro g hg
    have : R.TK ≤ R.TK.comap ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, hh, v₀, hv₀, rfl⟩
      exact Submodule.subset_span ⟨g * h, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg hh, v₀, hv₀, (hmul g hg h hh v₀).symm⟩
    exact fun v hv => this hv
  · intro v hv
    refine Submodule.subset_span ⟨1, ?_, v, hv, (hone v).symm⟩
    show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  · obtain ⟨w, hw, hlow⟩ := exists_isLowUnitH_of_isDSHpk hσ
    exact ⟨w, hw, PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow, hlow⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasicStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_unitary_smooth_basic : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  first | exact @GlobalTheory.rep_basic_of_isDS | exact GlobalTheory.rep_basic_of_isDS | (intros; apply GlobalTheory.rep_basic_of_isDS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quotMeas_ae_mem_and_measurable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hR hS
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r := by
    obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  have hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := by
    convert (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl using 1
    ext x
    simp
  have hrestr : νq.restrict {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} = νq :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hcont : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V),
      ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq := by
    intro V _ _ φ hφ
    have hof : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mx k r)) := continuous_id
    have h1 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} :=
      hφ.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := νq) hmeas
    rwa [hrestr] at h2
  refine ⟨hae, hcont, ?_, ?_⟩
  · intro a
    exact (hcont ℝ _ (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable
  · intro l hl w hw
    exact hcont Wp _ (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModelStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  first | exact @GlobalTheory.quotMeas_ae_mem_and_measurable | exact GlobalTheory.quotMeas_ae_mem_and_measurable | (intros; apply GlobalTheory.quotMeas_ae_mem_and_measurable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModule
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModule
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

private lemma inv_conj_mul_conj {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q)
    (A B : Matrix (Fin n) (Fin n) ℂ) : (Q⁻¹ * A * Q) * (Q⁻¹ * B * Q) = Q⁻¹ * (A * B) * Q := by
  have h : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  calc (Q⁻¹ * A * Q) * (Q⁻¹ * B * Q) = Q⁻¹ * A * (Q * Q⁻¹) * B * Q := by
        simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * (A * B) * Q := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private lemma single_one_mul_single_one_jet_harmonics {n : ℕ} (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · simp [h]

theorem conj_single_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
      (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q) =
    (if b = c then Q⁻¹ * Matrix.single a d 1 * Q else 0) -
      (if d = a then Q⁻¹ * Matrix.single c b 1 * Q else 0) := by
  rw [inv_conj_mul_conj Q hQ, inv_conj_mul_conj Q hQ, ← Matrix.sub_mul, ← Matrix.mul_sub,
    single_one_mul_single_one_jet_harmonics, single_one_mul_single_one_jet_harmonics]
  split_ifs <;> simp [Matrix.mul_sub, Matrix.sub_mul]

theorem smooth_gl_module : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  intro hK k r ε mu R hDS Q hQ
  obtain ⟨hmem, hlin, hadd, -, hbr, -⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hDS
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hz : ∀ Y, R.dC Y 0 = 0 := fun Y => by
    have h := hlin Y 1 0 h0 0 h0
    simpa using h
  have hY0 : ∀ v ∈ R.sm, R.dC 0 v = 0 := fun v hv => by
    have h := hadd 0 0 1 v hv
    simpa using h
  have hsub : ∀ Y Z, ∀ v ∈ R.sm, R.dC (Y - Z) v = R.dC Y v - R.dC Z v := fun Y Z v hv => by
    have h := hadd Z (Y - Z) 1 v hv
    simp only [one_smul, add_sub_cancel] at h
    rw [h, add_sub_cancel_left]
  let E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub := fun a b =>
    { toFun := fun v => ⟨R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v, hmem _ v v.2⟩
      map_add' := fun v w => Subtype.ext (by simpa using hlin _ 1 v v.2 w w.2)
      map_smul' := fun c v => Subtype.ext (by simpa [hz] using hlin _ c v v.2 0 h0) }
  refine ⟨E, fun a b v => rfl, ?_⟩
  intro a b c d
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have lhs : (((E a b * E c d - E c d * E a b) v : R.smSub) : R.H) =
      R.dC ((Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
        (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q)) v := by
    rw [← hbr _ _ v v.2]; rfl
  rw [lhs, conj_single_comm Q hQ a b c d, hsub _ _ v v.2]
  split_ifs <;> simp [E, hY0 v v.2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModuleStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_discreteSeries_glModule : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  first | exact @GlobalTheory.smooth_gl_module | exact GlobalTheory.smooth_gl_module | (intros; apply GlobalTheory.smooth_gl_module <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HilbertSchmidtNormSubmulInvGeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HilbertSchmidtNormSubmulInvGeOne
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix

namespace GlobalTheory.BesselNorm

theorem hilbertSchmidt_normInv : Formalism.FourierDecayAlt.ThreeDimData.NormInv := fun _ _ =>
  ⟨fun x y => PI.PolynomialProperness.GN.gN_mul_le x y,
    fun _ hx => ⟨PI.PolynomialProperness.GN.gN_inv hx, PI.PolynomialProperness.GN.gN_ge_one hx⟩⟩

end GlobalTheory.BesselNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HilbertSchmidtNormSubmulInvGeOneStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_norm_submul_inv_ge_one : Formalism.FourierDecayAlt.ThreeDimData.NormInv := by
  first | exact @GlobalTheory.BesselNorm.hilbertSchmidt_normInv | exact GlobalTheory.BesselNorm.hilbertSchmidt_normInv | (intros; apply GlobalTheory.BesselNorm.hilbertSchmidt_normInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotent
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace BesselGrowth

theorem continuous_hsNorm (k r : ℕ) :
    Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r)) := by
  unfold Formalism.FourierDecayAlt.B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  refine Complex.continuous_normSq.comp ?_
  exact (continuous_apply j).comp (continuous_apply i)

theorem measurable_hsNorm_rpow (k r : ℕ) (A : ℝ) :
    Measurable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A)) :=
  (continuous_hsNorm k r).measurable.pow_const _

theorem hsNorm_nonneg {k r : ℕ} (g : Mx k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

theorem growthS_of (hN : NormInv) (hG : GrowthG) : GrowthS := by
  intro k r z μW μN μG νq A _ _ hW hNn hGm hq hA
  obtain ⟨hS0, hS⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hNn
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hGm.2.2.1 hS0 hS hq
  have hA0 : 0 ≤ A := by
    have : 0 ≤ AG k r := by unfold AG; positivity
    linarith
  have hint := hG k r μG A hGm hA
  have hm := measurable_hsNorm_rpow k r A
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A)) with hF
  have hFm : Measurable F := hm.ennreal_ofReal
  have hfin : ∫⁻ x, F x ∂μG < ⊤ := hint.lintegral_lt_top
  have hν : νq Set.univ ≠ 0 := by
    intro h0
    have h1 := hq (fun _ => 1) measurable_const
    rw [Measure.measure_univ_eq_zero.mp h0, lintegral_zero_measure, lintegral_one] at h1
    exact hGm.2.1 (Measure.measure_univ_eq_zero.mp h1)
  have hSfin : ∫⁻ s, F s ∂(muSof μW μN) < ⊤ := by
    by_contra hc
    have htop : ∫⁻ s, F s ∂(muSof μW μN) = ⊤ := top_le_iff.mp (not_lt.mp hc)
    have hle : ∫⁻ _x, (⊤ : ℝ≥0∞) ∂νq ≤
        ∫⁻ x, (∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN)) ∂νq := by
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with x hx
      have hx1 := ((hN k r).2 _ hx).2
      have hFx : F x ≠ 0 := by
        simp only [hF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact Real.rpow_pos_of_pos (by linarith) _
      have h2 : ∫⁻ s, F s * F x ∂(muSof μW μN) = ⊤ := by
        rw [lintegral_mul_const _ hFm, htop, ENNReal.top_mul hFx]
      rw [← h2]
      refine lintegral_mono_ae ?_
      filter_upwards [(ae_iff.mpr hS : ∀ᵐ s ∂(muSof μW μN),
        Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))] with s hs
      have hsx := ((hN k r).2 _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hs hx)).2
      simp only [hF]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hsNorm_nonneg _) _),
        ← Real.mul_rpow (hsNorm_nonneg _) (hsNorm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos hsx) ((hN k r).1 _ _) (by linarith)
    rw [← hq F hFm, lintegral_const, ENNReal.top_mul hν] at hle
    exact absurd hfin (not_lt.mpr hle)
  have hf : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) :=
      continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) :=
      continuous_snd
    exact h1.matrix_mul h2
  have hI : Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A))
      (muSof μW μN) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hsNorm_nonneg _) _)).mpr hSfin⟩
  exact (integrable_map_measure hm.aestronglyMeasurable hf.measurable.aemeasurable).mp hI

end BesselGrowth

theorem besselGrowthS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS :=
  BesselGrowth.growthS_of GlobalTheory.T.hilbertSchmidt_norm_submul_inv_ge_one GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotentStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGrowth_stabilizer_unipotent : Formalism.FourierDecayAlt.ThreeDimData.GrowthS := by
  first | exact @GlobalTheory.besselGrowthS | exact GlobalTheory.besselGrowthS | (intros; apply GlobalTheory.besselGrowthS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.QuotRightInv

open PI

theorem measurable_mul_left {m : ℕ} (x : MtM m) :
    Measurable (fun s : MtM m => (fun i j => (Matrix.of s * Matrix.of x) i j : MtM m)) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurable_rmulQ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : Measurable (rmulQ g) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rmulQ, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurableSet_not_mem {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    MeasurableSet {x : MtM m | Matrix.of x ∉ G} := by
  have hc : IsClosed {x : MtM m | Matrix.of x ∈ G} := by
    have hof : Continuous (fun x : MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
    exact hG.1.preimage hof
  exact hc.measurableSet.compl

private lemma mul_not_mem_of_mem_of_not_mem {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G)
    (hSG : S ⊆ G) {s x : Matrix (Fin m) (Fin m) ℂ} (hs : s ∈ S) (hx : x ∉ G) : s * x ∉ G := by
  intro hsx
  apply hx
  obtain ⟨hinv, hone⟩ := hG.2.2.2 s (hSG hs)
  have hleft : s⁻¹ * s = 1 := mul_eq_one_comm.mp hone
  have h1 := hG.2.2.1 _ hinv _ hsx
  rwa [← Matrix.mul_assoc, hleft, Matrix.one_mul] at h1

private lemma continuous_mul_swap_pair {m : ℕ} :
    Continuous (fun p : MtM m × MtM m => (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : MtM m)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem ae_mem_of_quot {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
    (h : QuotientSetting G S μG μS ν) : ∀ᵐ x ∂ν, Matrix.of x ∈ G := by
  obtain ⟨hG, hS, hSG, hHG, hHS, -, -, hQ⟩ := h
  have : SigmaFinite μS := hHS.1
  have hBm : MeasurableSet {x : MtM m | Matrix.of x ∉ G} := measurableSet_not_mem hG
  have hSm : MeasurableSet {x : MtM m | Matrix.of x ∈ S} := by
    have h1 := (measurableSet_not_mem hS).compl
    simpa only [Set.compl_setOf, not_not] using h1
  have hf : Measurable ({x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)) :=
    measurable_one.indicator hBm
  have h0 := hQ _ hf
  rw [lintegral_indicator_one hBm, hHG.2.2.1] at h0
  have hinner : Measurable fun x : MtM m =>
      ∫⁻ s, {x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS :=
    Measurable.lintegral_prod_right (hf.comp continuous_mul_swap_pair.measurable)
  have hae := (lintegral_eq_zero_iff hinner).mp h0.symm
  have hSpos : μS {s : MtM m | Matrix.of s ∈ S} ≠ 0 := by
    intro hz
    apply hHS.2.1
    rw [← Measure.measure_univ_eq_zero]
    have hu := measure_union_le (μ := μS) {s : MtM m | Matrix.of s ∈ S} {s : MtM m | Matrix.of s ∈ S}ᶜ
    rw [Set.union_compl_self] at hu
    have hc : μS {s : MtM m | Matrix.of s ∈ S}ᶜ = 0 := hHS.2.2.1
    rw [hz, hc, add_zero] at hu
    exact le_antisymm hu zero_le
  filter_upwards [hae] with x hx
  by_contra hxG
  apply hSpos
  refine le_antisymm ?_ zero_le
  refine le_trans ?_ (le_of_eq hx)
  rw [← lintegral_indicator_one hSm]
  refine lintegral_mono fun s => ?_
  by_cases hs : Matrix.of s ∈ S
  · have hs' : s ∈ {s : MtM m | Matrix.of s ∈ S} := hs
    have hmem : (fun i j => (Matrix.of s * Matrix.of x) i j : MtM m) ∈ {x : MtM m | Matrix.of x ∉ G} :=
      mul_not_mem_of_mem_of_not_mem hG hSG hs hxG
    have e1 : {s : MtM m | Matrix.of s ∈ S}.indicator (1 : MtM m → ℝ≥0∞) s = 1 :=
      Set.indicator_of_mem hs' _
    have e2 : {x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)
        (fun i j => (Matrix.of s * Matrix.of x) i j) = 1 := Set.indicator_of_mem hmem _
    exact (e1.trans e2.symm).le
  · have e1 : {s : MtM m | Matrix.of s ∈ S}.indicator (1 : MtM m → ℝ≥0∞) s = 0 :=
      Set.indicator_apply_eq_zero.mpr fun h' => absurd h' hs
    exact e1.trans_le zero_le

theorem lintegral_eq_cutoff {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
    (h : QuotientSetting G S μG μS ν) (φ : MtM m → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∀ x : MtM m, Matrix.of x ∈ G →
      ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1)
    (F : MtM m → ℝ≥0∞) (hF : Measurable F)
    (hFS : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  have hνG := ae_mem_of_quot h
  obtain ⟨hG, hS, hSG, hHG, hHS, hRG, hRS, hQ⟩ := h
  rw [hQ (fun x => φ x * F x) (hφ.mul hF)]
  refine lintegral_congr_ae ?_
  filter_upwards [hνG] with x hx
  have hSae : ∀ᵐ s ∂μS, Matrix.of s ∈ S := ae_iff.mpr hHS.2.2.1
  have e : ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) *
        F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS
      = ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) * F x ∂μS := by
    refine lintegral_congr_ae ?_
    filter_upwards [hSae] with s hs
    rw [hFS _ hs x hx]
  rw [e, lintegral_mul_const (f := fun s : MtM m => φ (fun i j => (Matrix.of s * Matrix.of x) i j)) _
    (hφ.comp (measurable_mul_left x)), hφ1 x hx, one_mul]

theorem quotInv : PI.QuotInv := by
  intro m G S μG μS ν h F hF hFS g hg
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_normalised_cutoff' m G S μS h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1
  have hG : IsMatGroup G := h.1
  have hxg : ∀ x : MtM m, Matrix.of x ∈ G →
      Matrix.of (fun i j => (Matrix.of x * g) i j : MtM m) ∈ G := fun x hx => hG.2.2.1 _ hx _ hg
  have hφ' : Measurable (fun x : MtM m => φ (fun i j => (Matrix.of x * g) i j)) :=
    hφ.comp (measurable_rmulQ g)
  have hφ'1 : ∀ x : MtM m, Matrix.of x ∈ G →
      ∫⁻ s, (fun x : MtM m => φ (fun i j => (Matrix.of x * g) i j))
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
    intro x hx
    rw [← hφ1 _ (hxg x hx)]
    refine lintegral_congr fun s => ?_
    show φ _ = φ _
    congr 1
    change (Matrix.of s * Matrix.of x) * g = Matrix.of s * (Matrix.of x * g)
    exact Matrix.mul_assoc _ _ _
  have hFg : Measurable (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) :=
    hF.comp (measurable_rmulQ g)
  have hFgS : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G →
      (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) (fun i j => (s * Matrix.of x) i j) =
        (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) x := by
    intro s hs x hx
    have key := hFS s hs _ (hxg x hx)
    refine Eq.trans ?_ key
    show F _ = F _
    congr 1
    change (s * Matrix.of x) * g = s * (Matrix.of x * g)
    exact Matrix.mul_assoc _ _ _
  have e1 := lintegral_eq_cutoff h _ hφ' hφ'1 _ hFg hFgS
  have e2 := lintegral_eq_cutoff h φ hφ hφ1 F hF hFS
  refine e1.trans (Eq.trans ?_ e2.symm)
  calc ∫⁻ x, φ (fun i j => (Matrix.of x * g) i j) * F (fun i j => (Matrix.of x * g) i j) ∂μG
      = ∫⁻ x, (fun y => φ y * F y) (rmulQ g x) ∂μG := rfl
    _ = ∫⁻ x, (fun y => φ y * F y) x ∂(μG.map (rmulQ g)) :=
        (lintegral_map (hφ.mul hF) (measurable_rmulQ g)).symm
    _ = ∫⁻ x, φ x * F x ∂μG := by rw [h.2.2.2.2.2.1 g hg]

end GlobalTheory.QuotRightInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariantStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_right_invariant : PI.QuotInv := by
  first | exact @GlobalTheory.QuotRightInv.quotInv | exact GlobalTheory.QuotRightInv.quotInv | (intros; apply GlobalTheory.QuotRightInv.quotInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnits
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_expand_units {n : ℕ} (Q Y : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) :
    Y = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have h2 : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q)
      = Q⁻¹ * (∑ a, ∑ b, Matrix.single a b ((Q * Y * Q⁻¹) a b)) * Q := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h2, ← Matrix.matrix_eq_sum_single]
  calc Y = (Q⁻¹ * Q) * Y * (Q⁻¹ * Q) := by rw [h1]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_units_mul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = (if b = c then (1 : ℂ) else 0) • (Q⁻¹ * Matrix.single a d (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have : (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = Q⁻¹ * (Matrix.single a b (1 : ℂ) * (Q * Q⁻¹) * Matrix.single c d (1 : ℂ)) * Q := by
    simp only [Matrix.mul_assoc]
  rw [this, h1, Matrix.mul_one]
  by_cases h : b = c
  · subst h
    simp [Matrix.single_mul_single_same]
  · simp [h, Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem dC_expand_units : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  intro hK k r ε mu R hR Q E hQ hE
  obtain ⟨-, -, hlin, hX, hbr, -⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hL : ∀ v : R.smSub, ∃ L : Mx k r →ₗ[ℂ] R.H, ∀ Y, L Y = R.dC Y v := by
    intro v
    have hv : (v : R.H) ∈ R.sm := v.2
    have h0 : R.dC 0 v = 0 := by
      have := hlin 0 0 1 v hv
      simpa using this
    refine ⟨{ toFun := fun Y => R.dC Y v, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro Y Z
      simpa using hlin Y Z 1 v hv
    · intro a Y
      simpa [h0] using hlin Y 0 a v hv
  have hexp : ∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
    intro Y v
    obtain ⟨L, hLv⟩ := hL v
    rw [← hLv]
    conv_lhs => rw [conj_expand_units Q Y hQ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
    simp only [hLv, hE _ _ v]
  refine ⟨?_, hexp, fun X hXl v => ?_⟩
  · intro a b c d
    ext v
    obtain ⟨L, hLv⟩ := hL v
    have := hbr (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v v.2
    rw [conj_units_mul Q hQ, conj_units_mul Q hQ, ← hLv (_ - _), map_sub, map_smul, map_smul, hLv, hLv,
      ← hE, ← hE, ← hE, ← hE, ← hE, ← hE] at this
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [this]
    congr 1 <;> split_ifs <;> simp_all
  · rw [← hX X hXl v v.2, hexp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnitsStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedAction_expand_matrixUnits : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  first | exact @GlobalTheory.dC_expand_units | exact GlobalTheory.dC_expand_units | (intros; apply GlobalTheory.dC_expand_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HcParamSubIntegral
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

theorem hcParam_sub_integral : ∀ (n : ℕ) (lam lam' : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.IsHCParam lam' → ∃ ν : Fin n → ℤ, lam' = (fun a => lam a + (ν a : ℝ)) ∧ ((BranchingSupport.n1 ν : ℕ) : ℝ) = l1 lam' lam ∧ ∀ s, |lam' s - lam s| ≤ l1 lam' lam := by
  intro n lam lam' h h'
  choose m hm using h.2
  choose m' hm' using h'.2
  have key : ∀ a, lam' a - lam a = ((m' a - m a : ℤ) : ℝ) := by
    intro a
    push_cast
    linarith [hm a, hm' a]
  refine ⟨fun a => m' a - m a, ?_, ?_, ?_⟩
  · funext a
    linarith [key a]
  · unfold BranchingSupport.n1 l1
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a, Nat.cast_natAbs, Int.cast_abs]
  · intro s
    unfold l1
    exact Finset.single_le_sum (f := fun a => |lam' a - lam a|) (fun a _ => abs_nonneg _) (Finset.mem_univ s)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HypAndAdj
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.TypeGlModule

theorem hyp_and_adj :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ)
      (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ)
      (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)),
      inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L →
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) →
      IsFrameOf (n + 1) r [z] B →
      Hyp (EB π B) β L ∧ ∀ a b x y, inner ℂ (EB π B a b x) y = inner ℂ x (EB π B b a y) := by
  intro V _ _ _ n r z π u β L B hz hT hty hL hu hB
  obtain ⟨hnt, hrep, hcont, hunit, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨hgl, hq⟩ := Formalism.FourierDecayAlt.P.frame_general_linear V (n + 1) r (n + 1) z π B hR hB
  refine ⟨?_, fun a b x y => Formalism.FourierDecayAlt.P5.Kfp.EB_adj hrep hcont hunit hB a b x y⟩
  refine ⟨hgl, ⟨hnt, fun S hS =>
    hirr S (Formalism.FourierDecayAlt.P.lie_stabilizer V (n + 1) r z π B hz hT hR hB S hS)⟩, hL, ?_⟩
  intro w v
  rw [← hq w v, hcap B hB w v, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
  congr 1
  unfold cpol shf
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← hu j]
  ring

end GlobalTheory.TypeGlModule
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeil
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.QuotWeil

theorem measurable_mulM {m : ℕ} {α : Type} [MeasurableSpace α] {a b : α → PI.MtM m}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun t => (fun i j => (Matrix.of (a t) * Matrix.of (b t)) i j : PI.MtM m)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp ha)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hb)

theorem measurable_invM {m : ℕ} :
    Measurable (fun s : PI.MtM m => (fun i j => (Matrix.of s)⁻¹ i j : PI.MtM m)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hc : Continuous (fun s : PI.MtM m => (Matrix.of s : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  refine Measurable.mul (Measurable.inv hc.matrix_det.measurable) ?_
  exact (hc.matrix_adjugate.matrix_elem i j).measurable

theorem unfold_abstract {X : Type} [MeasurableSpace X] (mu : X → X → X) (iv : X → X)
    (hmu : Measurable (fun p : X × X => mu p.1 p.2)) (hiv : Measurable iv)
    (μG μS : Measure X) [SFinite μG] [SFinite μS]
    (hleft : ∀ᵐ s ∂μS, μG.map (mu s) = μG ∧ ∀ x, mu (iv s) (mu s x) = x)
    (hinv : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ s, f (iv s) ∂μS = ∫⁻ s, f s ∂μS)
    (φ : X → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∀ᵐ x ∂μG, ∫⁻ s, φ (mu s x) ∂μS = 1)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (mu s x) ∂μS) ∂(μG.withDensity φ) := by
  have hl : ∀ s, Measurable (mu s) := fun s => hmu.comp (measurable_const.prodMk measurable_id)
  have hr : ∀ x, Measurable (fun s => mu s x) := fun x =>
    hmu.comp (measurable_id.prodMk measurable_const)
  have h1 : Measurable (fun p : X × X => f (mu p.2 p.1)) := hf.comp (hmu.comp measurable_swap)
  have h2 : Measurable (fun p : X × X => φ (mu (iv p.1) p.2) * f p.2) :=
    (hφ.comp (hmu.comp ((hiv.comp measurable_fst).prodMk measurable_snd))).mul
      (hf.comp measurable_snd)
  have hF : Measurable (fun x : X => ∫⁻ s, f (mu s x) ∂μS) := h1.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hF]
  symm
  calc ∫⁻ x, (φ * fun x : X => ∫⁻ s, f (mu s x) ∂μS) x ∂μG
      = ∫⁻ x, ∫⁻ s, φ x * f (mu s x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, lintegral_const_mul]
        exact hf.comp (hr x)
    _ = ∫⁻ s, ∫⁻ x, φ x * f (mu s x) ∂μG ∂μS :=
        lintegral_lintegral_swap ((hφ.comp measurable_fst).mul h1).aemeasurable
    _ = ∫⁻ s, ∫⁻ y, φ (mu (iv s) y) * f y ∂μG ∂μS := by
        refine lintegral_congr_ae (hleft.mono fun s hs => ?_)
        have hm : Measurable (fun y : X => φ (mu (iv s) y) * f y) :=
          (hφ.comp (hl _)).mul hf
        beta_reduce
        conv_rhs => rw [← hs.1, lintegral_map hm (hl s)]
        refine lintegral_congr fun x => ?_
        rw [hs.2]
    _ = ∫⁻ y, ∫⁻ s, φ (mu (iv s) y) * f y ∂μS ∂μG := lintegral_lintegral_swap h2.aemeasurable
    _ = ∫⁻ y, f y ∂μG := by
        refine lintegral_congr_ae (hφ1.mono fun y hy => ?_)
        have hm : Measurable (fun s : X => φ (mu s y)) := hφ.comp (hr y)
        have hm' : Measurable (fun s : X => φ (mu (iv s) y)) := hm.comp hiv
        have := hinv _ hm
        beta_reduce at this ⊢
        rw [lintegral_mul_const _ hm', this, hy, one_mul]

theorem exists_isQuotM : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS : Measure (PI.MtM m)),
    PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM G μG → PI.IsHaarOnM S μS →
    PI.IsRightInvM S μS → ∃ ν, PI.IsQuotM μG μS ν := by
  intro m G S μG μS hG hS hSG hμG hμS hR
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_normalised_cutoff' m G S μS hG hS hSG hμS hR
  have hinv := GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup m S μS hS hμS hR
  haveI := hμG.1
  haveI := hμS.1
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ S := by rw [ae_iff]; exact hμS.2.2.1
  have haeG : ∀ᵐ s ∂μG, Matrix.of s ∈ G := by rw [ae_iff]; exact hμG.2.2.1
  refine ⟨μG.withDensity φ, fun f hf => ?_⟩
  refine unfold_abstract (fun s x : PI.MtM m => fun i j => (Matrix.of s * Matrix.of x) i j)
    (fun s i j => (Matrix.of s)⁻¹ i j) (measurable_mulM measurable_fst measurable_snd)
    measurable_invM μG μS (haeS.mono fun s hs => ⟨hμG.2.2.2 _ (hSG hs), fun x => ?_⟩) hinv φ hφ
    (haeG.mono fun x hx => hφ1 x hx) f hf
  have hs1 : (Matrix.of s)⁻¹ * Matrix.of s = 1 := mul_eq_one_comm.1 (hS.2.2.2 _ hs).2
  change (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) = Matrix.of x
  rw [← Matrix.mul_assoc, hs1, Matrix.one_mul]

end GlobalTheory.QuotWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeilStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotientMeasure_weil : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM G μG → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ ν, PI.IsQuotM μG μS ν := by
  first | exact @GlobalTheory.QuotWeil.exists_isQuotM | exact GlobalTheory.QuotWeil.exists_isQuotM | (intros; apply GlobalTheory.QuotWeil.exists_isQuotM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslatePullbackEigensection
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelEigen

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem sval_act {n : ℤ} {θ : ThetaGrp A L n T} {s s' : LB.Sec (LPow A L n T)} (H : IsActOf A L n θ s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J) (hJ : Good L z J) :
    sval s' r z J = (tval θ r z J).val * sval s (r ≫ (translT A θ.pt).left) z J := by
  have l₁ := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _)
  let j : Fin 2 → L.ι := fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)
  have hz : r z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j := hJ.mem _ r
  have e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  rw [sval_of s _ z J (fun _ => j 1) (fun _ => by rw [Category.assoc, e]; rfl)]
  exact (gs_res r z (chart_le_zero A L _ j) hz _).symm.trans ((congrArg (gs r z _) (H j)).trans
    ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _)
      ((gs_res r z (l₁ j) hz _).trans (gs_pull r (translT A θ.pt).left z
        (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (l₁ j hz) _)))))

theorem translT_snd_comp (a : A ⟶ A) [IsMonHom a] {c : T ⟶ A} (hc : c ≫ a = 1) :
    translT A c ≫ snd T A ≫ a = snd T A ≫ a := by
  rw [← Category.assoc, translT, lift_snd]
  show ((fst T A ≫ c) * snd T A) ≫ a = _
  rw [MonObj.mul_comp, Category.assoc, hc, MonObj.comp_one, _root_.one_mul]

theorem translT_whisker (a : A ⟶ A) [IsMonHom a] {c : T ⟶ A} (hc : c ≫ a = 1) :
    translT A c ≫ T ◁ a = T ◁ a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, whiskerLeft_snd, translT_snd_comp a hc]

theorem translT_comm [IsCommMonObj A] (x y : T ⟶ A) : translT A x ≫ translT A y = translT A y ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Category.assoc, H1.transl_snd]
    exact H1.transl_comm x y

theorem exists_kernel_lift (hL : L.IsLB) (a : A ⟶ A) [IsMonHom a] {m k : ℤ}
    (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ≫ a).left] ![m, -k])) (hmu : mu.IsGen)
    {c : T ⟶ A} (hc : c ≫ a = 1) :
    ∃ θ : ThetaGrp A L m T, θ.pt = c ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θ r z J = val mu r z J * (val mu (r ≫ (translT A c).left) z J)⁻¹ := by
  have e₀ : (translT A c).left ≫ (snd T A).left = (translPt A c).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have e₁ : (translT A c).left ≫ (snd T A ≫ a).left = (snd T A ≫ a).left := by
    rw [← Over.comp_left, translT_snd_comp a hc]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A c).left]) (ε' := ![m, -m])
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁,
        zpow_neg, inv_inv, Pi.neg_apply]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ mu (LB.invGen L _ _ (LB.pullGen L _ _ mu (translT A c).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hmu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hmu _)))
  refine ⟨⟨c, u, hu⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  rw [val_mul hJ, val_inv, val_pull hJ]

theorem commIsOf_of_weilIs (hL : L.IsLB) [Unique T.left] {n : ℤ} (θx θy : ThetaGrp A L n T)
    {e : Γ(T.left, ⊤)ˣ} (H : WeilIs A L n θx.pt θy.pt e) : CommIsOf A L n θx θy e := by
  obtain ⟨V, hV, -, H⟩ := H default
  obtain rfl : V = ⊤ := top_le_iff.1 fun x _ => by rw [Subsingleton.elim x default]; exact hV
  let h := overResι (T := T) ⊤
  have : IsIso h.left := inferInstanceAs (IsIso (Scheme.topIso T.left).hom)
  have : IsIso ((Over.forget S).map h) := this
  have : IsIso h := isIso_of_reflects_iso h (Over.forget S)
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1 (H θx' θy' hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  obtain ⟨r', rfl⟩ : ∃ r' : Z ⟶ (overRes (T := T) ⊤ ⊗ A).left, r = r' ≫ (h ▷ A).left :=
    ⟨r ≫ (inv (h ▷ A)).left, by rw [Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.comp_id]⟩
  have t : ∀ x : T ⟶ A, (r' ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r' ≫ (h ▷ A).left) ≫ (translT A x).left := fun x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (r' ≫ (fst (overRes (T := T) ⊤) A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom e) =
      gm ((r' ≫ (h ▷ A).left) ≫ (fst T A).left) z ⊤ e := by
    refine (gm_pull (r' ≫ (fst (overRes (T := T) ⊤) A).left) h.left z ⊤ trivial e).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  have := H' Z r' z J hJ
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t] at this
  exact this.trans (congrArg _ g)

end GlobalTheory.KernelEigen

namespace GlobalTheory


open KernelEigen CommPairing in
theorem translate_pullback_eigensection : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (K : Type) [Field K] (p : Spec (CommRingCat.of K) ⟶ S) (a : A ⟶ A), IsMonHom a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk p) A).left, (snd (Over.mk p) A ≫ a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)])), mu.IsGen → ∀ (s : LB.Sec (LPow A L (k : ℤ) (Over.mk p))) (t' t : LB.Sec (LPow A L ((k * N : ℕ) : ℤ) (Over.mk p))), (∀ (z : (Over.mk p ⊗ A).left) (J), Good L z J → sval t' (𝟙 _) z J = (val mu (𝟙 _) z J).val * sval s (Over.mk p ◁ a).left z J) → ∀ θ : ThetaGrp A L ((k * N : ℕ) : ℤ) (Over.mk p), IsActOf A L ((k * N : ℕ) : ℤ) θ t' t → ∀ (c : Over.mk p ⟶ A) (e : Γ((Over.mk p).left, ⊤)ˣ), c ≫ a = 1 → WeilIs A L ((k * N : ℕ) : ℤ) c θ.pt e → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk p ⊗ A).left) (z : Z) (J), Good L z J → sval t (r ≫ (translT A c).left) z J * (val mu r z J).val = gs (r ≫ (fst (Over.mk p) A).left) z ⊤ e.val * (sval t r z J * (val mu (r ≫ (translT A c).left) z J).val) := by
  intro S A _ _ L hL K _ p a ha N k mu hmu s t' t ht' θ hθ c e hc hW Z r z J hJ
  haveI : Unique (Over.mk p).left := inferInstanceAs (Unique (PrimeSpectrum K))
  obtain ⟨θc, rfl, hv⟩ := exists_kernel_lift hL a mu hmu hc
  have hC := (commIsOf_iff hL _ _ _).1 (commIsOf_of_weilIs hL θc θ hW) Z r z J hJ
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.Tor.secRel_iff hL _ _ t' _ _ s (Over.mk p ◁ a).left _ _ mu
  have ht := hs.1 (hs.2 fun y J hJ => by rw [ht' y J hJ, Category.id_comp, _root_.mul_comm])
  have e₁ : (r ≫ (translT A θc.pt).left) ≫ (translT A θ.pt).left =
      (r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, translT_comm]
  have e₂ : ((r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left) ≫ (Over.mk p ◁ a).left =
      (r ≫ (translT A θ.pt).left) ≫ (Over.mk p ◁ a).left := by
    rw [Category.assoc, ← Over.comp_left, translT_whisker a hc]
  rw [sval_act hθ _ z J hJ, sval_act hθ _ z J hJ, e₁, ht _ _ z J hJ, ht _ _ z J hJ, e₂,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_unit _ z ⊤ trivial]
  rw [hv _ _ z J hJ, hv _ _ z J hJ] at hC
  generalize tval θ (r ≫ (translT A θc.pt).left) z J = x₁ at hC ⊢
  generalize tval θ r z J = x₂ at hC ⊢
  generalize val mu ((r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left) z J = x₃ at hC ⊢
  generalize val mu (r ≫ (translT A θ.pt).left) z J = x₄ at hC ⊢
  generalize val mu (r ≫ (translT A θc.pt).left) z J = x₅ at hC ⊢
  generalize val mu r z J = x₆ at hC ⊢
  generalize ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm (r ≫ (fst (Over.mk p) A).left) z ⊤ e = x₇ at hC ⊢
  have key : x₁ * x₃ * x₆ = x₇ * x₂ * x₄ * x₅ := by
    apply Additive.ofMul.injective
    have a₀ := congrArg Additive.ofMul hC
    simp only [ofMul_mul, ofMul_inv] at a₀ ⊢
    linear_combination (norm := abel) a₀
  have key' := congrArg Units.val key
  simp only [Units.val_mul] at key'
  linear_combination (sval s ((r ≫ (translT A θ.pt).left) ≫ (Over.mk p ◁ a).left) z J) * key'

end GlobalTheory
end
end
