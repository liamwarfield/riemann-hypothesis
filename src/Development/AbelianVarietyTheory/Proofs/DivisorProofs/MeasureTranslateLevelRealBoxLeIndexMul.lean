module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVecEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumLengthMulLogCardEqNegLogAdicAbvNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolBox

variable {D : D7}

theorem rp_eq_one (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (k : GA D V) (hk : k ∈ GfC V) : rp k = 1 := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  have h1 : infMat D.sp.cm.sig V.gram (θ ρ) k = 1 := by
    have h2 := congrArg Units.val ((MonoidHom.mem_ker).1 hk)
    show (Units.val (infHom V k)).map (θ ρ) = 1
    rw [h2]
    simp
  rw [hrp, h1, Pi.one_apply, GlobalTheory.Mem.VolExists.mat_one, Matrix.one_mul, Matrix.mul_one]

theorem rp_realElt (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (b : ∀ ρ, Upq V ρ) :
    rp (realElt θ V fun ρ => realMat V A ρ (b ρ)) = b := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D ρ))).2.2 (A ρ) (hA ρ)
  have e : UpqT.mat (b ρ) * A ρ = A ρ * (C * (UpqT.mat (b ρ) * A ρ)) := by
    rw [← Matrix.mul_assoc (A ρ), h1, Matrix.one_mul]
  rw [hrp, GlobalTheory.RealBoxMeasure.infMat_realElt θ hθ V _ (fun τ => GlobalTheory.RealBoxMeasure.realMat_mem V hV A hA τ _) ρ,
    GlobalTheory.RealBoxMeasure.realMat_of V A hA ρ _ _ e, ← e]

theorem exists_fin (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (h : GA D V) :
    ∃ k : GA D V, rp k = 1 ∧ finE V k = finE V h := by
  refine ⟨(realElt θ V fun ρ => realMat V A ρ (rp h ρ))⁻¹ * h, ?_, ?_⟩
  · rw [map_mul, map_inv, rp_realElt V θ A rp hV hθ hA hrp, inv_mul_cancel]
  · rw [map_mul, map_inv, GlobalTheory.RealBoxMeasure.finE_realElt, inv_one, one_mul]

theorem meas_level (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ))
    (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V))
    (hV : V.SigOK) (hθ : IsInfFam θ) (hA : IsFrames V A) (hm : ∀ ρ, IsMinf (m ρ)) (hc : Continuous rp)
    (hrp : IsRealPart V θ A rp) (hK : IsOpen {h : GA D V | finE V h ∈ K}) (hμ : IsMeasLev V K μ)
    (B : Set (∀ ρ, Upq V ρ)) (hB : MeasurableSet B) :
    μ {h | finE V h ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hsc
  haveI := hbo
  have hBm : MeasurableSet (rp ⁻¹' B) := hc.measurable hB
  have H := GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi D θ hθ V hV K μ hμ A hA m hm
    ((rp ⁻¹' B).indicator 1) (measurable_one.indicator hBm) (fun g k hk => by
      have : rp (g * k) = rp g := by rw [map_mul, rp_eq_one V θ A rp hV hA hrp k hk.1, mul_one]
      exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, this, Set.mem_preimage]) rfl) hK.measurableSet
  rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm] at H
  rw [← lintegral_indicator_one hB, show {h | finE V h ∈ K ∧ rp h ∈ B} = rp ⁻¹' B ∩ {h : GA D V | finE V h ∈ K} from
    Set.ext fun h => and_comm, H]
  refine lintegral_congr fun b => ?_
  exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, rp_realElt V θ A rp hV hθ hA hrp]) rfl

theorem meas_translate_le : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → K ≤ K₀ → K.relIndex K₀ ≠ 0 → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  intro D V θ A m rp K K₀ μ hV hθ hA hm hc hrp _ hi hK hμ g _ B hB
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hμ.1
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hi⟩
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  let S : (K₀ ⧸ K.subgroupOf K₀) → Set (GA D V) := fun q =>
    {h | (∃ hh : finE V (g⁻¹ * h) ∈ K₀, (QuotientGroup.mk ⟨_, hh⟩ : K₀ ⧸ K.subgroupOf K₀) = q) ∧ rp h ∈ B}
  have hS : ∀ q, μ (S q) ≤ Measure.pi m B := by
    intro q
    rcases (S q).eq_empty_or_nonempty with h0 | ⟨h₀, ⟨hh₀, hq₀⟩, -⟩
    · rw [h0, measure_empty]; exact zero_le
    obtain ⟨k, hk1, hk2⟩ := exists_fin V θ A rp hV hθ hA hrp h₀
    rw [← meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB, ← measure_preimage_mul μ k⁻¹ {h | finE V h ∈ K ∧ rp h ∈ B}]
    refine measure_mono ?_
    rintro h ⟨⟨hh, hq⟩, hb⟩
    have h1 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hq₀.trans hq.symm))
    show finE V (k⁻¹ * h) ∈ K ∧ rp (k⁻¹ * h) ∈ B
    refine ⟨?_, ?_⟩
    · have h2 : finE V (k⁻¹ * h) = (finE V (g⁻¹ * h₀))⁻¹ * finE V (g⁻¹ * h) := by
        simp only [map_mul, map_inv, hk2]; group
      rw [h2]; exact h1
    · rwa [map_mul, map_inv, hk1, inv_one, one_mul]
  calc μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ μ (⋃ q, S q) :=
        measure_mono fun h hh => Set.mem_iUnion.2 ⟨_, ⟨hh.1, rfl⟩, hh.2⟩
    _ ≤ ∑ q, μ (S q) := measure_iUnion_fintype_le μ S
    _ ≤ ∑ _q : K₀ ⧸ K.subgroupOf K₀, Measure.pi m B := Finset.sum_le_sum fun q _ => hS q
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

end GlobalTheory.CovTop.VolBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_translateLevel_realBox_le_index_mul : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → K ≤ K₀ → K.relIndex K₀ ≠ 0 → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  first | exact @GlobalTheory.CovTop.VolBox.meas_translate_le | exact GlobalTheory.CovTop.VolBox.meas_translate_le | (intros; apply GlobalTheory.CovTop.VolBox.meas_translate_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicProperties
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThKBasic

theorem thetaBasic : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ThetaBasic := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hS := hP.weil.isUSplitting
  obtain ⟨l, hl, hlt⟩ := GlobalTheory.T.exists_admissibleForm_adelicThetaSum F (Fin n × Fin d)
  refine ⟨fun Φ hΦ => ⟨?_, ?_, GlobalTheory.T.theta_moderate_growth_height hKP F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ⟩, ?_⟩
  · refine (hS.cont l hl Φ hΦ).congr fun x => ?_
    simp only [theta]
    exact hlt _ (hS.pres _ _ hΦ)
  · intro γ hγ γ' hγ' g h
    simp only [theta]
    have e : om (γ * g, γ' * h) Φ = om (γ, γ') (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; rfl
    rw [e]
    exact GlobalTheory.T.thetaSum_invariant_rational_unitary hKP F E σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' _ (hS.pres _ _ hΦ)
  · intro φ hφ g h
    obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
    refine T.continuous.congr fun f => ?_
    simp only [theta]
    have hm : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) φ ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    rw [← hlt _ (hS.pres _ _ hm)]
    exact (hT f).symm

end GlobalTheory.ThKBasic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_basic_properties : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ThetaBasic := by
  first | exact @GlobalTheory.ThKBasic.thetaBasic | exact GlobalTheory.ThKBasic.thetaBasic | (intros; apply GlobalTheory.ThKBasic.thetaBasic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectio
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.Proj

variable {p q r : ℕ}

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem det_Jpq_ne (p q : ℕ) : (Formalism.UG.Jpq p q).det ≠ 0 := by
  rw [Jpq_eq_diagonal, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rcases i with i | i <;> simp

theorem star_det_mul_det (u : UpqT p q) : star (UpqT.mat u).det * (UpqT.mat u).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqExpChart.mat_unitary u)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := det_Jpq_ne p q
  apply mul_left_cancel₀ hJ
  linear_combination h

theorem det_mat_ne (u : UpqT p q) : (UpqT.mat u).det ≠ 0 := by
  intro h
  have := star_det_mul_det u
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem dg_unitary (a₀ : Fin p ⊕ Fin q) (z : ℂ) (hz : star z * z = 1) :
    (dg a₀ z)ᴴ * Formalism.UG.Jpq p q * dg a₀ z = Formalism.UG.Jpq p q := by
  rw [Jpq_eq_diagonal, dg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = a₀
  · subst h
    simp only [Pi.star_apply, Function.update_self]
    linear_combination (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i) * hz
  · simp [Function.update_of_ne h]

theorem det_sMat (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : (sMat a₀ u).det = 1 := by
  rw [sMat, Matrix.det_mul, det_dg, mul_inv_cancel₀ (det_mat_ne u)]

theorem sMat_unitary (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) :
    (sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u = Formalism.UG.Jpq p q := by
  have hz : star (UpqT.mat u).det⁻¹ * (UpqT.mat u).det⁻¹ = 1 := by
    rw [star_inv₀, ← mul_inv, star_det_mul_det, inv_one]
  have h1 := GlobalTheory.UpqExpChart.mat_unitary u
  have h2 := dg_unitary a₀ _ hz
  calc _ = (dg a₀ (UpqT.mat u).det⁻¹)ᴴ * ((UpqT.mat u)ᴴ * Formalism.UG.Jpq p q * UpqT.mat u) *
        dg a₀ (UpqT.mat u).det⁻¹ := by
        simp only [sMat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem continuous_sMat (a₀ : Fin p ⊕ Fin q) : Continuous (sMat a₀ : UpqT p q → _) := by
  unfold sMat dg
  refine GlobalTheory.UpqExpChart.continuous_mat.matrix_mul (Continuous.matrix_diagonal ?_)
  exact continuous_const.update a₀
    (GlobalTheory.UpqExpChart.continuous_mat.matrix_det.inv₀ det_mat_ne)

theorem sMat_mul (a₀ : Fin p ⊕ Fin q) (u v : UpqT p q) (hu : (UpqT.mat u).det = 1) :
    sMat a₀ (u * v) = UpqT.mat u * sMat a₀ v := by
  have h : UpqT.mat (u * v) = UpqT.mat u * UpqT.mat v := rfl
  rw [sMat, sMat, h, Matrix.det_mul, hu, one_mul, Matrix.mul_assoc]

theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) (A : Matrix ι (Fin r) ℂ)
    (B : Matrix (Fin r) ι ℂ) (hAB : A * B = 1) (S : Matrix ι ι ℂ) : (B * S * A).det = S.det := by
  have h1 : (B * S * A).submatrix e e = B.submatrix e id * S * A.submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  have h2 : A.submatrix id e * B.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, hAB]
    rfl
  rw [← Matrix.det_submatrix_equiv_self e, h1, Matrix.det_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

def gl (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (u : UpqT p q) : GL (Fin r) ℂ where
  val := B * sMat a₀ u * A
  inv := B * (sMat a₀ u).adjugate * A
  val_inv := by
    calc _ = B * (sMat a₀ u * (A * B) * (sMat a₀ u).adjugate) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.mul_adjugate, det_sMat, one_smul, Matrix.mul_one, hBA]
  inv_val := by
    calc _ = B * ((sMat a₀ u).adjugate * (A * B) * sMat a₀ u) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.adjugate_mul, det_sMat, one_smul, Matrix.mul_one, hBA]

section
variable (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1)

theorem gl_val (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = B * sMat a₀ u * A := rfl

theorem continuous_gl : Continuous (gl a₀ A B hAB hBA) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_const.matrix_mul (continuous_sMat a₀)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul (continuous_sMat a₀).matrix_adjugate).matrix_mul continuous_const

theorem mul_gl (u : UpqT p q) :
    A * (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = sMat a₀ u * A := by
  rw [gl_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul]

theorem gl_keeps (H : Matrix (Fin r) (Fin r) ℂ) (hH : Aᴴ * Formalism.UG.Jpq p q * A = -Hᵀ) (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ)ᵀ * H *
      (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = H := by
  have hm := mul_gl a₀ A B hAB hBA u
  generalize (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = g at hm ⊢
  have h : gᴴ * (-Hᵀ) * g = -Hᵀ := by
    calc _ = (A * g)ᴴ * Formalism.UG.Jpq p q * (A * g) := by
          rw [← hH]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Aᴴ * ((sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u) * A := by
          rw [hm]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [sMat_unitary, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h'
  exact h'

end

theorem exists_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)), IsIdent p q Ψ G x σ A e → ∃ π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G, Continuous π ∧ IsProj p q Ψ G σ A a₀ π ∧ (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ hI
  let B : ∀ ρ, Matrix (Fin r) (Fin (p ρ) ⊕ Fin (q ρ)) ℂ := fun ρ => mat x (σ ρ) * (permM (e ρ))ᵀ
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ => by
    simp only [B]
    rw [← Matrix.mul_assoc, (hI ρ).2, permM_mul_transpose]
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv (e ρ)).1 (hAB ρ)
  let F : (∀ ρ, UpqT (p ρ) (q ρ)) → κ → GL (Fin r) ℂ :=
    fun b ρ => gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ)
  have hF : ∀ b ρ, F b (σ.symm (σ ρ)) = gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ) := fun b ρ => by
    rw [Equiv.symm_apply_apply]
  have hmem : ∀ b, (fun τ => F b (σ.symm τ)) ∈ realSU Ψ G := fun b => by
    rw [DensOne.mem_realSU_iff]
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    simp only [hF]
    exact ⟨gl_keeps _ _ _ _ _ _ (hI ρ).1 _, by rw [gl_val, det_conj (e ρ) _ _ (hAB ρ), det_sMat]⟩
  refine ⟨fun b => ⟨_, hmem b⟩, ?_, ?_, ?_⟩
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    exact (continuous_gl _ _ _ _ _).comp (continuous_apply _)
  · intro b ρ
    simp only [hF]
    exact mul_gl _ _ _ _ _ _
  · intro s b₀ hs b
    refine Subtype.ext (funext fun τ => ?_)
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    apply Units.ext
    change ((F (b₀ * b) (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (s.1 (σ ρ) : GL (Fin r) ℂ) * ((F b (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    have h1 : ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B ρ * UpqT.mat (b₀ ρ) * A ρ := by
      rw [Matrix.mul_assoc, hs ρ, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
    have h2 : (UpqT.mat (b₀ ρ)).det = 1 := by
      rw [← det_conj (e ρ) _ _ (hAB ρ), ← h1]
      exact (((DensOne.mem_realSU_iff Ψ G _).1 s.2) (σ ρ)).2
    rw [hF, hF, gl_val, gl_val, h1, Pi.mul_apply, sMat_mul _ _ _ h2]
    calc _ = B ρ * UpqT.mat (b₀ ρ) * (A ρ * B ρ) * sMat (a₀ ρ) (b ρ) * A ρ := by
          rw [hAB]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CovTop.VolUp.Proj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectioStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)), IsIdent p q Ψ G x σ A e → ∃ π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G, Continuous π ∧ IsProj p q Ψ G σ A a₀ π ∧ (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) := by
  first | exact @GlobalTheory.CovTop.VolUp.Proj.exists_proj | exact GlobalTheory.CovTop.VolUp.Proj.exists_proj | (intros; apply GlobalTheory.CovTop.VolUp.Proj.exists_proj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp

theorem fdgram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = (xᴴ * (G.map τ)ᵀ * x)ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp [RCLike.star_def]
  ring

theorem permM_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) :
    (permM e)ᴴ * M * permM e = M.submatrix e.symm e.symm := by
  ext a b
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← e.symm.sum_comp]
  simp

theorem jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)) := by
  rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, ← Matrix.diagonal_neg]
  rfl

theorem sumElim_sgn {p q r : ℕ} (hcard : r = q + p) (a : Fin r) :
    Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)
        (((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a) =
      -(((sgn q (a : ℕ) : ℝ)) : ℂ) := by
  by_cases h : (a : ℕ) < q
  · have ha : finCongr hcard a = Fin.castAdd p ⟨a, h⟩ := Fin.ext rfl
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inr ⟨a, h⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [hv]
    simp [sgn, h]
  · have hlt := a.isLt
    have ha : finCongr hcard a = Fin.natAdd q ⟨(a : ℕ) - q, by omega⟩ := Fin.ext (by simp; omega)
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inl ⟨(a : ℕ) - q, by omega⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [hv]
    simp [sgn, h]

theorem exists_frame_of_sig {n p q : ℕ} {Gc : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature Gc p q)
    {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq p q * A = Gc) :
    ∃ (e : Fin p ⊕ Fin q ≃ Fin n) (x : Matrix (Fin n) (Fin n) ℂ), x.det ≠ 0 ∧ A * x = permM e ∧
      (-(xᴴ * Gc * x))ᵀ = Matrix.diagonal fun a : Fin n => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨L, hl, hr⟩ := GlobalTheory.DecompCompare.frame_inv h hA
  obtain ⟨e0, -⟩ := h
  have hcard : n = q + p := by
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  set π : Fin n ≃ Fin p ⊕ Fin q :=
    (finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p))) with hπ
  have hAx : A * (L * permM π.symm) = permM π.symm := by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  refine ⟨π.symm, L * permM π.symm, ?_, hAx, ?_⟩
  · have h1 : (L * permM π.symm) * ((permM π.symm)ᵀ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permM π.symm), permM_mul_transpose, Matrix.one_mul, hl]
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  · have key : ∀ y : Matrix (Fin n) (Fin n) ℂ, yᴴ * Gc * y = (A * y)ᴴ * Formalism.UG.Jpq p q * (A * y) := fun y => by
      rw [← hA, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [key, hAx, permM_conj, Equiv.symm_symm, jpq_eq_diagonal, Matrix.submatrix_diagonal_equiv,
      Matrix.diagonal_neg, Matrix.diagonal_transpose]
    congr 1
    funext a
    rw [Function.comp_apply, hπ, sumElim_sgn hcard a, neg_neg]

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem exists_ident_frame : ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) →
    ∀ A : Frames V, IsFrames V A → ∃ (X₀ : Data D.host.E V.rank) (σ : D.what₂.Tau ≃ X₀.Ψ) (x : Frame X₀.Ψ V.rank)
      (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank),
      X₀.Gm = -(V.gram)ᵀ ∧ (∀ ρ, (σ ρ).1 = tauE D ρ) ∧ IsOrth X₀ x ∧
        IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) X₀.Ψ X₀.Gm x σ A e := by
  intro D V P Q hV hs A hA
  choose e x hdet hAx hg using fun ρ => exists_frame_of_sig (hV (tauE D ρ)) (hA ρ)
  have hrk : V.rank = Q + P := by
    have h := hV D.host.φ₀
    rw [hs] at h
    obtain ⟨e0, -⟩ := h
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  have hmapT : ∀ ρ, ((-(V.gram)ᵀ).map (tauE D ρ))ᵀ = -(gramAt D V ρ) := fun ρ => by
    ext a b
    simp [gramAt]
  have hgr : ∀ ρ, ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(V.gram)ᵀ) (x ρ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn Q (a : ℕ) : ℝ) : ℂ) := fun ρ => by
    have h1 := hg ρ
    simp only [hs] at h1
    rw [fdgram_eq, hmapT, Matrix.mul_neg, Matrix.neg_mul]
    exact h1
  have hin : ∀ ρ, tauE D ρ ∈ Formalism.L2.Pj.cmTypeOfSqrt D := fun ρ => by
    rw [Formalism.L2.Pj.mem_cm_type_iff, Formalism.L2.Theta.tauE_sqrtMinusD]
    exact (D.host.φ₀_mem).symm
  have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ Formalism.L2.Pj.cmTypeOfSqrt D ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, hρ⟩ => hρ ▸ hin ρ⟩
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h' | h'
    · exact ⟨ρ, h'.symm⟩
    · exact absurd (h' ▸ h) ((Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D _).1 (hin ρ))
  have hinj : Function.Injective (tauE D) := fun _ _ h =>
    (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).1 (by simp only [h])
  obtain ⟨hh, hd, hfg, hsp, -⟩ := GlobalTheory.Member.selfDualLat_neg_gram_transpose D V
  obtain ⟨n, hn, hnint⟩ := GlobalTheory.PrincData.exists_nat_herm_int (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) hfg
  obtain ⟨k, hk, hkint⟩ := GlobalTheory.PrincData.exists_nat_int (-(2 * D.host.xi0))
  obtain ⟨X, hΨ, hG, hp, -, -, -, -, -, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski D.host.E V.rank Q 3
    (3 * n * k) (Formalism.L2.Pj.cmTypeOfSqrt D) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) D.host.xi0 (-(2 * D.host.xi0))
    (Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D) hh hd (by omega)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      exact ⟨x ρ, hdet ρ, hgr ρ⟩)
    hfg hsp le_rfl (Formalism.L2.Pj.conj_xi0_alt D)
    (by
      obtain ⟨ρ, -⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk D.host.φ₀)
      intro h
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      rw [h] at h1
      simp at h1)
    (Or.inr rfl)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      simp [map_ofNat]
      linarith)
    (by positivity)
    (fun u hu v hv => by
      have e1 : ((3 * n * k : ℕ) : D.host.E) / ((3 : ℕ) : D.host.E) * (-(2 * D.host.xi0)) *
          ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v =
          ((k : D.host.E) * (-(2 * D.host.xi0))) * ((n : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v) := by
        push_cast
        field_simp
      rw [e1]
      exact hkint.mul (hnint u hu v hv))
  let σ : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, by rw [hΨ]; exact hin ρ⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hmem τ.1).1 (hΨ ▸ τ.2)
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  refine ⟨X, σ, fun τ => x (σ.symm τ), e, hG, fun ρ => rfl, fun τ => ?_, fun ρ => ⟨?_, ?_⟩⟩
  · have hτ : τ.1 = tauE D (σ.symm τ) := (congrArg Subtype.val (σ.apply_symm_apply τ)).symm
    show ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (x (σ.symm τ)) = _
    rw [hG, hp, hτ]
    exact hgr _
  · rw [hA ρ, hG]
    show gramAt D V ρ = -((-(V.gram)ᵀ).map (tauE D ρ))ᵀ
    rw [hmapT, neg_neg]
  · show A ρ * x (σ.symm (σ ρ)) = permM (e ρ)
    rw [σ.symm_apply_apply]
    exact hAx ρ

end GlobalTheory.CovTop.VolUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentificationStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification : ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) → ∀ A : Frames V, IsFrames V A → ∃ (X₀ : Data D.host.E V.rank) (σ : D.what₂.Tau ≃ X₀.Ψ) (x : Frame X₀.Ψ V.rank) (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank), X₀.Gm = -(V.gram)ᵀ ∧ (∀ ρ, (σ ρ).1 = tauE D ρ) ∧ IsOrth X₀ x ∧ IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) X₀.Ψ X₀.Gm x σ A e := by
  first | exact @GlobalTheory.CovTop.VolUp.exists_ident_frame | exact GlobalTheory.CovTop.VolUp.exists_ident_frame | (intros; apply GlobalTheory.CovTop.VolUp.exists_ident_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.CoverHt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem isPreimmersion_j : IsPreimmersion V.j :=
  have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h


end GlobalTheory.Mean4O.CoverHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLattice
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FullLevel

theorem finE_mem_lev_of_isKM : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Links.IsSDFrame V β Λ 1 → V.rank ≤ L.r → L.P.H = ⊤ → ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L := by
  intro D V β Λ L hΛ hr hP h hK
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hk : GlobalTheory.Member.FinCong V 1 h := by
    intro z hz
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
    exact hK.2.1 z hz
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V 1 a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (1 : ℕ) • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap Λ 1 _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, -⟩ := GlobalTheory.PrincInLevel.exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Formalism.IndefR.Lev.finE V h)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) 1 hfr (hc h hk) hc'
  have hS : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.St β := ⟨y, hy⟩
  have hU : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := GlobalTheory.LevSplit.finE_mem_UA V h
  have hb : ∀ a : Fin V.rank, a.val < L.r := fun a => lt_of_lt_of_le a.2 hr
  refine Formalism.L2.DIV.mem_lev.2 ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hU, hS, fun PP _ => ?_, fun PP _ => ?_⟩, ?_⟩
  · intro i j hij
    exfalso
    simp only [Formalism.L2.DIV.blkOf, if_pos (hb i), if_pos (hb j)] at hij
    exact lt_irrefl _ hij
  · intro i j hij
    exfalso
    simp only [Formalism.L2.DIV.blk2, if_pos (hb i), if_pos (hb j)] at hij
    exact lt_irrefl _ hij
  · rw [hP]; exact Subgroup.mem_top _

end GlobalTheory.CovTop.VolUp.FullLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_mem_fullLevel_of_keeps_selfDualLattice : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Links.IsSDFrame V β Λ 1 → V.rank ≤ L.r → L.P.H = ⊤ → ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L := by
  first | exact @GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM | exact GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM | (intros; apply GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.SiegLev GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SiegSharpCover

theorem smoothDim {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (hk : 2 ≤ k) (hζ : IsUnit ζ) (hu : IsUnit (k : o)) : SmoothOfRelativeDimension h c.A.hom := by
  have := c.ab.smooth
  have := c.ab.geomConnected
  choose n W hW hd using H1.exists_dim c.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension h) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := S.residueField (c.A.hom y)
  let K := AlgebraicClosure κ
  let x : Sp K ⟶ S := spMap (algebraMap κ K) ≫ S.fromSpecResidueField (c.A.hom y)
  have hK : (k : K) ≠ 0 := by
    have := map_natCast (Spec.preimage (x ≫ s)).hom k
    rw [← this]
    exact (hu.map _).ne_zero
  have hp := (isGrpPullback_pullback c.A x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum K)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj c.A).hom := by change Smooth (pullback.snd c.A.hom x); infer_instance
  have : ConnectedSpace ((Over.pullback x).obj c.A).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := c.A.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj c.A).hom y'
  have e : n y = h :=
    (H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)).trans (SiegDim.dim_geometric_fibre c hk hζ hK x hd')
  have := hd y
  rwa [e] at this

end GlobalTheory.SiegSharpCover

namespace GlobalTheory.SiegSharpCover

end GlobalTheory.SiegSharpCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZer
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExtScaleZero


set_option maxHeartbeats 1000000 in
theorem exists_ext_all_models_uniformised_charZero (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (h0 : CharZero (ResidueField T.V)) :
    ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (e' : ℕ), CharZero (ResidueField T'.V) ∧ 0 < e' ∧
      (∀ I : IntData Xo c T' io' y'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso) ∧
      letI := io.toAlgebra; letI := io'.toAlgebra; ∃ φ : T.Fr →ₐ[c.F] T'.Fr,
        (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e' : ℤ) * vV T.V a) ∧ FrMap φ y.1 y'.1 := by
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hS⟩ := GlobalTheory.UnifTrait.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hfin : (algebraMap T.V W).Finite := RingHom.finite_algebraMap.2 hf
  have hl : IsLocalHom (algebraMap T.V W) := hfin.to_isIntegral.isLocalHom hi
  have hres : CharZero (ResidueField W) :=
    charZero_of_injective_ringHom (ResidueField.map (algebraMap T.V W)).injective
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  obtain ⟨φ, hφ⟩ : ∃ φ : T.Fr →+* T'.Fr, ∀ v, φ (algebraMap T.V T.Fr v) = algebraMap T'.V T'.Fr (algebraMap T.V W v) :=
    ⟨IsFractionRing.lift hj, IsFractionRing.lift_algebraMap hj⟩
  obtain ⟨r, hr0, hv⟩ := GlobalTheory.IntegralPull.exists_index (V' := T'.V) (algebraMap T.V W) φ hφ
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c _ _ ψ y.1
  obtain ⟨p, χ, y₀, hy₀⟩ := y.2.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, ⟨p, ψ.comp χ, y₀, Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ χ ψ y₀ y.1 z hy₀ hz⟩,
      GlobalTheory.IntegralPull.integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  exact ⟨T', φ.comp io, y', r, hres, hr0,
    fun I => GlobalTheory.IntegralPull.exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 I.m1 I.m2 hS, ψ, fun a _ => hv a, hz⟩

end GlobalTheory.ExtScaleZero

namespace GlobalTheory.ExtScaleZero


set_option maxHeartbeats 1000000 in
theorem exists_ext_chart_scale_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), CharZero (ResidueField T.V) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), CharZero (ResidueField T'.V) ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ GlobalTheory.SlopeRec.HasPhi y' (r * φ) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y hy φ hφ
  obtain ⟨S', io', z', r, hz', hr, hU, ψA, hv, hm⟩ :=
    exists_ext_all_models_uniformised_charZero E H Dw l Xo c T io y hy
  have hphi : ∀ φ' : ℝ, GlobalTheory.SlopeRec.HasPhi z' φ' → φ' = r * φ := fun φ' h' =>
    GlobalTheory.T.balancedPeriodSlope_mul_ramificationIndex _ _ _ _ Xo c T S' io io' y z' r hr ⟨ψA, hv, hm⟩ φ φ' hφ h'
  letI := io.toAlgebra
  let ψ : T.Fr →+* S'.Fr := letI := io'.toAlgebra; ψA.toRingHom
  have hio : io' = ψ.comp io := by
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (ψA.commutes a).symm
  have hv' : ∀ a : T.Fr, vV S'.V (ψ a) = (r : ℤ) * vV T.V a := fun a => by
    by_cases ha : a = 0
    · simp [ha, vV]
    · exact hv a ha
  have hev : ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      ∀ f ∈ thGen Xo c nab a n, ψ (evI y f) = evI z' f := fun nab hn a n f hf =>
    GlobalTheory.T.thetaRule_integralPoint_value_baseChange _ _ _ _ Xo c nab hn T S' io io' y z' ψA hm a n f hf
  clear_value ψ
  clear hm hv ψA
  subst hio
  obtain ⟨C, hCh⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists _ H _ _ Xo c (fun _ => rfl) S' _ z'
  obtain ⟨P, hP⟩ := hU C.I
  obtain ⟨φ', hφ'⟩ := GlobalTheory.SlopeRec.exists_hasPhi z' C.I.G C.I.t' C.I.m1 C.I.m2 P
  have e1 := hphi φ' hφ'
  subst e1
  refine ⟨S', ψ.comp io, z', r, C, P, hz', hr, hCh, hP, hφ', fun nab hn a n e s f hf => ?_⟩
  rw [← hev nab hn a n f hf, RingHom.comp_apply, ← map_mul, Formalism.L2.Pj.nval_bc ψ hr hv']

end GlobalTheory.ExtScaleZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZerStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_truncatedFrame_chart_residue_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), CharZero (ResidueField T.V) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), CharZero (ResidueField T'.V) ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ GlobalTheory.SlopeRec.HasPhi y' (r * φ) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  first | exact @GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero | exact GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero | (intros; apply GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheaf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheaf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem ker_specMap_quotientMk (R : Type) [CommRing R] (J : Ideal R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker =
      baseIdeal (𝟙 (Spec (CommRingCat.of R))) J := by
  rw [Scheme.ker_of_isAffine, baseIdeal]
  congr 1
  have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have h1' : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom y) =
        Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := fun y => by
    rw [← CommRingCat.comp_apply, h1, CommRingCat.comp_apply]
    rfl
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hc : ∀ r : R, cst (𝟙 (Spec (CommRingCat.of R))) ⊤ r =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    intro r
    simp [cst, rs]
  ext x
  rw [RingHom.mem_ker, ← map_eq_zero_iff _ hinj, h1']
  constructor
  · intro hx
    have hm := Ideal.mem_map_of_mem (cst (𝟙 (Spec (CommRingCat.of R))) ⊤)
      (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    rwa [hc, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at hm
  · intro hx
    have hle : J.map (cst (𝟙 (Spec (CommRingCat.of R))) ⊤) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom) := by
      refine Ideal.map_le_iff_le_comap.2 fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hc, RingHom.comp_apply, ← CommRingCat.comp_apply,
        Iso.inv_hom_id, CommRingCat.id_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hj
    exact hle hx

theorem baseChange_quotient : ∀ (R : Type) [CommRing R] (J : Ideal R) (W Y : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))),
    IsPullback b q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) →
      IsClosedImmersion b ∧ b.ker = baseIdeal f J ∧ ∀ V : W.Opens, IsAffineOpen V →
        Function.Surjective (b.app V).hom ∧ RingHom.ker (b.app V).hom = J.map (cst f V) := by
  intro R _ J W Y f b q h
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have e : h.isoPullback.hom ≫ pullback.fst _ _ = b := h.isoPullback_hom_fst
  haveI hb : IsClosedImmersion b := by
    rw [← e]
    infer_instance
  have hk : b.ker = baseIdeal f J := by
    rw [← e, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ker_specMap_quotientMk, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1, Category.comp_id]
  refine ⟨hb, hk, fun V hV => ⟨b.app_surjective V hV, ?_⟩⟩
  rw [← Scheme.Hom.ker_apply b ⟨V, hV⟩, hk, baseIdeal_ideal]

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf : ∀ (R : Type) [CommRing R] (J : Ideal R) (W Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback b q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → IsClosedImmersion b ∧ b.ker = baseIdeal f J ∧ ∀ V : W.Opens, IsAffineOpen V → Function.Surjective (b.app V).hom ∧ RingHom.ker (b.app V).hom = J.map (cst f V) := by
  first | exact @GlobalTheory.FormalAlg.baseChange_quotient | exact GlobalTheory.FormalAlg.baseChange_quotient | (intros; apply GlobalTheory.FormalAlg.baseChange_quotient <;> assumption)
end
end
