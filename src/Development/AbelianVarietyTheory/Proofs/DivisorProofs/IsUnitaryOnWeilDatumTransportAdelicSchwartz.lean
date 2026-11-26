module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSectionPolynomialGrowth
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ArthurClozelLocalSC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section
namespace GlobalTheory.WeilUnitaryTransportF

theorem isUnitaryOn_transportF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ χS χT hcS hcT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have hψ := hω.std
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.T.exists_unitaryPair_partner_cmExtension F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_rationalMatrices_tower F E nS nT
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ :=
    GlobalTheory.T.darbouxCoords_transfer_haar_fundamentalDomain_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform F B.ψ hψ.1 κ μ hμ ν' hν' 𝓕' h𝓕'
  have hiso : ∀ Ψ ∈ schA F κ, ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂μ =
      c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Ψ w‖ₑ ^ 2 ∂ν := by
    intro Ψ hΨ
    rw [hc Ψ hΨ, ← heq]
    rfl
  have hth : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
    ⟨GlobalTheory.T.thetaTransform_rationalTranslate_quasiInvariant_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.continuous_thetaTransform_schwartz_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.contDiff_thetaTransform_archimedean_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ⟩
  have ht := hom a b g h hh hg Φ hΦ
  calc
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ ((om (a, b)) Φ) w‖ₑ ^ 2 ∂ν := hiso _ ht.1
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w‖ₑ ^ 2 ∂ν := by
      calc
        _ = c * ∫⁻ w in 𝓕, ‖(ω (g, h)) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) w‖ₑ ^ 2 ∂ν := by
          congr 1
          apply lintegral_congr
          intro w
          exact congrArg (fun z : ℂ => ‖z‖ₑ ^ 2) (congrFun ht.2 w)
        _ = _ := congrArg (c * ·) (hω.om_unit ν 𝓕 hν h𝓕 _ _ hth)
    _ = _ := (hiso _ hΦ).symm

end GlobalTheory.WeilUnitaryTransportF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartzStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  first | exact @GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF | exact GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF | (intros; apply GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEntireFactorIsThetaFunctionStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEntireFactorIsThetaFunctionStandard
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawOF

theorem theta_of_vacuum_real : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (colLat frS : Set _) (colLat frT : Set _) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) := by
  intro D ψ θ S T frS frT hS hT δ hC hδ f hf Φ hΦd hΦ
  have hψ := hf.1
  have hθ := hf.2.inf
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hSd := GlobalTheory.FunObj.VecEx.isSelfDualC_colLat S frS hS
  have hTd := GlobalTheory.FunObj.VecEx.isSelfDualC_colLat T frT hT
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T (colLat frS) (colLat frT) hψ hSd hTd
  refine ⟨hΦd.comp ((differentiable_id).const_smul δ⁻¹), ?_⟩
  intro x hx Y
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.T.exists_rational_frameCoords_of_mem_torusLattice S T frS frT hS hT δ x hx
  have hv' : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (colLat frS : Set _) (colLat frT : Set _) (fun _ => True) := by
    rw [AddMonoidHom.map_neg]; exact neg_mem hv
  obtain ⟨ε, -, hε⟩ := h3 f hf.2.lat _ hv'
  have hsign := GlobalTheory.T.latticePoint_sign_eq_thetaLaw_semicharacter ψ S T frS frT hS hT hψ δ hδ v hv ε (fun g hg => hε g hg)
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hch hψ hf.2.theta v (hε f hf.2.lat)
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b with hX
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := δ⁻¹ • Y with hZ
  have hZY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  set z : GlobalTheory.FockCompare.RW T S := fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ with hz
  have hzτ : ∀ τ, (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) :=
    fun τ => coord_back frS frT Z τ
  have hz1 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) = Z := by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) = Z + X := by
    rw [zCo_iota hch]; funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)) * GlobalTheory.FockPos.frAt frS τ = Z τ + X τ
    rw [Matrix.mul_add, Matrix.add_mul, hzτ τ]
    rfl
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re := by
    rw [omO_frame frS frT hS hT]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hzτ τ]
    rfl
  have hl := hlaw z
  rw [hΦ _ (hch.real_iota T S _), hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO, hz1, hz2, hom, hsign] at hl

  simp only [Formalism.MainNotions.TaylorLogMetric.U]
  have e1 : δ⁻¹ • (Y + δ • X) = Z + X := by rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [e1, hZY, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
  have hZZ : δ⁻¹ • δ • Z = Z := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [hZZ]
  set a := Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) with ha
  have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    push_cast at h ⊢
    linear_combination h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)))
  rw [← kE]
  calc _ = a * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) * Φ (Z + X)) := by
        rw [kE]; ring
    _ = _ := by
        rw [hl]
        have := al_mul_self (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X)
        rw [← ha] at this
        linear_combination (Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) * Φ Z) * this

end GlobalTheory.ThetaLawOF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEntireFactorIsThetaFunctionStandardStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_vacuum_entire_factor_isThetaFunction_standard : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (colLat frS : Set _) (colLat frT : Set _) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) := by
  first | exact @GlobalTheory.ThetaLawOF.theta_of_vacuum_real | exact GlobalTheory.ThetaLawOF.theta_of_vacuum_real | (intros; apply GlobalTheory.ThetaLawOF.theta_of_vacuum_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem applyAt0_monomial' (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G = (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl,
    one_mul]

theorem taylor_comp_smul' (D : D7) {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) (hG : Differentiable ℂ G) (a : ℂ) (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => G (a • z)) α = a ^ (α.sum fun _ n => n) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_comp_const_smul (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) a ((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top))
  rw [key]
  simp only [smul_zero, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]
  congr 2
  exact Finsupp.card_toMultiset α

theorem fock_jets_eq_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) ∧ Θ ≠ 0 ∧ ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  intro D ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ f hf
  have hsS := cart_one frS hS hcS
  have hsT := cart_one frT hT hcT
  subst hsS hsT
  obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf
  have hTh := GlobalTheory.T.unit_vacuum_entire_factor_isThetaFunction_standard ψ θ S T frS frT hS hT δ hC hδ f hf Φ hΦd hreal
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ = fun Y => Φ (δ⁻¹ • Y) := ⟨_, rfl⟩
  rw [← hΘ] at hTh
  have hΦeq : Φ = fun z => Θ (δ • z) := by
    funext z
    simp only [hΘ, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  refine ⟨Θ, hTh, ?_, fun k => ?_⟩
  · intro h0
    obtain ⟨w, hw, hfw⟩ := GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel ψ θ S T _ _ _ _ f hf
    apply hfw
    have h1 : Φ (zCo θ frS frT w) = 0 := by
      rw [hΦeq]
      exact congrFun h0 _
    rw [hreal w hw, h1, mul_zero]
  · have hdiff : Differentiable ℂ Θ := hTh.1
    have hj := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hf.2.inf hS hT f Φ hΦd hreal k
    change pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f (MvPolynomial.monomial k 1) 0 = _
    rw [hj, hΦeq, applyAt0_monomial', applyAt0_monomial', taylor_comp_smul' D _ hdiff]
    have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
      intro τ
      rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
    have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
        (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
      simp only [hper, Finsupp.prod, Finsupp.sum]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    rw [hprod, mul_pow]
    ring

end GlobalTheory.FockPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJets_unitVacuum_eq_scaled_thetaJets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) ∧ Θ ≠ 0 ∧ ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  first | exact @GlobalTheory.FockPos.fock_jets_eq_theta | exact GlobalTheory.FockPos.fock_jets_eq_theta | (intros; apply GlobalTheory.FockPos.fock_jets_eq_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditive
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinBarCoords

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_algebraMap (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (u : AF F) :
    compFin F E v (algebraMap (AF F) (AE F E) u) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (evFin F v u) := rfl

theorem at_tensAt (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro u hu
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right, compFin_algebraMap, hu, map_zero, mul_zero, map_zero]

theorem eq_tensAt_of_at (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {z : AE F E} (hz : At (evFin F v) z) :
    z = tensAt E v (compFin F E v z) := by
  have h1 : (1 - atPlace v 1) • z = 0 := hz _ (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [Algebra.smul_def, show algebraMap (AF F) (AE F E) (atPlace v 1) = tensAt E v 1 from rfl, tensAt_mul_right, one_mul]

theorem piW_tensAt (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) : piW t (tensAt E v y) = splitProj t y := by
  show splitProj t (compFin F E v (tensAt E v y)) = _
  rw [compFin_tensAt]

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_matrix {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {x : Matrix m n (AE F E)} :
    At (evFin F v) x ↔ ∀ i j, At (evFin F v) (x i j) := by
  constructor
  · intro h i j u hu
    have := congrFun (congrFun (h u hu) i) j
    simpa using this
  · intro h u hu
    ext i j
    simpa using h i j u hu

def liftM (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) :
    Matrix m n (Fv F v) × Matrix m n (Fv F v) →+ Matrix m n (AE F E) :=
  AddMonoidHom.mk' (fun p => Matrix.of fun i j => tensAt E v ((splitAlgEquiv hcm t).symm (p.1 i j, p.2 i j)))
    (fun p q => by ext i j; simp only [Prod.fst_add, Prod.snd_add, Matrix.add_apply, Matrix.of_apply, ← Prod.mk_add_mk, map_add (f := _)])

theorem liftM_at (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : At (evFin F v) (liftM σ hcm v t p) :=
  (at_matrix v).2 fun _ _ => at_tensAt v _

theorem liftM_fst (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : (liftM σ hcm v t p).map (piW t) = p.1 := by
  ext i j
  simp [liftM, piW_tensAt]

theorem liftM_snd (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : (liftM σ hcm v t p).map (piW (t.comp σ)) = p.2 := by
  ext i j
  simp [liftM, piW_tensAt]

theorem eq_zero_of_at (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v)
    {x : Matrix m n (AE F E)} (hx : At (evFin F v) x) (h1 : x.map (piW t) = 0) (h2 : x.map (piW (t.comp σ)) = 0) :
    x = 0 := by
  ext i j
  rw [eq_tensAt_of_at v ((at_matrix v).1 hx i j)]
  have e : compFin F E v (x i j) = 0 := split_ext hcm t (by rw [map_zero]; exact (by simpa using congrFun (congrFun h1 i) j : piW t (x i j) = 0))
    (by rw [map_zero]; exact (by simpa using congrFun (congrFun h2 i) j : piW (t.comp σ) (x i j) = 0))
  rw [e, map_zero]; rfl

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  set A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm with hA'
  have key : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA, hA', Matrix.transpose_submatrix,
      Matrix.submatrix_mul (Aᵀ * M) (A.map star) e.symm id e.symm Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id, Matrix.submatrix_id_id, Matrix.submatrix_map]
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg,
    Matrix.det_one, mul_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0, mul_zero, zero_mul] at hd
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd.symm

theorem det_map_isUnit : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (r s : ℕ), c ≠ 0 → (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map (B.emb w).1) r s) →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v), IsUnit (J.map t).det := by
  intro F E _ _ _ _ _ B n J c r s hc hs v t
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h1 := det_ne_zero_of_hasSig (hs (NumberField.InfinitePlace.mk φ))
  have e1 : (J.map (B.emb (NumberField.InfinitePlace.mk φ)).1).det = (B.emb (NumberField.InfinitePlace.mk φ)).1 J.det :=
    (RingHom.map_det _ J).symm
  rw [Matrix.det_smul, e1] at h1
  have hJ : J.det ≠ 0 := fun h0 => h1 (by rw [h0, map_zero, mul_zero])
  have e2 : (J.map t).det = t J.det := (RingHom.map_det (t : E →+* Fv F v) J).symm
  rw [isUnit_iff_ne_zero, e2]
  exact (map_ne_zero_iff _ (t : E →+* Fv F v).injective).2 hJ

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

theorem exists_split_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW t) = 0 ∧ GlobalTheory.LinBarAt.coAt G t (uT Y) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW (t.comp σ)) = 0 ∧ (uM z).map (piW t) = -z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinBarAt.coAt G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinBarAt.coAt G t x i j * (u.map (piW t)) i j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v t
  have hcm := hTr.base.cm
  have hP : IsUnit (G.V'.J.map t).det := det_map_isUnit B G.V'.J 1 _ _ one_ne_zero (fun w => by rw [one_smul]; exact hTr.geo.hV'.sig w) v t
  have hQ : IsUnit ((G.W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose]; exact det_map_isUnit B G.W.J Complex.I _ _ Complex.I_ne_zero hTr.geo.hW.sig v t
  set P := G.V'.J.map t with hPdef
  set Q := (G.W.J.map t)ᵀ with hQdef
  let L := liftM σ hcm (m := Fin a') (n := Fin (a + a')) v t
  let uT : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun Y => L (0, -(P⁻¹ * Y * Q⁻¹))) (fun Y Y' => by
      rw [Matrix.mul_add, Matrix.add_mul, neg_add, ← map_add (f := _), Prod.mk_add_mk, add_zero])
  let uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun z => L (-z, 0)) (fun z z' => by rw [neg_add, ← map_add (f := _), Prod.mk_add_mk, add_zero])
  have hco : ∀ u, GlobalTheory.LinBarAt.coAt G t u = -(P * u.map (piW (t.comp σ)) * Q) := fun u => by
    simp [GlobalTheory.LinBarAt.coAt, hPdef, hQdef]
  have hTc : ∀ Y, (uT Y).map (piW (t.comp σ)) = -(P⁻¹ * Y * Q⁻¹) := fun Y => liftM_snd σ hcm v t _
  have hTt : ∀ Y, (uT Y).map (piW t) = 0 := fun Y => liftM_fst σ hcm v t _
  have hMc : ∀ z, (uM z).map (piW (t.comp σ)) = 0 := fun z => liftM_snd σ hcm v t _
  have hMt : ∀ z, (uM z).map (piW t) = -z := fun z => liftM_fst σ hcm v t _
  have hTa : ∀ Y, At (evFin F v) (uT Y) := fun Y => liftM_at σ hcm v t _
  have hMa : ∀ z, At (evFin F v) (uM z) := fun z => liftM_at σ hcm v t _
  refine ⟨uT, uM, fun Y => ⟨hTa Y, hTt Y, ?_⟩, fun z => ⟨hMa z, hMc z, hMt z⟩, fun u hu => ?_, fun x u hx hu => ?_⟩
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
    have e2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
    rw [hco, hTc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · refine ⟨GlobalTheory.LinBarAt.coAt G t u, -(u.map (piW t)), ?_⟩
    have hd : At (evFin F v) (u - (uT (GlobalTheory.LinBarAt.coAt G t u) + uM (-(u.map (piW t))))) := by
      intro c hc
      rw [smul_sub, smul_add, hu c hc, hTa _ c hc, hMa _ c hc, add_zero, sub_zero]
    refine (sub_eq_zero.1 (eq_zero_of_at σ hcm v t hd ?_ ?_))
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTt, hMt, neg_neg, zero_add, sub_self]
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTc, hMc, add_zero, hco, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
        Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, sub_self]
  · have h := GlobalTheory.T.local_lattice_hermitian_skew hcm v t G.V'.J G.W.J hTr.geo.hV'.herm hTr.geo.hW.skew x u hx
    dsimp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM] at h
    rw [hco, hco]
    exact h

end GlobalTheory.LinBarCoords
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unipotent_additive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW t) = 0 ∧ GlobalTheory.LinBarAt.coAt G t (uT Y) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW (t.comp σ)) = 0 ∧ (uM z).map (piW t) = -z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinBarAt.coAt G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinBarAt.coAt G t x i j * (u.map (piW t)) i j) := by
  first | exact @GlobalTheory.LinBarCoords.exists_split_coords | exact GlobalTheory.LinBarCoords.exists_split_coords | (intros; apply GlobalTheory.LinBarCoords.exists_split_coords <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

def ptAt (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) : w.adicCompletion E →ₙ+* _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  (GlobalTheory.AdelicU.Supp.singleTens E v).comp (InertChart.complEquiv hw h).symm.toRingHom.toNonUnitalRingHom

def locW (h : w.under (𝓞 F) = v) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

def kap (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (B : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    Matrix (Fin n) (Fin m) (w.adicCompletion E) →+ Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom).comp
    { toFun := fun x => A * xᵀ * Bᵀ
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul] }

variable (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem kap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (B : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x : Matrix (Fin n) (Fin m) (w.adicCompletion E)) : kap hw h A B x = (A * xᵀ * Bᵀ).map (ptAt hw h) := rfl

theorem ptAt_apply (z : w.adicCompletion E) :
    ptAt hw h z = GlobalTheory.AdelicU.Supp.singleTens E v ((InertChart.complEquiv hw h).symm z) := rfl

theorem locW_ptAt (z : w.adicCompletion E) : locW h (ptAt hw h z) = z := by
  change toCompl h (compFin F E v (GlobalTheory.AdelicU.Supp.singleTens E v ((InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.AdelicU.Supp.compFin_singleTens_self]
  exact (InertChart.complEquiv hw h).apply_symm_apply z

theorem at_ptAt (z : w.adicCompletion E) : At (evFin F v) (ptAt hw h z) :=
  GlobalTheory.ThK.at_evFin_iff.2 ⟨fun u => GlobalTheory.AdelicU.Supp.compInf_singleTens u v _,
    fun u hu => GlobalTheory.AdelicU.Supp.compFin_singleTens_ne hu _⟩

theorem ptAt_locW {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : ptAt hw h (locW h z) = z := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ThK.at_evFin_iff.1 hz
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun u => ?_) fun u => ?_
  · rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compInf_singleTens, h1 u]
  · by_cases e : u = v
    · subst e
      rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compFin_singleTens_self]
      exact (InertChart.complEquiv hw h).symm_apply_apply _
    · rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compFin_singleTens_ne e, h2 u e]

end GlobalTheory.InertCoord

namespace GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem cA_ptAt (σ : E →ₐ[F] E) {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) (z : w.adicCompletion E) :
    cA σ (ptAt hw h z) = ptAt hw h (c z) := by
  have e1 : ∀ y : AE F E, cA σ y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e1, ptAt_apply, GlobalTheory.AdelicU.Supp.sigR_singleTens, ptAt_apply]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((InertChart.complEquiv hw h).symm z)
  change c (InertChart.complEquiv hw h ((InertChart.complEquiv hw h).symm z)) = _ at this
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

theorem inclR_mul_ptAt (x : E) (z : w.adicCompletion E) :
    inclR (F := F) (AF F) x * ptAt hw h z = ptAt hw h (algebraMap E (w.adicCompletion E) x * z) := by
  rw [mul_comm, ptAt_apply, GlobalTheory.AdelicU.Supp.singleTens_mul, ptAt_apply]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply, mul_comm]
  congr 1
  change toCompl h (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [GlobalTheory.AdelicU.Supp.compFin_one_tmul, toCompl_tmul, map_one, one_mul]

end GlobalTheory.InertCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KInfPol

open GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem at_mul_right {m p q : Type} [Fintype p] {z : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hz : At (evI F) z)
    (A : Matrix p q (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : At (evI F) (z * A) := by
  intro u hu; rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

theorem heisLine_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (t : ℝ) :
    M.heisLine ψ u t 0 = 0 := by
  funext x
  simp [Model.heisLine, Darboux.rho, schr]

theorem sa_of_acts {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) : SA T f f₁ := by
  intro g hg
  refine h (fun x => g (fun i => (x i).2)) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  change g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [fin_eq_zero_of_at hz, add_zero]

theorem sd_intertwine {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ W.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (1, h)) f g) (hf₁ : Acts (evI F) (om (1, h)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (u * (mat h)ᵀ)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (1, h) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (1, h) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((1, h) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (u * (mat h)ᵀ) := by
    change (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (realAd F t • u) * (mat h)ᵀ = _
    rw [Matrix.one_mul, Matrix.smul_mul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

theorem pol_stable_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ ∈ M.Pol B.ψ B.emb := by
  intro F E _ _ _ _ _ σ B n d Y W M om χ₁ χ₂ hB hM hw k hk f hf f₁ hf₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B n d Y W M om χ₁ χ₂ hB hM hw k hk
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  have hle : M.Pol B.ψ B.emb ≤ (M.Pol B.ψ B.emb).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_right hu (mat k⁻¹)ᵀ
      have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
          calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
                ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
                (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_right hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.KInfPol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ ∈ M.Pol B.ψ B.emb := by
  first | exact @GlobalTheory.KInfPol.pol_stable_kInf | exact GlobalTheory.KInfPol.pol_stable_kInf | (intros; apply GlobalTheory.KInfPol.pol_stable_kInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelVPCore
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.LevelLawCore

theorem omega_level_vP_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Vc D i)), VStd D i → k ∈ GfC (Vc D i) → ∀ hk : fin (Vc D i) k ∈ levJ R i t, R.ωP i t (k, 1) (R.vP i t) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.vP i t := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t k _ hf hk
  have hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
      (Formalism.IndefR.Lev.flag1L (R.datVt i t)) := hk
  have hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k := ⟨hf, hl.1, Subgroup.mem_bot.1 hl.2⟩
  have hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
    ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
  refine (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 k 1 hκ hκ').trans ?_
  exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t)
    (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm

end GlobalTheory.AdTh.LevelLawCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothCharCompNormU
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCChar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def normU (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] :
    (u.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  Units.map (Algebra.norm (v.adicCompletion K) : u.adicCompletion L →* v.adicCompletion K)

theorem isSmoothChar_comp_normU (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L))
    [u.asIdeal.LiesOver v.asIdeal] {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmoothChar (χ.comp (normU v u)) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion L) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K L (u.adicCompletion L)]
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion L) := GroundTheory.Global.finite_adicCompletion v u
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K L v u _ (GroundTheory.Global.continuous_adicCompletionMap v u) hfd).2
  unfold IsSmoothChar at hχ ⊢
  rw [← MonoidHom.comap_ker]
  exact hχ.preimage (Continuous.units_map _ hc)

end GlobalTheory.BCChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmType
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

theorem nuH_inv_hasInf : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), (nuH G μ₀ i j)⁻¹.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  intro D T L sc μ₀ hL G i j k
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  obtain ⟨n', hn', hinf⟩ := (L.C.isMu0 j).inf
  have hk : ∀ τ, Formalism.L2.Host.embTau D τ (k : D.host.E) ≠ 0 := fun τ => by simp
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv, HChar.inf_inv, HChar.inf_mul, HChar.inf_inv, Units.val_inv_eq_inv_val,
    Units.val_mul, Units.val_inv_eq_inv_val, hinf k, G.ch.inf _ a1 a2 k, ← D.eTau.prod_comp, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 : n' (D.eTau τ) = -(2 * (num D sc.cGap τ).e (j + 1)) := by
    have := hn' (D.eTau τ)
    beta_reduce at this
    rw [Formalism.L2.Host.eExp, Equiv.symm_apply_apply,
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D sc.cGap) (cen D sc.cGap τ)).2.2] at this
    have h2 : ((n' (D.eTau τ) : ℤ) : ℚ) = ((-(2 * (num D sc.cGap τ).e (j + 1)) : ℤ) : ℚ) := by
      rw [this]; push_cast; unfold num; ring
    exact_mod_cast h2
  have hne : (Formalism.L2.Host.embTau D τ (k : D.host.E) / ((‖Formalism.L2.Host.embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ≠ 0 :=
    div_ne_zero (hk τ) (by simpa using hk τ)
  beta_reduce
  rw [h1]
  change ((Formalism.L2.Host.embTau D τ (k : D.host.E) / ((‖Formalism.L2.Host.embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ _ * _)⁻¹ = _
  rw [← zpow_neg, ← zpow_add₀ hne, ← zpow_neg]
  congr 1
  ring

end GlobalTheory.FunObj.SqNum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmTypeStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNu_inv_hasInfinityType_cmType : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), (nuH G μ₀ i j)⁻¹.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  first | exact @GlobalTheory.FunObj.SqNum.nuH_inv_hasInf | exact GlobalTheory.FunObj.SqNum.nuH_inv_hasInf | (intros; apply GlobalTheory.FunObj.SqNum.nuH_inv_hasInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weilDatum_doubleSpace_acts_unitScalar_seesaw_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = c • GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  first | exact @PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant | exact PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant | (intros; apply PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant <;> assumption)
end
