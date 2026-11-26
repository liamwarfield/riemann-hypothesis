module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicVectorThetaTransformHeisenbergDer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumThetaTransformEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumEquationsTransferSchroedingerDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanHeisenbergLineContinuousFiniteZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanHeisenbergLineContinuousFiniteZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

noncomputable section

namespace GlobalTheory.ArchLineCont

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (realAd)

theorem continuous_ofMixed' (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((_root_.continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((_root_.continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_realAd' (F : Type) [Field F] [NumberField F] : Continuous (realAd F) :=
  Continuous.prodMk ((continuous_ofMixed' F).comp (continuous_algebraMap ℝ _)) continuous_const


set_option synthInstance.maxHeartbeats 400000 in
theorem archLine_continuous_finPart : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (g : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
    (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u : Matrix (Fin S.rank) (Fin d) (AE D),
      Continuous (GlobalTheory.VacTransfer.archLine cS u) ∧ ∀ t, (GlobalTheory.VacTransfer.archLine cS u t).map (finPart D) = 0 := by
  intro D S X d e g cS hcS u
  have hform : ∀ t, GlobalTheory.VacTransfer.archLine cS u t =
      (HMul.hMul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)ᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D)) := fun t => by
    rw [GlobalTheory.VacTransfer.archLine_apply, hcS]
  refine ⟨?_, fun t => ?_⟩
  · have hsm : Continuous fun t : ℝ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u : Matrix (Fin S.rank) (Fin d) (AE D)) :=
      (continuous_realAd' D.host.F).smul continuous_const
    have : (GlobalTheory.VacTransfer.archLine cS u : ℝ → WO S X) = fun t =>
        (HMul.hMul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)ᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) :
          Matrix (Fin X.rank) (Fin S.rank) (AE D)) := funext hform
    rw [this]
    exact (hsm.matrix_transpose.matrix_submatrix e id).matrix_mul continuous_const
  · rw [hform]
    refine Matrix.ext fun i j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.map_apply, Matrix.zero_apply, Matrix.mul_apply, map_sum (finPart D)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [(finPart D).map_mul, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, GlobalTheory.ArchLineSum.finPart_smul,
      show sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul, zero_mul, zero_mul]

end GlobalTheory.ArchLineCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanHeisenbergLineContinuousFiniteZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (g : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
    (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u : Matrix (Fin S.rank) (Fin d) (AE D),
      Continuous (GlobalTheory.VacTransfer.archLine cS u) ∧ ∀ t, (GlobalTheory.VacTransfer.archLine cS u t).map (finPart D) = 0 := by
  first | exact @GlobalTheory.ArchLineCont.archLine_continuous_finPart | exact GlobalTheory.ArchLineCont.archLine_continuous_finPart | (intros; apply GlobalTheory.ArchLineCont.archLine_continuous_finPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivRealLineEqSumRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivRealLineEqSumRealPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

namespace GlobalTheory.PlaceSum
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem hD_finset_sum {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) {α : Type} (s : Finset α)
    (u : α → R) : hD ι π om (∑ a ∈ s, u a) f = ∑ a ∈ s, hD ι π om (u a) f := by
  funext w
  rw [Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hD_eq_fderiv ι π om f hf, map_sum, ContinuousLinearMap.sum_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

theorem deriv_heisO_eq_sum_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  intro D ψ hψ θ hθ S T f hf L hLc hLf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e1 : (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (L 1)) f :=
    dLine_eq_hD h hψ (L := L) ⟨hLc, hLf⟩ f
  have e2 : ∀ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1)) f := by
    intro τ
    have hl := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ (L 1))
    rw [dRho_eq_dLine]
    exact dLine_eq_hD h hψ ⟨hl.1, hl.2.1⟩ f
  have e3 : piW θ T S (L 1) = ∑ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) := by
    funext τ' i j
    simp only [Finset.sum_apply]
    have hc : ∀ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) τ' i j =
        compAt θ τ' (lineAt θ τ (compAt θ τ (L 1)) 1) i j := fun τ => rfl
    simp only [hc]
    rw [Finset.sum_eq_single τ']
    · rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ' (compAt θ τ' (L 1))).2.2 1 τ', if_pos rfl, Complex.ofReal_one,
        one_smul]
      rfl
    · intro b _ hb
      rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ b (compAt θ b (L 1))).2.2 1 τ', if_neg (Ne.symm hb)]
      rfl
    · intro hn; exact absurd (Finset.mem_univ τ') hn
  rw [e1, e3, hD_finset_sum _ _ _ f (theta_sm h hf)]
  exact Finset.sum_congr rfl fun τ _ => (e2 τ).symm

end GlobalTheory.PlaceSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivRealLineEqSumRealPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  first | exact @GlobalTheory.PlaceSum.deriv_heisO_eq_sum_dRho | exact GlobalTheory.PlaceSum.deriv_heisO_eq_sum_dRho | (intros; apply GlobalTheory.PlaceSum.deriv_heisO_eq_sum_dRho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerDerivRelationOfHeisenbergDeriv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerDerivRelationOfHeisenbergDeriv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

open GlobalTheory.ThetaTransform

noncomputable section

namespace GlobalTheory.LineDerivTransfer

theorem hasDerivAt_heisV_of {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) (hΦ'm : Φ' ∈ GlobalTheory.WeilM.schA F (Fin N)) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (hΦ'd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0) (w : VA F N) :
    HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := GlobalTheory.ThetaDeriv.decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ :=
    GlobalTheory.ThetaDeriv.decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (GlobalTheory.SWQ.rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (GlobalTheory.SWQ.rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (GlobalTheory.SWQ.rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (GlobalTheory.ThetaDeriv.hasDerivAt_schr hF ψ hM hΦ'd (GlobalTheory.SWQ.rat ξ + w.1) t).const_mul (ph ξ))
    (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this

theorem thV_smul {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (c : ℂ) (Φ : (Fin N → AF F) → ℂ) : thV ψ (c • Φ) = c • thV ψ Φ := by
  funext w
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

end GlobalTheory.LineDerivTransfer


open GlobalTheory.LineDerivTransfer in
theorem GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  intro D ψ hψ S T JB ξ hB κ _ co hrat Φ hΦ L L' hL hL0 hL' hL0' c hrel x
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  let e := numCoord co σ
  have he : ∀ w w', symplO S T w w' = symV (e w) (e w') := fun w w' => by
    rw [symplO_eq_symp rfl hB, co.form]
    simp only [e, symV, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
  obtain ⟨-, -, hfin, -⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank _ e
  have hc : Continuous e := (GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank _ e).1
  have hΦσ := comp_mem_schA σ hΦ
  have key : ∀ L : ℝ →+ WO S T, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∃ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin (Fintype.card κ)),
        (∀ x, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) (Φ' (x ∘ σ.symm)) 0) ∧
        (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
          thV ψ Φ' ∘ e := by
    intro L hL hL0
    have hM : IsRealLine (e.toLinearMap.toAddMonoidHom.comp L) := ⟨hc.comp hL, fun t => (hfin _).1 (hL0 t)⟩
    obtain ⟨Φ', hm, hd⟩ := GlobalTheory.ThetaDeriv.exists_deriv_schr hR ψ hψ.1 hM hΦσ
    refine ⟨Φ', hm, fun x => ?_, funext fun w => ?_⟩
    · have h : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) =
          fun t => GlobalTheory.WeilM.schr ψ (e.toLinearMap.toAddMonoidHom.comp L t) (fun y => Φ (y ∘ σ)) (x ∘ σ.symm) := by
        funext t
        simp only [GlobalTheory.WeilM.schr, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          LinearEquiv.coe_coe, e, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
        congr 2
        funext i
        simp
      rw [h]
      exact hd _
    · rw [thetaTr_eq co σ]
      have h : (fun t : ℝ => heisO ψ S T (L t) (thV ψ (fun y => Φ (y ∘ σ)) ∘ e) w) =
          fun t => heisV ψ (e.toLinearMap.toAddMonoidHom.comp L t) (thV ψ (fun y => Φ (y ∘ σ))) (e w) :=
        funext fun t => congrFun (heisO_comp he (L t) _) w
      rw [show numCoord co σ = e from rfl, h]
      exact (hasDerivAt_heisV_of ψ hR hψ.1 hΦσ hm hM hd (e w)).deriv
  obtain ⟨Φ₁, hm₁, hd₁, hh₁⟩ := key L hL hL0
  obtain ⟨Φ₂, hm₂, hd₂, hh₂⟩ := key L' hL' hL0'
  rw [hh₁, hh₂] at hrel
  have h2 : thV ψ Φ₂ = thV ψ (c • Φ₁) := by
    rw [thV_smul]
    funext v
    obtain ⟨w, rfl⟩ := e.surjective v
    exact congrFun hrel w
  have h3 := thV_injOn hR hψ.1 hm₂ (Submodule.smul_mem _ c hm₁) h2
  rw [(hd₂ x).deriv, (hd₁ x).deriv, h3]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerDerivRelationOfHeisenbergDerivStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerDeriv_relation_of_heisenbergDeriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  first | exact @GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv | exact GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv | (intros; apply GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumEquationsTransferSchroedingerDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.VacTransfer


set_option maxHeartbeats 800000 in
theorem exists_darboux_cS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ u, co.e (cS u) = M.co.e u := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hc
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    have h := hV.herm j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← h]
    rfl
  obtain ⟨co, hco⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e (X.gram.map (incA D))
    (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J)
    (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (by rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  refine ⟨1, D.host.xi0 • (sgn ε S).gram⁻¹, co, one_smul _ _, fun x => ?_, hco⟩
  obtain ⟨y, z, h⟩ := hM.rat ((x * G⁻¹)ᵀ.submatrix id e.symm)
  refine ⟨y, z, Eq.trans ?_ h⟩
  rw [← hco, hc]
  congr 1
  exact (map_transpose_inv_mul (incA D) e x hdet).symm

theorem vacDatum_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (f : WO S X → ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), IsFinF ψ θ ε A B f → IsDatum M ψ cS Φ f →
        GlobalTheory.VacDatum.IsGaussEq M Bs.ψ Bs.emb Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f Φ hf hD
  subst hψ
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  obtain ⟨ξ, JB, co, hJB, hrat, hco⟩ :=
    exists_darboux_cS D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS
  have hΦf : GlobalTheory.WeilSchrodinger.thetaTr D.host.F co Bs.ψ Φ = f := by
    funext w
    obtain ⟨u, rfl⟩ := cS.surjective w
    refine Eq.trans ?_ (hD.2 u)
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco]
  have hvac : ∀ τ z, dRho (heisO Bs.ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) f =
      Complex.I • dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f := by
    intro τ z
    funext w
    have h0 := congrFun (hf.2 τ z) w
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (-Complex.I) * h0 +
      dRho (heisO Bs.ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) f w * Complex.I_sq
  refine ⟨fun _ => 1, fun u u' _ _ hrel x => ?_⟩
  have hrel' : ∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ) := fun w => by
    simpa using hrel w
  obtain ⟨hc, hc0⟩ := GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero D S X e _ cS hcS u
  obtain ⟨hc', hc0'⟩ := GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero D S X e _ cS hcS u'
  have key : (fun w => deriv (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (archLine cS u' t) f w) 0) =
      Complex.I • (fun w => deriv (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (archLine cS u t) f w) 0) := by
    refine (GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces D Bs.ψ hstd θ hθ (sgn ε S) X f hf.1 (archLine cS u') hc' hc0').trans
      (Eq.trans ?_ (congrArg (Complex.I • ·) (GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces D Bs.ψ hstd θ hθ (sgn ε S) X f hf.1 (archLine cS u) hc hc0).symm))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact (congrArg (fun z => dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f)
      (GlobalTheory.T.realPlaceComponent_archLine_complexStructure D θ hθ ε S X A B e Bs Vs Ws hcart cS hcS u u' hrel' τ)).trans (hvac τ _)
  rw [← hΦf] at key
  have h1 := GlobalTheory.T.schrodingerDeriv_relation_of_heisenbergDeriv D Bs.ψ hstd (sgn ε S) X JB ξ hJB (Fin S.rank × Fin d) co hrat Φ hD.1 (archLine cS u) (archLine cS u')
    hc hc0 hc' hc0' Complex.I key x
  simpa only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.heisLine, GlobalTheory.WeilM.Darboux.rho, archLine_apply, hco] using h1

end GlobalTheory.VacTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumEquationsTransferSchroedingerDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuumEquations_transfer_schroedingerDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (f : WO S X → ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), IsFinF ψ θ ε A B f → IsDatum M ψ cS Φ f →
        GlobalTheory.VacDatum.IsGaussEq M Bs.ψ Bs.emb Φ := by
  first | exact @GlobalTheory.VacTransfer.vacDatum_transfer | exact GlobalTheory.VacTransfer.vacDatum_transfer | (intros; apply GlobalTheory.VacTransfer.vacDatum_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialTmulSchwartzBruhatMemAlgebraicData
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialTmulSchwartzBruhatMemAlgebraicData
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

noncomputable section

namespace GlobalTheory.SquareAgree

theorem pureA_mem_algD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    ∀ f ∈ M.Pol ψ τ, ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.SquareAgree.algD M ψ τ := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hM f hf g hg
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := GlobalTheory.EvAdm.exists_sum_finprod hg
  have hφvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = M.vac v := fun k =>
    ((hφstd k).and hM.std).mono fun v h => h.1.trans h.2.symm
  have h1 : GlobalTheory.WeilM.pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g =
      ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [GlobalTheory.WeilM.pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  rw [h1]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, φ k, hf, hφSB k, hφvac k, rfl⟩)

end GlobalTheory.SquareAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialTmulSchwartzBruhatMemAlgebraicDataStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomial_tmul_schwartzBruhat_mem_algebraicData : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    ∀ f ∈ M.Pol ψ τ, ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.SquareAgree.algD M ψ τ := by
  first | exact @GlobalTheory.SquareAgree.pureA_mem_algD | exact GlobalTheory.SquareAgree.pureA_mem_algD | (intros; apply GlobalTheory.SquareAgree.pureA_mem_algD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumThetaTransformEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.VacDatum

theorem vacDatum_exists : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ f : WO S X → ℂ, IsFinF ψ θ ε A B f → ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD f := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f hf
  obtain ⟨ξ, JB, co, hJB, hrat, hiff⟩ :=
    GlobalTheory.T.exists_rational_darboux_orientedPair_transport D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hψ ▸ hBs.std)
  obtain ⟨-, -, hon⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := sgn ε S) (T := X) co hstd rfl hJB hrat
  obtain ⟨Φ, hΦ, hΦf⟩ := (hon f).1 hf.1
  have hD : IsDatum M ψ cS Φ f := (hiff Φ f).2 ⟨hΦ, hΦf⟩
  have hG := GlobalTheory.T.fockVacuumEquations_transfer_schroedingerDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f Φ hf hD
  have hsp := GlobalTheory.T.mem_gaussianVacuaSpan_of_vacuumEquations M Bs.ψ Bs.emb hBs.std Φ hΦ hG
  refine ⟨Φ, Submodule.span_le.2 ?_ hsp, hD⟩
  rintro _ ⟨g, h, hg, hh, rfl⟩
  exact GlobalTheory.T.fockPolynomial_tmul_schwartzBruhat_mem_algebraicData M Bs.ψ Bs.emb hM g hg h hh

end GlobalTheory.VacDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumThetaTransformEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicDatum_thetaTransform_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ f : WO S X → ℂ, IsFinF ψ θ ε A B f → ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD f := by
  first | exact @GlobalTheory.VacDatum.vacDatum_exists | exact GlobalTheory.VacDatum.vacDatum_exists | (intros; apply GlobalTheory.VacDatum.vacDatum_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem isDatum_zero_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) :
    IsDatum M ψ crd 0 0 := by
  refine ⟨zero_mem _, fun u => ?_⟩
  simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem isDatum_smul_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z)
    {Φ : (Fin n × Fin d → AF F) → ℂ} {f : Z → ℂ} (h : IsDatum M ψ crd Φ f) (c : ℂ) :
    IsDatum M ψ crd (c • Φ) (c • f) := by
  refine ⟨Submodule.smul_mem _ _ h.1, fun u => ?_⟩
  rw [Pi.smul_apply, ← h.2 u]
  simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

theorem algVec_correspond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD Φ) ∧
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, IsDatum M ψ cS ΦD Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
  have hadd : ∀ {Φ Φ' : (Fin S.rank × Fin d → AF D.host.F) → ℂ} {f f' : WO S X → ℂ},
      IsDatum M ψ cS Φ f → IsDatum M ψ cS Φ' f' → IsDatum M ψ cS (Φ + Φ') (f + f') :=
    fun h h' => GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz M ψ hstd cS _ _ _ _ h h'

  set Aop := aPlusAll (heisO ψ (sgn ε S) X) θ (fun τ => cplxO ((frSgn ε A).cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hfock : ∀ f P, fockF ψ θ ε A B f P = pureTensorL Aop f P := fun f P => rfl
  have step : ∀ g : WO S X → ℂ, (∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD g) →
      ∀ k, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (Aop k g) := by
    rintro g ⟨ΦD, hD, hd⟩ k
    obtain ⟨a, ha, h1⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
    obtain ⟨b, hb, h2⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2))
    refine ⟨((fockScale D k.1 : ℂ)⁻¹) • (a + (-Complex.I) • b),
      Submodule.smul_mem _ _ (add_mem ha (Submodule.smul_mem _ _ hb)), ?_⟩
    have e1 := isDatum_smul_smul M ψ cS (hadd h1 (isDatum_smul_smul M ψ cS h2 (-Complex.I))) ((fockScale D k.1 : ℂ)⁻¹)
    convert e1 using 1
    simp only [hAop, aPlusAll, aPlus, crea, sub_eq_add_neg, neg_smul]
  have gen : ∀ f, IsFinF ψ θ ε A B f → ∀ P, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (fockF ψ θ ε A B f P) := by
    intro f hf P
    have h0 := GlobalTheory.T.exists_algebraicDatum_thetaTransform_eq D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS f hf
    have hl : ∀ l : List (FVar D X.rank S.rank), ∃ ΦD ∈ algD M Bs.ψ Bs.emb,
        IsDatum M ψ cS ΦD (l.foldr (fun i g => Aop i g) f) := by
      intro l
      induction l with
      | nil => exact h0
      | cons k l ih => exact step _ ih k
    rw [hfock]
    induction P using MvPolynomial.induction_on' with
    | monomial u a =>
      have em : MvPolynomial.monomial u a = a • MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ u := by
        rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      obtain ⟨ΦD, hD, hd⟩ := hl (Multiset.toList (Finsupp.toMultiset u))
      refine ⟨a • ΦD, Submodule.smul_mem _ _ hD, ?_⟩
      rw [em, map_smul]
      unfold pureTensorL
      rw [Module.Basis.constr_basis]
      exact isDatum_smul_smul M ψ cS hd a
    | add p q hp hq =>
      obtain ⟨a, ha, h1⟩ := hp
      obtain ⟨b, hb, h2⟩ := hq
      exact ⟨a + b, add_mem ha hb, by rw [map_add (f := _)]; exact hadd h1 h2⟩
  have fin_mem : ∀ f, IsFinF ψ θ ε A B f → f ∈ algF ψ θ ε A B := by
    intro f hf
    refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
    have e1 : (1 : MvPolynomial (FVar D X.rank S.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    rw [hfock, e1]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
    simp [opPow]
  refine ⟨fun Φ hΦ => ?_, fun ΦD hΦD => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact gen f hf P
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩
  · have pure_add : ∀ (g g' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g + g') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ := by
      intro g g' φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    have pure_smul : ∀ (c : ℂ) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • g) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
      intro c g φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    have pure_zero : ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) φ = 0 := by
      intro φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    let N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) :=
      { carrier := {g | ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
          ∃ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f}
        zero_mem' := fun φ _ _ => ⟨0, zero_mem _, by rw [pure_zero]; exact isDatum_zero_zero M ψ cS⟩
        add_mem' := by
          intro g g' hg hg' φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          obtain ⟨b, hb, d2⟩ := hg' φ h1 h2
          exact ⟨a + b, add_mem ha hb, by rw [pure_add]; exact hadd d1 d2⟩
        smul_mem' := by
          intro c g hg φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [pure_smul]; exact isDatum_smul_smul M ψ cS d1 c⟩ }
    have hPol : M.Pol Bs.ψ Bs.emb ≤ N := by
      refine sInf_le ⟨fun g₀ hg₀ φ h1 h2 => ?_, fun u hu g hg g₁ hg₁ φ h1 h2 => ?_⟩
      · obtain ⟨f, hf, hd⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g₀ φ hg₀ h1 h2
        exact ⟨f, fin_mem f hf, hd⟩
      · obtain ⟨f, hf, hd⟩ := hg φ h1 h2
        exact GlobalTheory.T.exists_algebraicVector_thetaTransform_heisenbergDerivative D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g φ h1 h2 f hf hd u hu g₁ hg₁
    induction hΦD using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, φ, hg, h1, h2, rfl⟩ := hx
      exact hPol hg φ h1 h2
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩

end GlobalTheory.SquareAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicVectors_correspond_schrodinger_thetaMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD Φ) ∧
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, IsDatum M ψ cS ΦD Φ := by
  exact @GlobalTheory.SquareAgree.algVec_correspond
end
