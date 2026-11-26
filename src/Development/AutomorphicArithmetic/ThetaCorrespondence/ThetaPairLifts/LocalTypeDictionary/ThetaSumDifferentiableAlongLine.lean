module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridKernelPairingIndependentOfExpansion
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspTypeLiftApproxFockSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDer
theorem hasDerivAt_theta_sum_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hcm hψ hG hW γ hγ m f f₁ φ hφ hD u
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    fun i => ((hφ i).2.and hG.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ i (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i g => GlobalTheory.TensUniq.pure_mem_schA g (φ i) (hφ i).1 (hstd i)
  choose c g hcg using fun i => _root_.GlobalTheory.T.twisted_smoothLine_pure_weight hP M ψ χX χW om hcm hψ hG hW γ hγ (f i) (φ i) (hφ i).1 (hφ i).2
  have hc := fun i => (hcg i).1
  have hlim := fun i => (hcg i).2
  choose Λ hΛ using fun i => GlobalTheory.ThetaHeisCLM.exists_clm_thetaSum_rho_pure M ψ hψ hG u (φ i) (hφ i).1 (hφ i).2
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      = fun t => ∑ i, Λ i (c i t) := by
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hc]
    rw [rho_sum M ψ hψ u _ (fun i => hmem i _)]
    simp only [hΛ]
  have hg : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) := by
    intro i
    funext x
    have hR := GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hφ i).1 (hstd i)
    have h1 := hD i _ hR x
    have ev : Continuous fun s : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
      by
        have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
        have h2 := (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
          (fun j => evI F (x j))).comp h1
        exact h2
    have h2 : HasDerivAt (fun t : ℝ => c i t (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j))
        (g i (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      exact (((ev.tendsto (g i)).comp (hlim i)).mul_const _).congr' (Filter.Eventually.of_forall fun t => schwartz_diffQuotient_eval_mul_eq_slope _ _ _ t)
    have h3 : (fun t : ℝ => c i t (fun j => evI F (x j)) * ∏ᶠ v, φ i v fun j => evFin F v (x j)) =
        fun t => om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evI F) (⇑(f i)) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))) x := by
      funext t
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i t) (φ i) x = om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x
      rw [hc i t]
    rw [h3] at h2
    exact h2.unique h1
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) = ∑ i, Λ i (g i) := by
    rw [rho_sum M ψ hψ u _ (fun i => hmem i _)]
    simp only [← hg, hΛ]
  have hc0 : ∀ i, HasDerivAt (fun t => Λ i (c i t)) (Λ i (g i)) 0 := by
    intro i
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((Λ i).continuous.tendsto (g i) |>.comp (hlim i)).congr' (Filter.Eventually.of_forall fun t => ?_)
    simp [slope_def_module, map_sub, map_smul]
  rw [hcurve, hend]
  have := HasDerivAt.sum (u := Finset.univ) fun i _ => hc0 i
  simpa [Finset.sum_fn] using this
end GlobalTheory.ThetaLineDer
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_differentiable_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line | exact _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line | (intros; apply _root_.GlobalTheory.ThetaLineDer.hasDerivAt_theta_sum_along_line <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses
section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx _root_.Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
structure MultiplicityCoverHypotheses : Prop where
  cover : GlobalTheory.Published.DiscreteSeriesCover
  h1 : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems
  h3 : GlobalTheory.Published.HeckeLPartialContinuation
  multL : StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.CuspMult.MultEq z.R.toRealDat
  multW : StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → GlobalTheory.CuspMult.MultEq z.R.toRealDat ∧ Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)
end
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull
namespace GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem rowSum_of_hypotheses_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ t a => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.RowClaim.Test.pde_ne_q hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := GlobalTheory.RowClaim.Test.guard hS t
  obtain ⟨h1, h2, h3, h4, h5⟩ := GridChoice.sumOK_classes ch.W ch.S.toGridChoice t (ch.Phi a) hL
  obtain ⟨f1, f2, -⟩ := GridChoice.sumOK_flat_fin_ex hL ch.S.toGridChoice t (ch.Phi a) hde hc
  obtain ⟨v1, v2⟩ := GlobalTheory.T.gridKernelPairing_independent_of_expansion D T R.toLevCh ch.sc ch.G ch.W Set.univ ch.S.toGridChoice A.μ0 hL t trivial (ch.Phi a)
  exact
    { flat := f1
      flatA := fun w _ => flatIntegrable_aaVac_of_conductor ch.W w (hasConductor_psiAt_AA ch.W w)
      fin := f2
      ex := GridChoice.sumOK_ex hL ch.S.toGridChoice t (ch.Phi a) hde hc
      vec := v1
      indep := v2
      cls := h1
      gam := h2
      wts := h3
      br := h4
      read := h5 }
end GlobalTheory.RowClaim
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.SumOKK := by
  first | exact @_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt | exact _root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLinearBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
namespace GlobalTheory.RowEx
theorem twisted_linear_bound (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) : LinB := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hsc hch a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.twisted_base_change_lift_exists hP hL large₂ hS ch hch CF hsc a u
  exact ⟨h1, GlobalTheory.T.besselPeriodCorank_converges_column ch.W ch.M hch.vol ch.ξ _ (col_mem ch a) _ h2⟩
end GlobalTheory.RowEx
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtThetaSumAlongLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDerFirst
theorem hasDerivAt_thetaSum_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hG hW γ hγ m f f₁ φ hφ hD u
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    fun i => ((hφ i).2.and hG.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ i (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i g => GlobalTheory.TensUniq.pure_mem_schA g (φ i) (hφ i).1 (hstd i)
  have hpres := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).pres
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      = fun t => ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))) := by
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact GlobalTheory.ThetaLineDer.rho_sum M ψ hψ u _ (fun i => hpres _ _ (hmem i (f i)))
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) =
      ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f₁ i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j)))) :=
    GlobalTheory.ThetaLineDer.rho_sum M ψ hψ u _ (fun i => hmem i (f₁ i))
  have hi : ∀ i, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f₁ i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))) 0 :=
    fun i => _root_.GlobalTheory.T.thetaSum_differentiable_along_line hP M ψ χX χW om hψ hG hW γ hγ (f i) (f₁ i) _
      (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hφ i).1 (hstd i)) (hD i) u
  rw [hcurve, hend]
  have := HasDerivAt.sum (u := Finset.univ) fun i _ => hi i
  simpa [Finset.sum_fn] using this
end GlobalTheory.ThetaLineDerFirst
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistPolarizationDatumLieDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SquareAgree.DatA
theorem polarization_datum_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W X → ℂ), IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M ψ cA (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M ψ cA Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ hγ hL Φ Φ' hD T m f f₁ φ hf hA hΦ Φ'D hΦ'
  have hM := hT.geo.hM
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
    intro i
    filter_upwards [hM.std, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    rw [(hf i).2.2 v hvT, hv]
  have hrest : ∀ i, Rest (evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun i =>
    ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)⟩
  have hsum : ∀ g : Fin m → SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) = ∑ i, tens (evI D.host.F) (⇑(g i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun g =>
    Finset.sum_congr rfl fun i _ => GlobalTheory.EvZeroInf.pure_eq_tens _ _
  have hone : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW 1 = 1 := by
    apply Subtype.ext; simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]
  have hstdψ : IsStd ψ := hO.psi ▸ hT.base.std
  have hmem : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)
  have hDat : IsDatum Γ.M ψ cA (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) Φ' := by
    refine ⟨hmem, fun u => ?_⟩
    have h1 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))))) (Φ' (cA u)) 0 := by
      have h2 := hD (cA u)
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      have h3 := (hO.weilA _ _ hΦ 1 (oneP θ X τ Y t)).2 u
      rw [hone, ← hγ t] at h3
      exact h3
    have h4 := _root_.GlobalTheory.T.twisted_theta_line_derivative hP Bs Γ Xc om om' hT γ hL m f f₁ (fun i => GlobalTheory.EvZeroInf.finPart (φ i)) hrest hA u
    rw [← hsum, ← hsum, hO.psi] at h4
    exact h4.unique h1
  exact GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstdψ cA Φ'D _ Φ' hΦ' hDat
end GlobalTheory.SquareAgree.DatA
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_polarization_datum_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W X → ℂ), IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M ψ cA (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M ψ cA Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  first | exact @_root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative | exact _root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative | (intros; apply _root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftHasKType
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftPreservesType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaLiftTypeUp
theorem thetaLift_hasTypeAt : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hL hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint τ
  have hV : (G.P (i + 1)).V.SigOK := (hG.spaces.P (i + 1) (by omega)).sigOK
  intro C hC δ hδ
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ := _root_.GlobalTheory.T.twist_cuspType_lift_approx_fockSpace hL hP D hSz G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint C hC (δ / 2) (by linarith)
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hR hG
  choose F' hF' hE using fun l => hCA.up i hi (f l) (hf l) (F l) (hF l)
  have hψ0 : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ)
      (∑ l, F' l (G.ItU i (p l) (v l))) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ _ τ _).sum_mem fun l _ => _root_.GlobalTheory.T.cusp_value_has_prescribed_type hP R.θ hR.inf _ hV _ (hF' l) _ τ
  obtain ⟨ψ, hψ, hψC⟩ := hψ0 C hC (δ / 2) (by linarith)
  refine ⟨ψ, hψ, fun x hx => ?_⟩
  have h1 := happ x hx
  have h2 := hψC x hx
  have e : (∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω x g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F l (v l) g ∂(G.mP i).ν) = (∑ l, F' l (G.ItU i (p l) (v l))) x := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
  rw [e] at h1
  calc _ = ‖((∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω x g Φ) * φ g ∂(G.mP i).ν) - (∑ l, F' l (G.ItU i (p l) (v l))) x) + ((∑ l, F' l (G.ItU i (p l) (v l))) x - ψ x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring
end GlobalTheory.ThetaLiftTypeUp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_preserves_type : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.ThetaLiftTypeUp.thetaLift_hasTypeAt | exact _root_.GlobalTheory.ThetaLiftTypeUp.thetaLift_hasTypeAt | (intros; apply _root_.GlobalTheory.ThetaLiftTypeUp.thetaLift_hasTypeAt <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.UpTypeLift
theorem upward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, IsTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hc τ
  have hN := hG.spaces.P (i + 1) (by omega)
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hR.inf hN.sigOK (GlobalTheory.NodePar.goodPar_of_sigOK (G.P (i + 1)) hN.sigOK τ)
    (_root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc)
    (_root_.GlobalTheory.T.theta_lift_preserves_type hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc τ)
end GlobalTheory.UpTypeLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, IsTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType | exact _root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType | (intros; apply _root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsDarbouxBasisOfSymplecticPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
noncomputable section
namespace GlobalTheory.PairDarboux
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexOrder
theorem exists_darboux_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ ∧ GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ := by
  intro _ D ψ θ hψ _ ε M X A B χS χT ω eS eT hω _
  have hω' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε) := hω
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := GlobalTheory.AdelicU.isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  let τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w := fun w => ⟨_, hτf w⟩
  have hτ : ∀ w x, (τ w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  let Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank :=
    ⟨GlobalTheory.RealDict.sgE (D := D) ε • M.gram, ⊥, fun w => (if ε then 1 else -1 : ℂ) • A.cart (τf w), fun _ => 1⟩
  let Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank :=
    ⟨D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)), ⊥,
      fun w => (B.cart (τf w)).map conj, fun _ => 1⟩
  have hXJ : Xs.J = -(sgn ε M).gram := gram_neg_sgn ε M rfl
  have hWJ : Ws.J = D.host.xi0 • X.gramᵀ := rfl
  have hc : GlobalTheory.RealDict.sgE (D := D) ε ≠ 0 := by cases ε <;> simp [GlobalTheory.RealDict.sgE]
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hXh : ∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j := fun i j => by
    rw [hXJ]
    show star (-(sgn ε M).gram j i) = -(sgn ε M).gram i j
    rw [star_neg, GlobalTheory.TripleSpace.star_gram]
  have hXd : Xs.J.det ≠ 0 := by
    rw [hXJ]
    exact gram_det_ne (neg (sgn ε M))
  have hWs : ∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j := fun i j => by
    show star (D.host.xi0 * X.gram i j) = -(D.host.xi0 * X.gram j i)
    rw [star_mul', Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, GlobalTheory.TripleSpace.star_gram, neg_mul]
  have hWd : Ws.J.det ≠ 0 := by
    rw [hWJ, Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hξ) (gram_det_ne X)
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star (R := D.host.E) x
  obtain ⟨co, hrat⟩ := GlobalTheory.RatDarboux.exists_darboux (AF D.host.F) h2 D.sp.cm.sig hσ hXh hWs hXd hWd
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas M
  obtain ⟨hμ', h𝓕'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain M (J := Xs.J) _ hc rfl μ 𝓕 hμ h𝓕
  obtain ⟨o, ho⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E D.sp.cm.sig hcm
    (by haveI := GlobalTheory.InertOfConj.unram D; infer_instance)
  let Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws :=
    ⟨co, fun v => Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1,
      μ.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (J := Xs.J) _ rfl), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (J := Xs.J) _ rfl '' 𝓕⟩
  have hgood : Mo.IsGood ψ :=
    { rat := hrat
      vac := fun v => isVac_of_bot Mo rfl ψ o ho v
      std := Filter.Eventually.of_forall fun _ => rfl
      haar := hμ'
      dom := h𝓕' }
  obtain ⟨om, hom, htr⟩ := exists_weil_transp ψ ε M X Xs Ws rfl rfl Mo hrat χS χT ω hω
  refine ⟨Xs, Ws, Mo, ψ, χS, χT, om, τ, ⟨hcm, GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ, hXh, hXd, hWs, hWd,
    GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ hω'.resS, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ hω'.resT,
    hω'.hecS, hω'.hecT, hom, fun w => ?_, fun w => ?_⟩,
    ⟨rfl, rfl, rfl, fun w => ⟨τf w, hτ w, rfl, rfl⟩, hgood, htr⟩⟩
  · have h := GlobalTheory.TripleSpace.isCartan_neg_conj
      (isCartanInv_sgn ε M (τf w) (GlobalTheory.CompactFockAction.cart_isCartanInv A (τf w)))
    have e1 : Xs.J.map (τ w).1 = -((gramAt D (sgn ε M) (τf w)).map star) := by
      rw [hXJ]
      ext a b
      simp [gramAt, hτ]
    have e2 : Xs.θ w = -sgnM ε (A.cart (τf w)) := by
      cases ε <;> simp [Xs, sgnM]
    rw [e1, e2]
    exact h
  · have h := isCartan_conj (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (GlobalTheory.CompactFockAction.cart_isCartanInv B (τf w))
    have e0 : Complex.I * conj (tauE D (τf w) D.host.xi0) = ((tauE D (τf w) D.host.xi0).im : ℂ) := by
      apply Complex.ext <;> simp [Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero]
    have e1 : Complex.I • Ws.J.map (τ w).1 = ((tauE D (τf w) D.host.xi0).im : ℂ) • gramAt D X (τf w) := by
      ext a b
      have e3 : conj (tauE D (τf w) (X.gram b a)) = tauE D (τf w) (X.gram a b) := by
        rw [← GlobalTheory.TripleSpace.star_gram X b a]
        exact (hcm.2.2.2 (tauE D (τf w)) (X.gram b a)).symm
      show Complex.I * conj (tauE D (τf w) (D.host.xi0 * X.gram b a)) = _ * tauE D (τf w) (X.gram a b)
      rw [map_mul, map_mul, ← mul_assoc, e0, e3]
    rw [e1]
    exact h
end GlobalTheory.PairDarboux
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_darboux_basis_of_symplectic_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ ∧ GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ := by
  first | exact @_root_.GlobalTheory.PairDarboux.exists_darboux_pair | exact _root_.GlobalTheory.PairDarboux.exists_darboux_pair | (intros; apply _root_.GlobalTheory.PairDarboux.exists_darboux_pair <;> assumption)
end
end
