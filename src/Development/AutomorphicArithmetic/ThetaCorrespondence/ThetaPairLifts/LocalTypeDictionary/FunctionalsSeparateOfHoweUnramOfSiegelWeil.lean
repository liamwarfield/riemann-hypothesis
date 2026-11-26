module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RealBranch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyHasModels
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SignedHC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SepRows
theorem separating_family_has_models : _root_.GlobalTheory.FunPr.ThetaLocalInputs → CoreModels := fun h => coreModels_of_upq h.discreteSeriesUpqExists
end GlobalTheory.SepRows
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_models : _root_.GlobalTheory.FunPr.ThetaLocalInputs → CoreModels := by
  first | exact @_root_.GlobalTheory.SepRows.separating_family_has_models | exact _root_.GlobalTheory.SepRows.separating_family_has_models | (intros; apply _root_.GlobalTheory.SepRows.separating_family_has_models <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealFunctionalsSeparateOfHypothesis
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselSeparate
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftsSeparateOfSeparatingData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
noncomputable section
namespace GlobalTheory.SepRows.SepProof
section
open Classical
end
set_option maxHeartbeats 1000000 in
open Classical in
theorem theta_lifts_separate_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → TopSep := by
  intro _
  unfold TopSep All
  intro D _ T L μ0 _ sc G W M hM S MB F' hF' Ψ hΨ
  have hθ : IsInfFam W.θ := W.θ_is
  set T' : MMap MB := PiTensorProduct.lift.symm F' with hT'
  have hT'm : T' ∈ Mult W.θ MB ∅ 1 := (mem_multT W.θ MB ∅ 1 F').1 hF'
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_meets_besselTopRationalOrbits W M hM
  have hφ : ∀ ξ, pairVec (coefPlus G W.θ) ξ Ψ ∈ contLeft (G.V (.top 0)) := fun ξ =>
    ⟨GlobalTheory.RowBplus.pairVec_cont G W.θ hθ ξ hΨ, fun γ hγ g => GlobalTheory.RowBplus.pairVec_left G W.θ ξ hΨ hγ g⟩
  have H := fun ξ => GlobalTheory.T.besselPeriodCorankOne_additive_bounded_compact W M hM Ω hΩc hΩ _ (hφ ξ)
  choose C hC using H
  have hadd := fun ξ => (hC ξ).1
  have hadd' := fun ξ => (hC ξ).2.1
  have hbd := fun ξ => (hC ξ).2.2
  have hTt : ∀ u : MB.Vec, F' (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : F' = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply F').symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT MB, F' x ∈ contLeft (G.V (.grid D.R.m 0)) := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft _).smul_mem r (GlobalTheory.Core.Mi.SepPer.mult_mem_contLeft W.θ MB ∅ 1 hT'm u)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact (contLeft _).add_mem hx hy
  have pv_add : ∀ ξ ξ', pairVec (coefPlus G W.θ) (ξ + ξ') Ψ = pairVec (coefPlus G W.θ) ξ Ψ + pairVec (coefPlus G W.θ) ξ' Ψ := by
    intro ξ ξ'; funext h; simp [pairVec_apply]
  have pv_smul : ∀ (a : ℂ) ξ, pairVec (coefPlus G W.θ) (a • ξ) Ψ = a • pairVec (coefPlus G W.θ) ξ Ψ := by
    intro a ξ; funext h; simp [pairVec_apply]
  have hBadd : ∀ ξ ξ' F, F ∈ contLeft (G.V (.grid D.R.m 0)) → Bplus W M (pairVec (coefPlus G W.θ) (ξ + ξ') Ψ) F =
      Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F + Bplus W M (pairVec (coefPlus G W.θ) ξ' Ψ) F := by
    intro ξ ξ' F hF; rw [pv_add]; exact hadd' ξ _ (hφ ξ') F hF
  have hBsmul : ∀ (a : ℂ) ξ F, Bplus W M (pairVec (coefPlus G W.θ) (a • ξ) Ψ) F = a * Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F := by
    intro a ξ F
    rw [pv_smul]; exact Bplus_smul_left W M a _ F
  have hBsmulR : ∀ (a : ℂ) φ F, Bplus W M φ (a • F) = a * Bplus W M φ F := by
    intro a φ F
    exact Bplus_smul_right W M a φ F
  refine ⟨⟨LinearMap.mk₂ ℂ (fun ξ v => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v))
      (fun ξ ξ' v => hBadd ξ ξ' _ (hmem v)) (fun a ξ v => hBsmul a ξ _)
      (fun ξ v v' => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_add v v')).trans (hadd ξ _ (hmem v) _ (hmem v')))
      (fun a ξ v => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_smul a v)).trans (hBsmulR a _ _)), fun ξ v => rfl⟩, ?_⟩
  intro Wt _ _ π e he τ x v
  have hE : ∀ (y y' : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (y + y'))) =
      e (PiTensorProduct.tprod ℂ (Function.update x τ y)) + e (PiTensorProduct.tprod ℂ (Function.update x τ y')) := by
    intro y y'; rw [MultilinearMap.map_update_add, map_add (f := _)]
  have hEs : ∀ (a : ℂ) (y : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (a • y))) =
      a • e (PiTensorProduct.tprod ℂ (Function.update x τ y)) := by
    intro a y; rw [MultilinearMap.map_update_smul, map_smul]; simp
  have hV : ∀ (u u' : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (u + u'))) =
      F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) + F' (PiTensorProduct.tprod ℂ (Function.update v τ u')) := by
    intro u u'; rw [MultilinearMap.map_update_add, map_add (f := _)]
  have hVs : ∀ (a : ℂ) (u : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (a • u))) =
      a • F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) := by
    intro a u; rw [MultilinearMap.map_update_smul, map_smul]; simp
  have hF1 : ∀ (g : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.grid D.R.m 0)).rank) ℂ),
      g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.grid D.R.m 0)) τ) → ∀ (x₁ y₁ : MB.sm τ), (y₁ : MB.H τ) = MB.rep τ g x₁ →
      F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁)) =
        rTr _ (atTau W.θ _ τ g) (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁))) := by
    intro g hg x₁ y₁ hy
    rw [hTt, hTt]
    have := mult_equiv W.θ MB ∅ 1 hT'm τ hg (Function.update v τ x₁) y₁ (by simpa using hy)
    simpa using this
  obtain ⟨Lw, Cu, hL, hb⟩ := GlobalTheory.Core.Mi.SepPer.mult_bound (θ := W.θ) hθ MB (∅ : Set (GA D (G.V (.grid D.R.m 0)))) 1 hT'm Ω hΩc τ v
  refine ⟨LinearMap.mk₂ ℂ (fun y u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))))
      (fun y y' u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hE y y')).trans (hBadd _ _ _ (hmem _)))
      (fun a y u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hEs a y)).trans (hBsmul _ _ _))
      (fun y u u' => (congrArg (Bplus W M _) (hV u u')).trans (hadd _ _ (hmem _) _ (hmem _)))
      (fun a y u => (congrArg (Bplus W M _) (hVs a u)).trans (hBsmulR _ _ _)), ⟨?_, ?_, ?_⟩, fun y u => rfl⟩
  · intro y
    have hℓ0 := fun (u u' : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hV u u')).trans
        (hadd _ _ (hmem _) _ (hmem _))
    have hℓ1 := fun (a : ℂ) (u : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hVs a u)).trans
        (hBsmulR a _ _)
    let ℓ₀ : MB.sm τ →ₗ[ℂ] ℂ :=
      { toFun := fun u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
          (F' (PiTensorProduct.tprod ℂ (Function.update v τ u)))
        map_add' := hℓ0
        map_smul' := hℓ1 }
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ u : MB.sm τ, ℓ u = Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
        (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))) := fun u => congrArg (fun m => m u) hℓ
    refine ⟨ℓ, ⟨Lw, C (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) * Cu, hL, fun w hw => ?_⟩, fun u => hℓw u⟩
    have hw' : w ∈ MB.sm τ := Submodule.subset_span hw
    have e1 : ℓ w = ℓ ((⟨w, hw'⟩ : MB.sm τ) : MB.H τ) := rfl
    rw [e1, hℓw]
    have := hbd (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) _ (hmem _) _
      (fun z hz => by rw [hTt]; exact hb ⟨w, hw'⟩ z hz)
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro h hh g hg hEm w x₁ y₁ hy
    have he1 := he τ h hh (Function.update x τ w) (Function.update x τ (π τ h w)) (by simp) (fun τ' hτ' => by simp [hτ'])
    have hp := pairVec_comp_rho (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ
      (atTau_mem_GinfC' W.θ _ τ h)
    have hemb : atTau W.θ (G.V (.grid D.R.m 0)) τ g = embTop G (atTau W.θ (G.V (.top 0)) τ h) :=
      (embRel_iff _ _ _).1 (GlobalTheory.T.embRel_atRealPlace_of_unitaryEmbedding D W.θ hθ _ _ _ τ h g hh hg hEm)
    show Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ (π τ h w)))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) =
      Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [he1, hp, hF1 g hg x₁ y₁ hy, hemb]
    exact GlobalTheory.T.besselPeriodCorankOne_simultaneous_rightTranslate W M hM _ (hφ _) _ (hmem _) _
  · intro u hu w x₁ y₁ hy
    show Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) = _ * Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [hF1 u hu.1 x₁ y₁ hy]
    exact GlobalTheory.T.besselPeriodCorankOne_rightTranslate_unipotent W M hM _ _ (hmem _) _ (GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic D W.θ hθ _ G.besTop.e τ u hu)
end GlobalTheory.SepRows.SepProof
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lifts_separate_points : _root_.GlobalTheory.FunPr.ThetaLocalInputs → TopSep := by
  first | exact @_root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data | exact _root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data | (intros; apply _root_.GlobalTheory.SepRows.SepProof.theta_lifts_separate_of_separating_data <;> assumption)
end
end

section
namespace UpperTheory.Lit
open GlobalTheory.SepRows
theorem bessel_separate_of_step_gap (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hT : RowTower) :
    SizeGap → GoodRows → RowConv → WeakSep → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
  Bur.separate_of_burGapPos burGapPos GlobalTheory.T.dualCoefSpace_isTensorOverRealPlaces (_root_.GlobalTheory.T.theta_lifts_separate_points P) hT
end UpperTheory.Lit
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCoreSurjectiveOfLocalComponents
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistEvenSurjectiveOfRepresentatives
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EvenOnto
theorem even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  intro hHC hCusp hDS hHCM hCW hHowe hWeil hSW hSWc hDoub hUnr D
  have hHecke := _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' hWeil hCusp hSW hSWc hDoub hUnr D
  obtain ⟨hFin, hMet⟩ := GlobalTheory.T.evenThetaChain_finiteDimensional_and_peterssonProducts hHC hCusp D
  obtain ⟨hEig, hPoV, hInd⟩ := GlobalTheory.T.even_theta_chain_spanned_params_of_value_independent hCusp D hFin hMet
  have hBd := GlobalTheory.T.evenRankChain_params_trivialBound_rapidDecay hCusp D
  obtain ⟨hSpan, hAdj⟩ := GlobalTheory.T.thetaLiftUpward_cuspSpan_and_adjoint hDS hHCM hCusp hCW D
  have hPar := GlobalTheory.T.evenThetaChainUpwardLift_heckeParam_transferred hCusp hHowe D
  have hRZ := GlobalTheory.T.evenThetaStep_realZeta_nonvanishing hDS hHCM D
  have hZN := GlobalTheory.T.evenThetaStep_semilocalZeta_ne_zero_of_real D hMet hRZ
  have hNe := GlobalTheory.T.upwardThetaLift_ne_zero_of_lValue_ne_zero D hHecke hMet hZN
  have hStep := GlobalTheory.T.even_theta_step_adjoint_nonzero_transferred_params D hFin hPoV hSpan hAdj hPar hNe
  exact GlobalTheory.T.evenRankThetaChainLift_surjective_of_adjoint_nonzero D hFin hMet hEig hInd hBd hStep
end GlobalTheory.EvenOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  first | exact @_root_.GlobalTheory.EvenOnto.even_surjective_of_representatives | exact _root_.GlobalTheory.EvenOnto.even_surjective_of_representatives | (intros; apply _root_.GlobalTheory.EvenOnto.even_surjective_of_representatives <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Twist.CoreOntoAssembly
theorem twist_core_surjective_of_local_components : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → CoreOnto := by
  intro hP hHCF hCRD hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG
  exact GlobalTheory.T.coreChain_lifts_surjective_of_evenRank
    (_root_.GlobalTheory.T.twist_even_surjective_of_representatives hHCF hCRD hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG)
    GlobalTheory.T.testGridCommonData_properties_hold GlobalTheory.T.testGridStageLatticesProperties_proof
    (GlobalTheory.T.core_chain_composites_exist_lift_combinations hDSC hHCM hCRD hCW GlobalTheory.T.dependence_fixed (_root_.GlobalTheory.T.exists_separating_models hP))
    GlobalTheory.T.definiteTopSpace_columnValues
end GlobalTheory.Twist.CoreOntoAssembly
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_core_surjective : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → CoreOnto := by
  first | exact @_root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components | exact _root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components | (intros; apply _root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RapidDecayOfSeparatingFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SepRows.RowRapidPf
theorem separating_family_rapid_decay : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowRapid := by
  intro hP hT D hq hs T L μ0 hL sc hc G W M hM M₀ hM₀ t ht w
  have ht' : t ∈ MultT W.θ M₀ ∅ 1 := multT_le_empty W.θ M₀ _ _ ht
  have key : ∀ ρ Φ n (h : n ≤ D.R.m),
      PathConv W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) (t w) ∧
        RapidDec (G.V (.grid n 0)) (part W M ρ Φ (t w) n h) := by
    intro ρ Φ n h
    obtain ⟨S, MB, -, -, vec, hv⟩ := hT D hq hs T L μ0 hL sc hc G W M hM M₀ hM₀ n h
    obtain ⟨F', hF', hF⟩ := hv t ht' Φ
    obtain ⟨hcv, heq⟩ := hF ρ w
    refine ⟨hcv, ?_⟩
    rw [heq]
    exact (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ S MB W.θ W.θ_is ∅ 1 F' hF' (vec ρ w)).2.2
  exact ⟨fun ρ Φ n h => (key ρ Φ n h).2, fun ρ Φ => (key ρ Φ D.R.m le_rfl).1⟩
end GlobalTheory.SepRows.RowRapidPf
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapid_decay_of_separating_family : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowRapid := by
  first | exact @_root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay | exact _root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay | (intros; apply _root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingModelsOfSeparatingData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SepRows
open Matrix
theorem separating_models_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowModels := by
  intro hP D _ _ T L μ0 _ sc hsc G W M _ i hi
  have hDS := hP.discreteSeriesUpqExists
  classical
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  ·
    rw [parRow_zero]
    have hV : (G.V (.grid 0 0)).SigOK := D.sp.Y_sig (min 0 D.R.m)
    refine exists_model_of_enum hDS hV (W.onb (.grid 0 0)) (W.cart (.grid 0 0)) (fun τ => ?_)
      (W.onb_is (.grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩)
    obtain ⟨lam, ε, hE, hH, -, hq⟩ := GlobalTheory.ChainModels.goodPar_parB D (min 0 D.R.m) (min_le_right _ _) τ
    have e : parB (Ptw D) (min 0 D.R.m) τ = parB (Ptw D) 0 τ := by rw [Nat.zero_min]
    rw [e] at hE
    exact ⟨lam, ε, hE, hH, hq⟩
  · rw [hsc]
    have hX : (Node.grid i 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
    have hv := G.isV hX (fun j e => by cases e; omega)
    refine exists_model_of_enum hDS hv.sigOK (W.onb (.grid i 0)) (W.cart (.grid i 0)) (fun τ => ?_) (W.onb_is _ hX)
    obtain ⟨hr, hc, hm⟩ := GlobalTheory.GridJoin.dualPar_shift_counts (if Odd (i + 0) then -(1 / 2) else 0)
      (GlobalTheory.GridParDCount.isRegular_parD D 1 τ hi (Nat.zero_le D.R.m))
    have hc' : (parRow D 1 i τ).card = (G.V (.grid i 0)).rank :=
      hc.trans ((GlobalTheory.GridParDCount.card_parD D 1 τ hi (Nat.zero_le _)).trans hv.rank.symm)
    obtain ⟨lam, ε, hE, hcount⟩ := GlobalTheory.GridJoin.exists_isEnum_of_regular hr hc'
    refine ⟨lam, ε, hE, isHCParam_dual_parV D i 0 τ lam ε hv.rank hE, ?_⟩
    rw [hcount, hv.sig]
    exact hm.trans (GlobalTheory.SignedHC.Model.nMinus_parD _ i 0)
end GlobalTheory.SepRows
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_models_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowModels := by
  first | exact @_root_.GlobalTheory.SepRows.separating_models_of_separating_data | exact _root_.GlobalTheory.SepRows.separating_models_of_separating_data | (intros; apply _root_.GlobalTheory.SepRows.separating_models_of_separating_data <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSeesawPairOfThetaData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PairIt
open GlobalTheory.Chain GlobalTheory.Chain.RealIt
theorem exists_seesaw_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx := by
  intro hPr D S S' aS aT hP V W M M' θ ψ hθ
  have hD := hPr.discreteSeriesCover
  have hH := hPr.harishChandraModules
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have hB := GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ =>
    exists_locIt_pair hX h1 h2 hB M M' τ (hP τ)
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, fun ω ⟨χS, χT, hω, he⟩ f hf => ?_⟩
  have hc := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2
    (fun τ => (hc τ).2.1) fun τ => (hc τ).2.2
end GlobalTheory.PairIt
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx := by
  first | exact @_root_.GlobalTheory.PairIt.exists_seesaw_pair | exact _root_.GlobalTheory.PairIt.exists_seesaw_pair | (intros; apply _root_.GlobalTheory.PairIt.exists_seesaw_pair <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConvergenceOfSeparatingFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowConvAll
theorem separating_family_converges : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowConv := by
  intro hP hT D hq hS T L μ0 hL sc hc G W M hM M₀ hM₀ t ht w ρ ξ Ψ hΨ Φ
  obtain ⟨S, MB, -, -, vec, hv⟩ := hT D hq hS T L μ0 hL sc hc G W M hM M₀ hM₀ D.R.m le_rfl
  obtain ⟨F', hF', hF⟩ := hv t (multT_le_empty _ _ _ _ ht) Φ
  obtain ⟨hconv, hpart⟩ := hF ρ w
  have hrow : (fun i : Fin D.R.m => W.datum ρ Φ (Fin.castLE (le_refl D.R.m) i)) = W.datum ρ Φ := by
    funext i; simp
  rw [hrow] at hconv
  have hth : thetaChi W M ρ Φ (t w) = F' (vec ρ w) := hpart
  refine ⟨hconv, ?_⟩
  rw [hth]
  have hA := (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ S MB W.θ W.θ_is ∅ 1 F' hF' (vec ρ w)).1
  exact GlobalTheory.RowBplus.bplusConv_col W M hM ξ Ψ hΨ _ hA.toIsAutFun
end GlobalTheory.RowConvAll
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_of_separating_family : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowConv := by
  first | exact @_root_.GlobalTheory.RowConvAll.separating_family_converges | exact _root_.GlobalTheory.RowConvAll.separating_family_converges | (intros; apply _root_.GlobalTheory.RowConvAll.separating_family_converges <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyExtendsByTwistedRow
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.PairLift GlobalTheory.ChainFr GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowArrow
variable {D : D7}
end GlobalTheory.RowArrow
open GlobalTheory.RowArrow in
theorem GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx → RowModels → RowStep := by
  intro pr hE _ D _ hS T L μ0 hL sc hc G W M hM i hi S S' MA MB e e' cA cB
  obtain ⟨X, hX, -, -, h3, h4, h5⟩ :=
    GlobalTheory.RealPlaceTheta.exists_record_theta_all pr.discreteSeriesCover pr.harishChandraModules
  have I := GlobalTheory.PairLift.inputs_of_chosenSeries pr.discreteSeriesCover pr.harishChandraModules pr.cuspRapidDecay pr.casselmanWallach D X hX
  have hP := GlobalTheory.PairLift.RuleLift.pairLifts D X I (GlobalTheory.PairLift.cuspAll_of_lowAll D X I
    (GlobalTheory.PairLift.lowAll_of_lowFock D X I (GlobalTheory.LowerMembersRule.lowFock D X I)))
  have rA : (Node.grid i 0).InRange D.R.m := ⟨hi.le, Nat.zero_le _⟩
  have rB : (Node.grid (i + 1) 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
  obtain ⟨FA, a1, a2⟩ := exists_frame _ _ _ (W.onb_is _ rA)
  obtain ⟨FB, b1, b2⟩ := exists_frame _ _ _ (W.onb_is _ rB)
  have b3 : (frSgn true FB).cart = G.cartS W.cart (.chi i 0) := funext fun τ => by
    rw [cart_frSgn, b1]; rfl
  have b4 : (frSgn true FB).onb = G.onS W.onb (.chi i 0) := b2
  have hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ)
      (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0)) (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) :=
    fun τ => by
      rw [e, e', hc, parRow_eq, parRow_eq]
      exact GlobalTheory.GridParD.pairPar_X D hS i 0 τ hi (Nat.zero_le _)
  have hη : ∀ τ, HasInfExp D L.eta τ (1 / 2) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have hχ : ∀ τ, HasInfExp D (G.ch.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => GlobalTheory.Grid.cen D τ (D.R.m - i)) (G.ch.chi_eq _ (by omega) (by omega))
      ⟨_, fun τ => by simp only [cen_eq, hc]; push_cast; rfl, G.ch.inf _ (by omega) (by omega)⟩ τ
  have hω : IsWeilExp W.ψ (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) 0))) (G.V (.grid i 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) (W.om (.chi i 0)) := by
    refine ⟨_, _, W.om_is (.chi i 0) rB, fun τ => ⟨?_, ?_⟩⟩
    · have r : (G.pS (.chi i 0)).rank = GlobalTheory.Grid.rkV D (i + 1) 0 := (node_isV G hL rB).rank
      rw [GridData.chrS, r]
      exact exp_att (hχ τ) (hη τ) _
    · have r : (G.pT (.chi i 0)).rank = GlobalTheory.Grid.rkV D i 0 := (node_isV G hL rA).rank
      rw [GridData.chrT, r]
      exact exp_att (hχ τ) (hη τ) _
  have hv := (W.vac_is i hi).2
  have v0 : IsVacF W.ψ W.θ (frSgn true FB) FA (W.vac i) := ⟨hv.theta, fun τ => by rw [b3, a1]; exact hv.fock τ⟩
  have n0 : W.vac i ≠ 0 := fun h => by
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
    have := h2 p hp
    simp [nrm2, h] at this
  have v1 : ∀ κ, IsVacF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) := fun κ => by
    obtain ⟨u, hu, h⟩ := W.cosVec_is
    have th := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) hv.theta
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hu
    refine ⟨th, fun τ => ?_⟩
    rw [b3, a1]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (h i hi κ) hv.theta th
      (hv.fock τ)
  obtain ⟨hν, h𝓕⟩ := (hM.row i hi.le).haar_fund
  obtain ⟨It, hIt⟩ := lifts_neg h3 h4 h5 hP hE W.θ_is W.ψ_std MA MB hR FA FB (cA.trans a1.symm) (cB.trans b1.symm) hω v0 n0 hν h𝓕
  refine ⟨It, fun F hF κ => ?_⟩
  obtain ⟨F', hF', h⟩ := hIt _ (v1 κ) F hF
  have ef : ∀ P, ptF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) P = W.fock (.chi i 0) (W.cosVec i κ) P := fun P => by
    unfold ptF
    rw [b3, b4, a1, a2]
    rfl
  simp only [ef] at h
  exact ⟨F', hF', fun P v => ⟨fun g => (h P v g).1, funext fun g => (h P v g).2⟩⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separating_family_extend_by_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx → RowModels → RowStep := by
  first | exact @_root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row | exact _root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row | (intros; apply _root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row <;> assumption)
end
end

section
namespace UpperTheory.Lit
theorem real_functionals_separate_of_hypothesis
    (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (realIn : Branch.RealInputE) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  have rowModels := _root_.GlobalTheory.T.exists_models_of_separating_data P
  have rowStep := _root_.GlobalTheory.T.separating_family_extend_by_twist P (_root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data P) rowModels
  have rowTower := GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow rowModels rowStep
  have conv := _root_.GlobalTheory.T.convergence_of_separating_family P rowTower
  have per := Branch.periodNe_of_eigen P.harishChandraModules P.casselmanWallach P.cuspRapidDecay realIn
  have onto := _root_.GlobalTheory.T.twist_core_surjective P P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover
    P.harishChandraModules P.casselmanWallach hHowe P.weilRepresentationUnitaryPair
    P.weilSiegelFormulaUnitary hSW P.doublingMethod P.unramifiedDoublingGL
  have weak := GlobalTheory.T.rowSeparation_by_realFunctionals_of_chain_steps GlobalTheory.T.largeScaleSizes_imply_gapConditions (_root_.GlobalTheory.T.exists_separating_models P) (_root_.GlobalTheory.T.rapid_decay_of_separating_family P rowTower) per onto
    (GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data GlobalTheory.T.dependence_fixed)
  exact _root_.UpperTheory.Lit.bessel_separate_of_step_gap P rowTower GlobalTheory.T.largeScaleSizes_imply_gapConditions GlobalTheory.T.goodRows_principalLevel_are_rows conv weak
end UpperTheory.Lit
end
end

section
noncomputable section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal
open scoped InnerProductSpace
namespace UpperTheory.Lit.Branch
variable {n : ℕ}
variable {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
  {mu : Fin n → ℝ} {B : ℝ}
end UpperTheory.Lit.Branch
end
namespace UpperTheory.Lit
theorem functionalsSeparate_of_howeUnram_of_siegelWeil (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hH : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent) : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
  _root_.UpperTheory.Lit.real_functionals_separate_of_hypothesis P hH hSW realInputE_holds
end UpperTheory.Lit
end
