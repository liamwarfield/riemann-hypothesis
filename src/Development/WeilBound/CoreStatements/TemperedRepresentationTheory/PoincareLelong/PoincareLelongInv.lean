module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVarIntGraphX
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointChart
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneCompleteIntersection
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolydiscLelongLimit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionUnramifiedGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGoodPointBranches
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTransverseSliceGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelPlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIdentityAll

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDivisorCompare
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem chartDivisorCompare : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.proof GlobalTheory.T.segre_chart_integral_holds
    GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints.proof
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorLength

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LelongLimitAtBranches
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchIntDecompose
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem branchIntDecompose : GroundTheory.Heights₂.Heights.BranchIntDecompose.Statement :=
  GroundTheory.Heights₂.Heights.BranchIntDecompose.proof GlobalTheory.T.branch_proper_at_point_holds
    (GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof
      (GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof
        GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof
          GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof))
      GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.proof)
    GroundTheory.Heights₂.Heights.AutoClose.ChartIntSumOffHyperplane
    GroundTheory.Heights₂.Heights.Swarm.BranchChartInt.proof

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchInt
namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem paramChartInt : GroundTheory.Heights₂.Heights.ParamChartInt.Statement :=
  GroundTheory.Heights₂.Heights.ParamChartInt.proof
    (GroundTheory.Heights₂.Heights.ChartIntCountAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact)
    GroundTheory.Heights₂.Heights.ParamPieceInt.proof GroundTheory.Heights₂.Heights.ParamCritNull.proof
    GroundTheory.Heights₂.Heights.ParamOffRegularZero.proof GroundTheory.Heights₂.Heights.RegularInjectivePieces.proof
    GroundTheory.Heights₂.Heights.ParamDensIntegrable.proof

theorem sliceBranchInt : GroundTheory.Heights₂.Heights.SliceBranchInt.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranchInt.proof GlobalTheory.T.branch_proper_at_point_holds paramChartInt

end GlobalTheory.CompanionTheory.Ar.SliceBranch
end

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Lelong

open GroundTheory.Heights₂.Heights

theorem lelongLimitAtBranches : LelongLimitAtBranches.Statement :=
  LelongLimitAtBranches.proof GlobalTheory.CompanionTheory.Ar.branchIntDecompose GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranchInt
    PolydiscLelongLimit.proof GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint

end GlobalTheory.CompanionTheory.Ar.Lelong
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceReducedAwayZariski
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHolds
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem sliceBranches : GroundTheory.Heights₂.Heights.SliceBranches.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranches.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full
    GlobalTheory.T.branch_proper_at_point_holds
    GroundTheory.Heights₂.Heights.SliceMatricesOpen.full
    GroundTheory.Heights₂.Heights.ImplicitCurve.full

end GlobalTheory.CompanionTheory.Ar.SliceBranch
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_branches_holds : GroundTheory.Heights₂.Heights.SliceBranches.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | exact GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | (intros; apply GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchNormalisationHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchNormalisationHolds
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.BranchNorm

open MvPolynomial Filter Topology GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

theorem coordinateGraphNear_of_chart {n : ℕ} {X : Set (Fin n → ℂ)} {x : Fin n → ℂ}
    (A : (Fin n → ℂ) →L[ℂ] ℂ) (O : Set ℂ) (V : Set (Fin n → ℂ)) (g : ℂ → Fin n → ℂ)
    (hO : IsOpen O) (hV : IsOpen V) (hxV : x ∈ V) (hxX : x ∈ X) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hXV : X ∩ V = g '' O) : IsCoordinateGraphNear X x := by
  obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXV ▸ ⟨hxX, hxV⟩

  have hAd : ∀ y ∈ O, A (deriv g y) = 1 := by
    intro y hy
    have h1 : HasDerivAt (fun t ↦ A (g t)) (A (deriv g y)) y :=
      A.hasFDerivAt.comp_hasDerivAt y (hg y hy).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun t ↦ A (g t)) 1 y :=
      (hasDerivAt_id' y).congr_of_eventuallyEq (eventually_of_mem (hO.mem_nhds hy) hAg)
    exact h1.unique h2

  obtain ⟨i, hi⟩ : ∃ i, deriv g y₀ i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : deriv g y₀ = 0 := funext h
    simpa [h0] using hAd y₀ hy₀O
  set φ : ℂ → ℂ := fun y ↦ g y i with hφdef
  have hφ : AnalyticOnNhd ℂ φ O := fun y hy ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt (g y)).comp (hg y hy)
  have hφd : ∀ y ∈ O, HasDerivAt φ (deriv g y i) y := fun y hy ↦
    hasDerivAt_pi.1 (hg y hy).differentiableAt.hasDerivAt i

  set U : Set ℂ := O ∩ deriv φ ⁻¹' {0}ᶜ with hUdef
  have hU : IsOpen U := hφ.deriv.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hy₀U : y₀ ∈ U := ⟨hy₀O, by simpa [(hφd y₀ hy₀O).deriv] using hi⟩
  have hs : HasStrictDerivAt φ (deriv g y₀ i) y₀ := by
    simpa [(hφd y₀ hy₀O).deriv] using (hφ y₀ hy₀O).hasStrictDerivAt
  set e := ((hs.hasStrictFDerivAt_equiv hi).toOpenPartialHomeomorph φ).restrOpen U hU with hedef
  have he : ∀ y, e y = φ y := fun _ ↦ rfl
  have hsrc : ∀ {y}, y ∈ e.source → y ∈ U := fun hy ↦ hy.2
  have hy₀e : y₀ ∈ e.source := ⟨(hs.hasStrictFDerivAt_equiv hi).mem_toOpenPartialHomeomorph_source, hy₀U⟩
  refine ⟨hxX, V ∩ A ⁻¹' e.source ∩ (fun z ↦ z i) ⁻¹' e.target,
    (hV.inter (e.open_source.preimage A.continuous)).inter (e.open_target.preimage (continuous_apply i)),
    ⟨⟨hxV, ?_⟩, ?_⟩, i, e.target, fun t ↦ g (e.symm t), e.open_target, ?_, ?_, ?_⟩
  · show A x ∈ e.source
    rw [← hgy₀, hAg y₀ hy₀O]
    exact hy₀e
  · show x i ∈ e.target
    rw [← hgy₀, show g y₀ i = e y₀ from rfl]
    exact e.map_source hy₀e
  · intro t ht
    have hyt := hsrc (e.map_target ht)
    have hder : HasDerivAt e (deriv φ (e.symm t)) (e.symm t) :=
      (hφ _ hyt.1).differentiableAt.hasDerivAt
    exact ((hg _ hyt.1).differentiableAt.comp t
      (e.hasDerivAt_symm ht hyt.2 hder).differentiableAt).differentiableWithinAt
  · intro t ht
    exact e.right_inv ht
  · rintro z ⟨⟨hzV, hzA⟩, hzi⟩
    constructor
    · intro hzX
      obtain ⟨y, hyO, rfl⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
      have hye : y ∈ e.source := by simpa [hAg y hyO] using hzA
      refine ⟨hzi, ?_⟩
      show g (e.symm (e y)) = g y
      rw [e.left_inv hye]
    · rintro ⟨ht, hgz⟩
      have hyO := (hsrc (e.map_target ht)).1
      have : z ∈ X ∩ V := hXV ▸ ⟨_, hyO, hgz⟩
      exact this.1

theorem curveCoordinateGraph : CurveCoordinateGraph.Statement := by
  intro n I q _ hdim
  obtain ⟨N, hN, hNx⟩ := GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre n I q hdim
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨ε, hε, fun x hxZ hxb hxq ↦ ?_⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hZV⟩ := hNx x ⟨hxZ, hball hxb⟩ hxq
  exact coordinateGraphNear_of_chart A O V g hO hV hxV hxZ hg hAg hZV

theorem puncturedCurveDiscInverse : PuncturedCurveDiscInverse.Statement := by
  have hG := curveCoordinateGraph
  have hD := InjectiveHolomorphicDerivNeZero.proof
  intro n I q hrad hdim
  obtain ⟨ε, hε, hgraph⟩ := hG n I q hrad hdim
  refine ⟨ε, hε, fun φ σ₀ δ hδ hφd hφi hφZ hφε hφq ↦ ?_⟩
  have hσ₀ : σ₀ ∈ Metric.ball σ₀ δ := Metric.mem_ball_self hδ
  obtain ⟨-, W, hWo, hxW, i, V, g, -, -, -, hW⟩ := hgraph (φ σ₀) (hφZ hσ₀) hφε hφq
  set f : ℂ → ℂ := fun σ ↦ φ σ i with hf
  set D : Set ℂ := Metric.ball σ₀ δ ∩ φ ⁻¹' W with hDdef
  have hDo : IsOpen D := hφd.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hWo
  have hσD : σ₀ ∈ D := ⟨hσ₀, hxW⟩
  have hφg : ∀ σ ∈ D, g (f σ) = φ σ := fun σ hσ ↦ ((hW _ hσ.2).1 (hφZ hσ.1)).2
  have hfd : DifferentiableOn ℂ f D := (differentiableOn_pi.1 hφd i).mono Set.inter_subset_left
  have hfi : Set.InjOn f D := fun s hs t ht h ↦ hφi hs.1 ht.1 (by rw [← hφg s hs, ← hφg t ht, h])
  have hfa : AnalyticAt ℂ f σ₀ := hfd.analyticAt (hDo.mem_nhds hσD)
  have hf' : deriv f σ₀ ≠ 0 := hD D f hDo hfd hfi σ₀ hσD
  set h := hfa.hasStrictDerivAt.localInverse f (deriv f σ₀) σ₀ hf' with hhdef
  have hha : AnalyticAt ℂ h (f σ₀) := hfa.analyticAt_localInverse hf'
  have hh0 : h (f σ₀) = σ₀ := HasStrictFDerivAt.localInverse_apply_image ..
  have hev : ∀ᶠ y in 𝓝 (f σ₀), AnalyticAt ℂ h y ∧ f (h y) = y ∧ h y ∈ D :=
    hha.eventually_analyticAt.and ((hfa.hasStrictDerivAt.eventually_right_inverse hf').and
      (hha.continuousAt.preimage_mem_nhds (by rw [hh0]; exact hDo.mem_nhds hσD)))
  obtain ⟨T, hTsub, hTo, hT⟩ := mem_nhds_iff.1 hev
  refine ⟨W ∩ (fun z ↦ z i) ⁻¹' T, hWo.inter (hTo.preimage (continuous_apply i)), ⟨hxW, hT⟩,
    fun z ↦ h (z i), fun z hz ↦ ?_, fun z ⟨hzZ, hzW, hzT⟩ ↦ ?_⟩
  · exact ((hTsub hz.2).1.differentiableAt.comp z (differentiableAt_apply i z)).differentiableWithinAt
  · obtain ⟨-, hfh, hhD⟩ := hTsub hzT
    refine ⟨h (z i), hhD.1, ?_, rfl⟩
    rw [← hφg _ hhD, hfh]
    exact ((hW z hzW).1 hzZ).2

theorem normalCurveBranchOrder : NormalCurveBranchOrder.Statement :=
  NormalCurveBranchOrder.proof NormalCurvePointDVR.proof GroundTheory.Heights₂.Heights.AutoClose.UniformiserBranchSimpleZero

theorem normalModelOpenMappingCurve (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (U : Set (Fin 1 → ℂ)) (φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ)
    (_hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ))
    (hU : IsOpen U) (hφd : DifferentiableOn ℂ φ U) (hφi : Set.InjOn φ U)
    (hφZ : Set.MapsTo φ U (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal)) :
    ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ φ '' U = IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ O := by
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have key : ∀ τ ∈ U, ∃ W : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen W ∧ φ τ ∈ W ∧
      IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ W ⊆ φ '' U := by
    intro τ hτ
    obtain ⟨A, O, V, g, hO, hV, hwV, hg, hAg, hZV⟩ :=
      GroundTheory.Heights₂.Heights.AutoClose.NormalCurveRegularPoint (Fin n ⊕ Fin M.m) M.ideal (φ τ) M.isPrime
        M.isIntegrallyClosed hdim' (hφZ hτ)
    set D : Set (Fin 1 → ℂ) := U ∩ φ ⁻¹' V with hD
    have hDo : IsOpen D := hφd.continuousOn.isOpen_inter_preimage hU hV
    have hφg : ∀ σ ∈ D, ∃ y ∈ O, g y = φ σ := fun σ hσ ↦ by
      have : φ σ ∈ g '' O := hZV ▸ ⟨hφZ hσ.1, hσ.2⟩
      exact this
    have hgA : ∀ σ ∈ D, g (A (φ σ)) = φ σ := fun σ hσ ↦ by
      obtain ⟨y, hy, hyφ⟩ := hφg σ hσ
      rw [← hyφ, hAg y hy]
    have hhd : DifferentiableOn ℂ (fun σ ↦ A (φ σ)) D :=
      A.differentiable.comp_differentiableOn (hφd.mono Set.inter_subset_left)
    have hhi : Set.InjOn (fun σ ↦ A (φ σ)) D := fun s hs t ht h ↦
      hφi hs.1 ht.1 (by rw [← hgA s hs, ← hgA t ht]; exact congrArg g h)
    have hopen : IsOpen ((fun σ ↦ A (φ σ)) '' D) :=
      GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_open_holds 1 D _ hDo hhd hhi
    refine ⟨V ∩ A ⁻¹' ((fun σ ↦ A (φ σ)) '' D), hV.inter (hopen.preimage A.continuous),
      ⟨hwV, τ, ⟨hτ, hwV⟩, rfl⟩, ?_⟩
    rintro z ⟨hzZ, hzV, σ, hσ, hσz⟩
    obtain ⟨y, hy, rfl⟩ : z ∈ g '' O := hZV ▸ ⟨hzZ, hzV⟩
    refine ⟨σ, hσ.1, ?_⟩
    rw [← hgA σ hσ]
    have : A (φ σ) = y := hσz.trans (hAg y hy)
    rw [this]
  choose! W hWo hWm hWs using key
  refine ⟨⋃ τ ∈ U, W τ, isOpen_biUnion fun τ hτ ↦ hWo τ hτ, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    exact ⟨hφZ hτ, Set.mem_biUnion hτ (hWm τ hτ)⟩
  · rintro z ⟨hzZ, hz⟩
    obtain ⟨τ, hτ, hzW⟩ := Set.mem_iUnion₂.1 hz
    exact hWs τ hτ ⟨hzZ, hzW⟩

def BranchLiftCurve : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (γ : VarBranch J 1 p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) →
    ∃ Γ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ,
      DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) ∧
      (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords (Γ τ) = γ.toFun τ) ∧
      ∀ V ⊆ Metric.ball 0 γ.radius, IsOpen V →
        ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ Γ '' V = IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ O

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets in
theorem branchLiftCurve : BranchLiftCurve := by
  have hR := RiemannExtensionAnalytic.proof
  have hB := GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds
  have hP := NormalModelProper.proof
  have hO := normalModelOpenMappingCurve
  intro n J p M γ hJ hdim
  set Δ := Metric.ball (0 : Fin 1 → ℂ) γ.radius with hΔ
  have hγd : DifferentiableOn ℂ γ.toFun Δ := γ.differentiableOn
  have hγZ : ∀ τ ∈ Δ, γ.toFun τ ∈ zeroSetIn J := fun τ hτ => γ.mapsTo hτ
  choose a b hbJ hab using M.birational
  have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, Differentiable ℂ (fun z : Fin n → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq =>
      simp only [eval_add]
      exact hp.add hq
    | mul_X p i hp =>
      simp only [eval_mul, eval_X]
      exact hp.mul (differentiable_apply i)
  have hcomp : ∀ q, DifferentiableOn ℂ (fun τ => eval (γ.toFun τ) q) Δ := fun q =>
    (hpoly q).comp_differentiableOn hγd
  set g : (Fin 1 → ℂ) → ℂ := fun τ => eval (γ.toFun τ) (∏ i, b i) with hg
  have hBJ : (∏ i, b i) ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  have hgne : ∀ V, IsOpen V → V ⊆ Δ → V.Nonempty → ∃ t ∈ V, g t ≠ 0 := fun V hV hVΔ hne =>
    hB n 1 J _ V γ.toFun hJ hdim hBJ hV hne (hγd.mono hVΔ) (γ.injOn.mono hVΔ)
      fun τ hτ => hγZ τ (hVΔ hτ)
  have hbne : ∀ τ, g τ ≠ 0 → ∀ i, eval (γ.toFun τ) (b i) ≠ 0 := fun τ hτ i h =>
    hτ (by simp only [hg, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)
  set f : Fin M.m → (Fin 1 → ℂ) → ℂ := fun i τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)
  have hgraph : ∀ τ ∈ Δ, g τ ≠ 0 → (Sum.elim (γ.toFun τ) fun i => f i τ) ∈ zeroSetIn M.ideal :=
    fun τ hτ hgτ => M.graph_mem_zeroSetIn a b hab _ (hγZ τ hτ) (hbne τ hgτ)
  have hfd : ∀ i, DifferentiableOn ℂ (f i) (Δ ∩ {t | g t ≠ 0}) := fun i τ hτ => by
    have h1 := (hcomp (a i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    have h2 := (hcomp (b i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    show DifferentiableWithinAt ℂ (fun τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)) _ τ
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv (hbne τ hτ.2 i))
  have hbdd : ∀ i, ∀ τ ∈ Δ, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f i '' (N ∩ Δ ∩ {t | g t ≠ 0})) := by
    intro i τ hτ
    obtain ⟨ε, hε, hεΔ⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball τ hτ
    have hsub : Metric.closedBall τ (ε / 2) ⊆ Δ :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεΔ
    have hK : Bornology.IsBounded (γ.toFun '' Metric.closedBall τ (ε / 2)) :=
      ((isCompact_closedBall τ (ε / 2)).image_of_continuousOn (hγd.continuousOn.mono hsub)).isBounded
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hP n J M _ hK)
    refine ⟨Metric.closedBall τ (ε / 2), Metric.closedBall_mem_nhds τ (by linarith),
      isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩⟩
    rintro _ ⟨t, ⟨⟨ht, htΔ⟩, hgt⟩, rfl⟩
    have hw := hC _ ⟨hgraph t htΔ hgt, ⟨t, ht, rfl⟩⟩
    exact (norm_le_pi_norm (Sum.elim (γ.toFun t) fun i => f i t) (Sum.inr i)).trans hw
  choose F hFd hFeq using fun i => hR 1 Δ g (f i) Metric.isOpen_ball
    ((hpoly _).comp_differentiableOn hγd) hgne (hfd i) (hbdd i)
  set Γ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ := fun τ => Sum.elim (γ.toFun τ) fun i => F i τ with hΓ
  have hΓd : DifferentiableOn ℂ Γ Δ := by
    refine differentiableOn_pi.2 fun s => ?_
    rcases s with j | i
    · simpa [hΓ] using differentiableOn_pi.1 hγd j
    · simpa [hΓ] using hFd i
  have hdense : Δ ⊆ closure (Δ ∩ {t | g t ≠ 0}) := by
    intro τ hτ
    rw [mem_closure_iff]
    intro o ho hτo
    obtain ⟨t, ⟨hto, htΔ⟩, hgt⟩ := hgne (o ∩ Δ) (ho.inter Metric.isOpen_ball)
      Set.inter_subset_right ⟨τ, hτo, hτ⟩
    exact ⟨t, hto, htΔ, hgt⟩
  have hΓZ : ∀ τ ∈ Δ, Γ τ ∈ zeroSetIn M.ideal := by
    intro τ hτ q hq
    have heq : Set.EqOn (fun t => eval (Γ t) q) (fun _ => (0 : ℂ)) (Δ ∩ {t | g t ≠ 0}) := by
      intro t ht
      have hΓt : Γ t = Sum.elim (γ.toFun t) fun i => f i t := by
        simp only [hΓ]
        congr 1
        funext i
        exact hFeq i ht
      simp only [hΓt]
      exact hgraph t ht.1 ht.2 q hq
    exact heq.of_subset_closure ((MvPolynomial.continuous_eval q).comp_continuousOn hΓd.continuousOn)
      continuousOn_const Set.inter_subset_left hdense hτ
  have hΓinj : Set.InjOn Γ Δ := fun s hs t ht hst =>
    γ.injOn hs ht (by
      have := congrArg firstCoords hst
      exact this)
  refine ⟨Γ, hΓd, fun τ hτ => ⟨hΓZ τ hτ, rfl⟩, fun V hV hVo => ?_⟩
  exact hO n J M V Γ hJ hdim hVo (hΓd.mono hV) (hΓinj.mono hV) fun τ hτ => hΓZ τ (hV hτ)

theorem primeBranchPlace : PrimeBranchPlace.Statement := by
  have hD := PrimeBranchDimOne.proof
  have hL := branchLiftCurve
  have hA := NormalModelPlace.proof
  have hO := normalCurveBranchOrder
  intro n J q c hJ hdim
  have hdim1 := hD n J q c hJ hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n J q M c hJ hdim1
  have hr := c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 c.radius := Metric.mem_ball_self hr

  have hinj : Set.InjOn Γ (Metric.ball 0 c.radius) := fun a ha b hb hab ↦
    c.injOn ha hb (by rw [← (hΓ a ha).2, ← (hΓ b hb).2, hab])
  obtain ⟨P, hP⟩ := hA n J q M (Γ 0) hJ (hΓ 0 h0).1 ((hΓ 0 h0).2.trans c.map_zero)
  refine ⟨P, fun f ↦ ?_⟩
  rw [hP f, hO n J M (Γ 0) c.radius Γ hJ hdim1 hr hΓd hinj (fun τ hτ ↦ (hΓ τ hτ).1) rfl]

  unfold branchOrder
  apply analyticOrderAt_congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
  have hτ' : (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
    rw [mem_ball_zero_iff] at hτ ⊢
    exact (pi_norm_const_le τ).trans_lt hτ
  rw [eval_rename, ← (hΓ _ hτ').2]
  rfl

theorem sameOrderBranchesMeet : SameOrderBranchesMeet.Statement := by
  have hC := GroundTheory.Heights₂.Heights.AutoClose.BranchInCurveComponent
  have hO := GroundTheory.Heights₂.Heights.AutoClose.SameOrdersLiftCentre
  have hL := branchLiftCurve
  intro n I q c c' _ hdim hord
  obtain ⟨J, hJmin, hJdim, hev⟩ := hC n I q c hdim
  have hJ : J.IsPrime := hJmin.1.1
  have htop : ∀ f ∈ J, branchOrder c f = ⊤ := fun f hf ↦ by
    refine analyticOrderAt_eq_top.2 ?_
    have hι : Tendsto (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (𝓝 0) (𝓝 0) :=
      (continuous_pi fun _ ↦ continuous_id).tendsto' _ _ rfl
    filter_upwards [hι.eventually hev] with τ hτ using hτ f hf
  have hev' := c'.eventually_mem_zeroSet J fun f hf ↦ (hord f).symm.trans (htop f hf)
  obtain ⟨ε, hε, hεJ⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', hεJ'⟩ := Metric.eventually_nhds_iff_ball.1 hev'
  let γ := c.restrictInto J ε hε hεJ
  let γ' := c'.restrictInto J ε' hε' hεJ'
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n J q M γ hJ hJdim
  obtain ⟨Γ', hΓ'd, hΓ', hΓ'o⟩ := hL n J q M γ' hJ hJdim
  have hw : Γ 0 = Γ' 0 := hO n J q M γ γ' Γ Γ' hJ hJdim hΓd hΓ hΓ'd hΓ' hord
  obtain ⟨U, hUo, hU⟩ := hΓ'o _ subset_rfl Metric.isOpen_ball
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 γ.radius := Metric.mem_ball_self γ.radius_pos
  have hΓ0U : Γ 0 ∈ U := by
    rw [hw]
    exact (hU ▸ Set.mem_image_of_mem Γ' (Metric.mem_ball_self γ'.radius_pos)).2
  have hcont : ContinuousAt Γ 0 := hΓd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 γ.radius_pos)
  have hnear : ∀ᶠ τ in 𝓝[≠] (0 : Fin 1 → ℂ), τ ≠ 0 ∧ τ ∈ Metric.ball 0 γ.radius ∧ Γ τ ∈ U := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 γ.radius_pos),
      nhdsWithin_le_nhds (hcont.preimage_mem_nhds (hUo.mem_nhds hΓ0U))] with τ h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨τ, hτ0, hτ, hτU⟩ := hnear.exists
  obtain ⟨τ', hτ', hτ'eq⟩ : Γ τ ∈ Γ' '' Metric.ball 0 γ'.radius := hU ▸ ⟨(hΓ τ hτ).1, hτU⟩
  have hτc : τ ∈ Metric.ball 0 c.radius := Metric.ball_subset_ball (min_le_right _ _) hτ
  refine ⟨c.toFun τ, ⟨⟨τ, hτc, rfl⟩, ⟨τ', Metric.ball_subset_ball (min_le_right _ _) hτ', ?_⟩⟩, fun hq ↦ hτ0 ?_⟩
  · have e1 := (hΓ' τ' hτ').2
    have e2 := (hΓ τ hτ).2
    rw [hτ'eq] at e1
    exact e1.symm.trans e2
  · exact c.injOn hτc (Metric.mem_ball_self c.radius_pos) (hq.trans c.map_zero.symm)

theorem primePlaceBranchExists : PrimePlaceBranchExists.Statement :=
  PrimePlaceBranchExists.proof
    (NormalModelPointOfPlace.proof NormalisationModelLocalization.full ModelLocalizationMaximalPoint.proof
      LocalizationAtPrimeQuotient.proof)
    GroundTheory.Heights₂.Heights.AutoClose.NormalModelDisc NormalModelProjectionLocallyInjective.proof normalCurveBranchOrder

theorem placeHasBranch : PlaceHasBranch.Statement :=
  PlaceHasBranch.proof
    (PlaceBranchExists.proof GroundTheory.Heights₂.Heights.AutoClose.PlaceOnComponent primePlaceBranchExists)
    (PuncturedBranchInOneBranch.proof
      (BranchImageNhdOffCentre.proof GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre))
    (PuncturedBranchSameOrder.proof puncturedCurveDiscInverse)

theorem branchNormalisation : BranchNormalisation.Statement :=
  BranchNormalisation.proof GroundTheory.Heights₂.Heights.AutoClose.BranchGermDimOne
    (BranchPlace.proof BranchInComponent.proof primeBranchPlace MinimalPrimePlace.proof)
    sameOrderBranchesMeet placeHasBranch GroundTheory.Heights₂.Heights.AutoClose.OrdDeterminesPlace
    CurveResidueDegree.proof OrdFiniteNonZeroDivisor.proof

end

end GlobalTheory.CompanionTheory.BranchNorm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchNormalisationHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branch_normalisation_holds : GroundTheory.Heights₂.Heights.BranchNormalisation.Statement := by
  first | exact @GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation | exact GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation | (intros; apply GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHolds
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.CurveBranch

theorem curveBranchLength_of_branchNormalisation
    (hB : GroundTheory.Heights₂.Heights.BranchNormalisation.Statement) :
    GroundTheory.Heights₂.Heights.CurveBranchLength.Statement :=
  GroundTheory.Heights₂.Heights.CurveBranchLength.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationLength hB

theorem curveBranchLength : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement :=
  curveBranchLength_of_branchNormalisation GlobalTheory.T.branch_normalisation_holds

end GlobalTheory.CompanionTheory.Heights.CurveBranch
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_branch_length_holds : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | exact GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | (intros; apply GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength <;> assumption)
end
end

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.BranchOrder

open GroundTheory.Heights₂.Heights

theorem sliceReducedAwayZariski : SliceReducedAwayZariski.Statement :=
  @SliceReducedAwayZariski.proof AutoClose.GenericFibreRadicalAway SliceBundleRadicalAway.proof

theorem sliceReducedAway : SliceReducedAway.Statement :=
  @SliceReducedAway.proof sliceReducedAwayZariski

theorem sliceUnmixedGeneral : SliceUnmixedGeneral.Statement :=
  @SliceUnmixedGeneral.proof AutoClose.CMHeightOneGeneral LocalDimDomain.proof
    AutoClose.SliceLocalDimGeneral AutoClose.SliceCMUnmixed

theorem sliceReducedGeneral : SliceReducedGeneral.Statement :=
  @SliceReducedGeneral.proof sliceUnmixedGeneral sliceReducedAway

theorem sliceMultGeneral : SliceMultGeneral.Statement :=
  @SliceMultGeneral.proof AutoClose.CMGeneralPoint TransverseSliceGeneral.proof AutoClose.LengthTransverseSlice

theorem sliceLength : SliceLength.Statement :=
  @SliceLength.proof IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full sliceReducedGeneral sliceMultGeneral

theorem localOrder : LocalOrder.Statement :=
  LocalOrder.proof sliceLength GlobalTheory.T.slice_branches_holds GlobalTheory.T.curve_branch_length_holds

end GlobalTheory.CompanionTheory.Heights.BranchOrder
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisorGeneralPointBranches
namespace GlobalTheory.CompanionTheory.ComplexSets


open GroundTheory.Heights₂.Heights in
theorem divisorGeneralPointBranches : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement :=
  DivisorGeneralPointBranches.proof DivisorOneComponent.proof
    (DivisorBranches.proof IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof
      GroundTheory.Heights₂.Heights.AutoClose.DivisorRegularGeneric
      (NormalDivisorChartGeneric.proof
        (NormalModelDivisorChartGeneric.proof
          (NormalModelGoodPointGeneric.proof NormalCodimOneCompleteIntersection.proof
            NormalCodimOneUniformiser.proof JacobianRankOffHypersurface.proof
            ProjectionUnramifiedGeneric.proof)
          NormalModelGoodPointChart.proof))
      NormalDoublePointsGeneric.proof DivisorGoodPointBranches.proof)

end GlobalTheory.CompanionTheory.ComplexSets
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableAbsFibreSumOfIsCxVar
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConePtsSubsetMcPtsOfMinimal
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem conePts_subset_mcPts_of_minimal {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) : conePts Q ⊆ mcPts P := fun _ hz =>
  ⟨hz.1, fun f hf => hz.2 _ (hQ.1.2 (Ideal.mem_map_of_mem _ hf))⟩

theorem exists_minimal_of_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ∃ Q ∈ (cxIdeal P).minimalPrimes, z ∈ conePts Q := by
  have hz' : z ∈ conePts (cxIdeal P) := by rw [← mcPts_eq_conePts]; exact hz
  have hle : cxIdeal P ≤ RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ) :=
    fun f hf => RingHom.mem_ker.2 (hz'.2 f hf)
  have : (RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, hQ, hz'.1, fun f hf => RingHom.mem_ker.1 (hQle hf)⟩

theorem mem_conePts_of_segre_eq {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (hs : segre z = segre z') : z' ∈ conePts Q := by
  classical
  choose i0 hi0 using hz.1
  obtain ⟨-, h4⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
  have hJ := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResBridge.isMultiHomogIdeal_of_mem_minimalPrimes hP hQ
  have h5 := ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hJ (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z hz.2
  refine ⟨hz', fun f hf => ?_⟩
  rw [h4]
  exact h5 f hf

theorem isSheet_of_isSetSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSetSheet (conePts Q) Ψ y w γ) : IsSheet P Ψ y w γ :=
  ⟨h.1, h.2.mono fun _ h' => ⟨h'.1, conePts_subset_mcPts_of_minimal hQ h'.2.1, h'.2.2⟩⟩

theorem isSetSheet_of_isSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hone : ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q → z ∈ conePts Q' →
      Ψ (segre z) = Fin.cons 1 y → Q' = Q)
    (hw : w ∈ setFibre (conePts Q) Ψ y) (h : IsSheet P Ψ y w γ) :
    IsSetSheet (conePts Q) Ψ y w γ := by
  obtain ⟨z, hz, hzw, -⟩ := hw
  obtain ⟨hd, hm, hΨγ⟩ := h.2.self_of_nhds
  have hγQ : γ y ∈ conePts Q := mem_conePts_of_segre_eq hP hQ hz hm.1 (hzw.trans h.1.symm)
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hev : ∀ᶠ y' in 𝓝 y, ∀ Q' ∈ (cxIdeal P).minimalPrimes, Q' ≠ Q → γ y' ∉ conePts Q' := by
    refine (Filter.eventually_all_finite hfin).2 fun Q' hQ' => ?_
    by_cases hne : Q' = Q
    · exact Eventually.of_forall fun _ h' => absurd hne h'
    have hnot : γ y ∉ conePts Q' := fun hc => hne (hone Q' hQ' _ hγQ hc hΨγ)
    obtain ⟨f, hf, hf0⟩ : ∃ f ∈ Q', eval (γ y) f ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hnot ⟨hm.1, hcon⟩
    have hc : ContinuousAt (fun y' => eval (γ y') f) y :=
      (MvPolynomial.continuous_eval f).continuousAt.comp hd.continuousAt
    filter_upwards [hc.eventually_ne hf0] with y' hy' _ hmem
    exact hy' (hmem.2 f hf)
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, hev] with y' h1 h2
  obtain ⟨Q', hQ', hz'⟩ := exists_minimal_of_mem_mcPts h1.2.1
  by_cases hne : Q' = Q
  · subst hne
    exact ⟨h1.1, hz', h1.2.2⟩
  · exact absurd hz' (h2 Q' hQ' hne)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCxVarOfMemMinimalPrimesCxIdeal
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

theorem isCxVar_of_mem_minimalPrimes_cxIdeal :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (d + 1) →
    ∀ Q ∈ (cxIdeal P).minimalPrimes, IsCxVar Q d ∧
      Q.comap (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P := by
  classical
  intro K _ ι _ P d hP Q hQ
  obtain ⟨hK, ⟨hPp, hPm, hPr⟩, hPh, hdim⟩ := hP
  have hc : Q.comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P :=
    GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.comap_of_minimal P hPh Q hQ
  have hCm : IsMultiHomogIdeal (cxIdeal P) := by
    obtain ⟨T, hT, hPT⟩ := hPm
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [cxIdeal, hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩
  have hQm : IsMultiHomogIdeal Q :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearCover.isMultiHomogIdeal_of_mem_minimalPrimes hCm hQ
  have hQr : IsRelevant Q := fun k => by
    obtain ⟨i, hi⟩ := hPr k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hc, Ideal.mem_comap, MvPolynomial.map_X]
    exact hX
  have hP' : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [hPh] at this
    exact this
  obtain ⟨hQp, -, hQdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have hmapP : cxIdeal P =
      (ReciprocityTheory.AnForm.R.extQ P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [cxIdeal, GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.map_int_complex_eq, ← Ideal.map_map]
    rfl
  have hQ' := hQ
  rw [hmapP] at hQ'
  refine ⟨⟨hK, ⟨hQ.1.1, hQm, hQr⟩, ?_⟩, hc⟩
  rw [ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map _ Q hQ']
  rw [hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega] at hQdim
  exact GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.dim_cancel_one hQdim

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxAbs

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (absLogNorm)

theorem absFibreSum_eq_sum_components_ae {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι} {A : HermLine ι}
    {s : MRing ι}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w| =
      ∑ᶠ Q ∈ (cxIdeal P).minimalPrimes, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w| := by
  classical
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hmeet := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentsMeetNull.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDimLt.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartRatioImageNull.proof K ι P e Ψ hfin.toFinset hP hΨ
    (fun W hW => hfin.mem_toFinset.1 hW)
  filter_upwards [compl_mem_ae_iff.mpr hmeet, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hone : ∀ Q ∈ (cxIdeal P).minimalPrimes, ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q →
      z ∈ conePts Q' → Ψ (segre z) = Fin.cons 1 y → Q' = Q := by
    intro Q hQ Q' hQ' z hz hz' hΨz
    by_contra hne
    refine hyN ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hΨz, Q, hfin.mem_toFinset.2 hQ, Q',
      hfin.mem_toFinset.2 hQ', fun h => hne h.symm, ?_, ?_⟩
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz.2 f hf
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz'.2 f hf
  have hunion : fibre P Ψ y = ⋃ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y := by
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz, hzw, hΨw⟩
      obtain ⟨Q, hQ, hzQ⟩ := exists_minimal_of_mem_mcPts hz
      exact ⟨Q, hQ, z, hzQ, hzw, hΨw⟩
    · rintro ⟨Q, hQ, z, hz, hzw, hΨw⟩
      exact ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hzw, hΨw⟩
  have hsub : ∀ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y ⊆ fibre P Ψ y := by
    intro Q hQ w hw
    rw [hunion]
    exact Set.mem_biUnion hQ hw
  have hdisj : ((cxIdeal P).minimalPrimes).PairwiseDisjoint fun Q => setFibre (conePts Q) Ψ y := by
    intro Q hQ Q' hQ' hne
    refine Set.disjoint_left.2 ?_
    rintro w ⟨z, hz, hzw, hΨw⟩ ⟨z', hz', hzw', -⟩
    have hzQ' : z ∈ conePts Q' := mem_conePts_of_segre_eq hP hQ' hz' hz.1 (hzw'.trans hzw.symm)
    exact hne (hone Q hQ Q' hQ' z hz hzQ' (by rw [hzw]; exact hΨw)).symm
  rw [hunion, finsum_mem_biUnion hdisj hfin
    (fun Q hQ => (fibreFinite K ι P e Ψ hP hΨ y).subset (hsub Q hQ))]
  refine finsum_mem_congr rfl fun Q hQ => finsum_mem_congr rfl fun w hw => ?_
  refine congrArg abs ?_
  have hiff : (∃ γ, IsSheet P Ψ y w γ) ↔ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ :=
    ⟨fun ⟨γ, h⟩ => ⟨γ, isSetSheet_of_isSheet hP hQ (hone Q hQ) hw h⟩,
      fun ⟨γ, h⟩ => ⟨γ, isSheet_of_isSetSheet hQ h⟩⟩
  rw [sheetDensity_eq_setSheetDensity]
  unfold setSheetDensity
  by_cases hex : ∃ γ, IsSheet P Ψ y w γ
  · have hexQ := hiff.1 hex
    have hexP : ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dite_eq_left hexP, dite_eq_left hexQ]
    exact hind w _ _ hexP.choose_spec (isSheet_of_isSetSheet hQ hexQ.choose_spec)
  · have hexQ : ¬ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ := fun h => hex (hiff.2 h)
    have hexP : ¬ ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dite_eq_right hexP, dite_eq_right hexQ]

theorem abs_setSheetDensity_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} (hS : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (A : HermLine ι) (s : MRingOver ℂ ι) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    |setSheetDensity S Ψ φ (logNormC A s) y w| =
      max (setSheetDensity S Ψ φ (absLogNorm A s) y w) 0 +
        max (setSheetDensity S Ψ φ (fun z => -absLogNorm A s z) y w) 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · have hz := hS _ hγ.choose_spec.2.self_of_nhds.2.1
    have ha : absLogNorm A s (hγ.choose y) = |logNormC A s (hγ.choose y)| := by
      simp only [absLogNorm, if_pos hz]
    beta_reduce
    rw [ha, abs_mul]
    generalize maDensity (fun j y' => φ j (hγ.choose y')) y = m
    generalize logNormC A s (hγ.choose y) = g
    have hg := abs_nonneg g
    rcases le_total 0 m with hm | hm
    · rw [abs_of_nonneg hm, max_eq_left (mul_nonneg hg hm),
        max_eq_right (by nlinarith : -|g| * m ≤ 0), add_zero]
    · rw [abs_of_nonpos hm, max_eq_right (by nlinarith : |g| * m ≤ 0),
        max_eq_left (by nlinarith : 0 ≤ -|g| * m), zero_add]
      ring
  · simp

theorem integrable_absFibreSum_of_isCxVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) (hsQ : s ∉ Q) :
    Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) := by
  classical
  have hS : ∀ z ∈ conePts Q, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun z hz => hz.1
  have hfin := GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ hQ hΨ
  have hm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.measurable_absLogNorm A hA s
  have hdeg := fun (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) =>
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.absLogNorm_blockScale A hAa hs hc z
  have h1 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm hdeg
  have h2 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm.neg
    (g := fun z => -absLogNorm A s z) (fun c z hc => by simp only [hdeg c z hc])
  have heq : (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) =
      fun y => cxPosDens (conePts Q) Ψ (pot L) (absLogNorm A s) y +
        cxPosDens (conePts Q) Ψ (pot L) (fun z => -absLogNorm A s z) y := by
    funext y
    unfold cxPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => abs_setSheetDensity_eq hS Ψ (pot L) A s y w
  refine ⟨?_, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => abs_nonneg _)).2
    (GlobalTheory.T.lintegral_fibre_logNorm_finite K ι Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ)⟩
  rw [heq]
  exact (h1.add h2).aestronglyMeasurable

theorem ptsAbsIntegrable : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hae := absFibreSum_eq_sum_components_ae hP hΨ hL hA hs
  obtain ⟨a, hAa, hsa, hsP⟩ := hs
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hsa' : IsMultiHomog (map (Int.castRingHom ℂ) s : MRingOver ℂ ι) a := fun m hm k =>
    hsa m (support_map_subset _ _ hm) k
  have hcomp : ∀ Q ∈ (cxIdeal P).minimalPrimes, Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w|) := by
    intro Q hQ
    obtain ⟨hQv, hc⟩ := isCxVar_of_mem_minimalPrimes_cxIdeal K ι P e hP Q hQ
    refine integrable_absFibreSum_of_isCxVar hQv
      (fun z hz => hΨ z (conePts_subset_mcPts_of_minimal hQ hz)) hL hA hAa hsa' fun hmem => hsP ?_
    rw [← hc]
    exact hmem
  refine (integrable_finsetSum hfin.toFinset fun Q hQ => hcomp Q (hfin.mem_toFinset.1 hQ)).congr ?_
  filter_upwards [hae] with y hy
  rw [hy]
  exact (finsum_mem_eq_finite_toFinset_sum _ hfin).symm

end GlobalTheory.CompanionTheory.Ar.Pub.CxAbs
end
end

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.Development
namespace PositivityTheory.Tls2.Pl

open GroundTheory.Heights₂.Heights

theorem stokesOnVariety : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement := by
  have hDeep : TubeDeepMass.Statement :=
    TubeDeepMass.proof TubeDeepRankOne.proof
      (TubeDeepAreaCount.proof AutoClose.IsolatedPointsCount)
      HilbertSamuel.Closed.TubeDeepWeightMass
  exact StokesOnVariety.of_open HilbertSamuel.Closed.SheetImageAreaSet
    (TubeEuclMass.proof HilbertSamuel.Closed.TubeCollarMass hDeep)

theorem lelongLimit (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) :
    GroundTheory.Heights₂.Heights.LelongLimit.Statement := by
  have hGood : LelongLimitGoodPoints.Statement := LelongLimitGoodPoints.proof hBr hLim hOrd
  have hMass : LelongMassNearSmall.Statement :=
    LelongMassNearSmall.proof hReg AutoClose.VarMassNearSmall
  exact LelongLimit.proof AutoClose.LelongLimitOffZero
    (LelongLimitOnZero.proof AutoClose.LelongLimitOffZero hGood hMass AutoClose.VarIntAdd)
    AutoClose.VarIntAdd

theorem lelongPolyLimit (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement) :
    GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.Statement :=
  GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.of_mult_weight GroundTheory.Heights₂.Heights.Targets.LocalMultComap.proof
    (GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit.proof hL stokesOnVariety
      GroundTheory.Heights₂.Heights.AutoClose.Targets_LelongWeightDiff)

theorem ptsAbsMeasurable (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement) :
    GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement :=
  fun K _ ι _ P e Ψ L A s h1 h2 h3 h4 h5 => (hAbs K ι P e Ψ L A s h1 h2 h3 h4 h5).aestronglyMeasurable

theorem poincareLelong_of (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hLPL : GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.Statement) : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong := by
  have hPI : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement :=
    PtsIntegrable.of_found hAbs HilbertSamuel.Closed.PtsSumMeasurable
  have hStk : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement :=
    StokesStatement.of_found (PtsBilinear.proof hAbs HilbertSamuel.Closed.PtsSumMeasurable)
      HilbertSamuel.Closed.SegrePartition
      (SegreChart.proof HilbertSamuel.Closed.SegreChartDim hSCI) stokesOnVariety
  have hChart : Targets.LelongChartLimit.Statement :=
    Targets.LelongChartLimit.proof hSCI HilbertSamuel.Closed.SegreChartDim
      Targets.ChartSectionNotMem.proof hLPL hCDC
  exact Targets.PoincareLelongAlt.of_found hStk (Targets.PoincareLelongRegularised.proof hPI (ptsAbsMeasurable hAbs))
    (Targets.PoincareLelongLimit.proof hPI (Targets.LelongSectionLimit.proof hPI hChart))

theorem poincareLelong_of_leaves (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of hAbs hSCI hCDC (lelongPolyLimit (lelongLimit hBr hLim hOrd hReg))

theorem poincareLelongInv_of_leaves (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv := by
  intro K _ ι _ P n L A B s hP hL hA hB _ _ _ hB0 hs
  have h : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula :=
    poincareLelong_of_leaves hAbs hSCI hCDC hBr hLim hOrd hReg
  exact h K ι P n L A B s hP hL hA hB hB0 hs

end PositivityTheory.Tls2.Pl
end

namespace PositivityTheory.Tls2.Pl

theorem poincareLelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

theorem poincareLelongInv : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv :=
  poincareLelongInv_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

end PositivityTheory.Tls2.Pl
