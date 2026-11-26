module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
public import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hasDerivAt_exp_entries (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (Matrix.of.symm X) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun M => Matrix.of.symm M
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
    {F : (Fin n → Fin n → ℂ) → H} (hF : ContDiff ℝ ∞ F) (hFG : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) (Matrix.of.symm X)) 0 := by
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
      fun t : ℝ => F (Matrix.of.symm (NormedSpace.exp (t • X))) := by
    funext t
    have hmem : Matrix.of (Matrix.of.symm (NormedSpace.exp (t • X))) ∈ G := by
      rw [Matrix.of.apply_symm_apply]
      exact hX t
    simpa only [Matrix.of.apply_symm_apply] using hFG _ hmem
  rw [hfun]
  have hdiff : DifferentiableAt ℝ F (Matrix.of.symm (NormedSpace.exp ((0 : ℝ) • X))) :=
    (hF.differentiable (by simp)) _
  have h := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_entries X)
  rw [zero_smul, NormedSpace.exp_zero] at h
  exact h

theorem differentiableAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
  obtain ⟨F, hF, hFG⟩ := hv
  exact (hasDerivAt_orbit hF hFG hX).differentiableAt

theorem dRep_linear : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G),
    dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧
      ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v := by
  intro n G H _ _ π hG _hrep u v hu hv X Y hX hY
  have hXY : X + Y ∈ HCSS.lieOf G := (lieOf_isLieSubalgebra hG).1 X Y hX hY
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨F, hF, hFG⟩ := hv
    simp only [dRep]
    rw [(hasDerivAt_orbit hF hFG hXY).deriv, (hasDerivAt_orbit hF hFG hX).deriv,
      (hasDerivAt_orbit hF hFG hY).deriv]
    exact (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ))).map_add
      (Matrix.of.symm X) (Matrix.of.symm Y)
  · simp only [dRep, map_add (f := _)]
    exact deriv_add (differentiableAt_orbit hu hX) (differentiableAt_orbit hv hX)
  · intro c
    simp only [dRep, map_smul]
    exact deriv_const_smul c (differentiableAt_orbit hv hX)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_additive : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧ ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
section -- merged from Development.WeilBound.CoreStatements.MeasureExistence.ExistsMeas
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.MatrixIdentityOffBase

variable {D : D7}

theorem exists_meas (V : HSp D) : ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓕, inferInstance, h⟩

end PositivityTheory.MatrixIdentityOffBase

namespace GlobalTheory.ConstRatio

export PositivityTheory.MatrixIdentityOffBase (exists_meas)

end GlobalTheory.ConstRatio

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicOpenNeighbourhoodProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CuspNbhd

open GlobalTheory.AdelicU

theorem real_mul_level_mem_nhds : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ N ∈ 𝓝 (1 : GA D V), {g : GA D V | ∃ r k : GA D V, r ∈ GinfC V ∧ r ∈ N ∧ k ∈ U ∧ k ∈ GfC V ∧ g = r * k} ∈ 𝓝 (1 : GA D V) := by
  intro D V U hU N hN
  have hr : Continuous fun g : GA D V =>
      ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) :=
    (continuous_ofInf _ _).comp (continuous_projInf _ _)
  have hk : Continuous fun g : GA D V =>
      ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) :=
    (continuous_ofFin _ _).comp (continuous_projFin _ _)
  have h1 : ∀ᶠ g : GA D V in 𝓝 1, ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) ∈ N := by
    have := hr.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this hN
  have h2 : ∀ᶠ g : GA D V in 𝓝 1, ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) ∈ U := by
    have := hk.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this (hU.mem_nhds U.one_mem)
  filter_upwards [h1, h2] with g hg1 hg2
  exact ⟨_, _, mem_infPts.2 (by simp), hg1, hg2, mem_finPts.2 (by simp),
    (ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g).symm⟩

end GlobalTheory.CompanionTheory.CuspNbhd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfCompactCoercive
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfCompactCoercive
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Glob

theorem finiteDimensional_of_compact_coercive :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c →
        (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  intro H _ _ _ A hA S c hc hS
  have hS' : ∀ u ∈ S.topologicalClosure, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re := by
    intro u hu
    have hcl : IsClosed {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} :=
      isClosed_le (continuous_const.mul (continuous_norm.pow 2))
        (Complex.continuous_re.comp (continuous_id.inner A.continuous))
    have hsub : (S : Set H) ⊆ {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} := fun u hu ↦ hS u hu
    have h := closure_minimal hsub hcl
    rw [← Submodule.topologicalClosure_coe] at h
    exact h hu
  have hbd : ∀ u ∈ S.topologicalClosure, ‖u‖ ≤ c⁻¹ * ‖A u‖ := by
    intro u hu
    have h1 := hS' u hu
    have h2 : (⟪u, A u⟫_ℂ).re ≤ ‖u‖ * ‖A u‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h3 : c * ‖u‖ ≤ ‖A u‖ := by
      rcases (norm_nonneg u).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]
        exact norm_nonneg _
      · nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  let T : S.topologicalClosure →L[ℂ] H := A.comp S.topologicalClosure.subtypeL
  have hT : IsCompactOperator T := hA.comp_clm S.topologicalClosure.subtypeL
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T := by
    refine ContinuousLinearMap.antilipschitz_of_bound T fun x ↦ ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    exact hbd x x.2
  have hemb : Topology.IsClosedEmbedding T := hanti.isClosedEmbedding T.uniformContinuous
  have hK := IsCompactOperator.isCompact_closure_image_closedBall
    (f := (T : S.topologicalClosure →ₗ[ℂ] H)) hT 1
  have hball : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    exact subset_closure ⟨x, hx, rfl⟩
  have : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hball
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure

end GlobalTheory.CompanionTheory.Glob
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfCompactCoerciveStatement
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c → (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | exact GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | (intros; apply GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspFin

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil

theorem le_re_inner_of_isRepOp {G H : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : G →* (H →L[ℂ] H)} {μ : Measure G} {φ : G → ℝ} {T : H →L[ℂ] H}
    (hT : IsRepOp π μ (fun g => (φ g : ℂ)) T) (hφ : Integrable φ μ) (h0 : 0 ≤ φ) {N : Set G}
    (hs : Function.support φ ⊆ N) (u : H) (c : ℝ) (hc : ∀ g ∈ N, c ≤ (⟪u, π g u⟫_ℂ).re) :
    c * ∫ g, φ g ∂μ ≤ (⟪u, T u⟫_ℂ).re := by
  have hi := (hT u).1
  have hin : Integrable (fun g => ⟪u, (φ g : ℂ) • π g u⟫_ℂ) μ := hi.const_inner u
  have e : (⟪u, T u⟫_ℂ).re = ∫ g, (⟪u, (φ g : ℂ) • π g u⟫_ℂ).re ∂μ := by
    rw [(hT u).2, ← integral_inner hi u]
    exact (integral_re hin).symm
  rw [e, ← integral_const_mul]
  refine integral_mono (hφ.const_mul c) hin.re fun g => ?_
  simp only [inner_smul_right, Complex.re_ofReal_mul]
  by_cases hg : φ g = 0
  · simp [hg]
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hc g (hs hg)) (h0 g)

variable {D : D7} {V : HSp D}

theorem exists_bump (μ : Measure (GA D V)) [μ.IsHaarMeasure] {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V)) :
    ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ Function.support φ ⊆ N ∧ Integrable φ μ ∧
      0 < ∫ g, φ g ∂μ := by
  obtain ⟨φ, hφ, h0, h1, hs⟩ : ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ φ 1 = 1 ∧
      Function.support φ ⊆ N := GlobalTheory.CuspSpectrum.exists_bump_ccAd (isCMExt_host D) hN
  have hc := continuous_of_mem_ccAd hφ
  have hφc : Continuous φ := Complex.continuous_re.comp hc.1
  have hφs : HasCompactSupport φ := hc.2.comp_left (g := Complex.re) rfl
  exact ⟨φ, hφ, h0, hs, hφc.integrable_of_hasCompactSupport hφs,
    hφc.integral_pos_of_hasCompactSupport_nonneg_nonzero hφs h0 (x := 1) (by rw [h1]; exact one_ne_zero)⟩

theorem finiteDimensional_of_coercive (hP : GlobalTheory.Published.CuspDecayBound) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Sb : Submodule ℂ (L2cusp V μ)) {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V))
    (h : ∀ g ∈ N, ∀ u ∈ Sb, (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤ (⟪u, Rcusp V μ g u⟫_ℂ).re) : FiniteDimensional ℂ Sb := by
  obtain ⟨φ, hf, h0, hs, hi, hpos⟩ := exists_bump μ hN
  have hrep := GlobalTheory.CuspSpectrum.isRepOp_RcuspOp (μ := μ) hf
  refine GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive (L2cusp V μ) (RcuspOp V μ _)
    (isCompactOperator_of_isHilbertSchmidt (GlobalTheory.CuspHS.isHilbertSchmidt_RcuspOp hP hf)) Sb
    ((1 / 2) * ∫ g, φ g ∂μ) (by positivity) fun u hu => ?_
  have := le_re_inner_of_isRepOp hrep hi h0 hs u ((1 / 2 : ℝ) * ‖u‖ ^ 2) fun g hg => h g hg u hu
  calc _ = (1 / 2 : ℝ) * ‖u‖ ^ 2 * ∫ g, φ g ∂μ := by ring
    _ ≤ _ := this

end GlobalTheory.CompanionTheory.CuspFin
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp

open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}


variable (θ V) in
abbrev Mc : Submodule ℂ (GA D V → ℂ) := GlobalTheory.Cusp.cuspForms θ V ⊥

theorem mem_Mc_iff {φ : GA D V → ℂ} : φ ∈ Mc θ V ↔ IsAutFunSm θ V φ ∧ IsCuspFun V φ := by
  refine ⟨fun h => (mem_cuspForms.1 h).1, fun h => mem_cuspForms.2 ⟨h, ?_⟩⟩
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨Submodule.span ℂ {φ}, inferInstance, fun k hk => ?_⟩
  rw [Subgroup.mem_bot.1 hk]
  exact Submodule.subset_span (by simp)

def der (hθ : IsInfFam θ) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Module.End ℂ (Mc θ V) where
  toFun φ := ⟨Rder θ V τ X φ.1, mem_Mc_iff.2
    ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX (mem_Mc_iff.1 φ.2).1,
      GlobalTheory.CuspLie.isCuspFun_Rder hθ hX (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩⟩
  map_add' f g := Subtype.ext (Rder_add (mem_Mc_iff.1 f.2).1.smooth (mem_Mc_iff.1 g.2).1.smooth hX)
  map_smul' c f := Subtype.ext (Rder_smul c f.1 τ X)

def io (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) : Mc θ V →ₗ[ℂ] L2cusp V μ :=
  GlobalTheory.Cusp.cuspToL2 ⊥ μ
    (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ

theorem io_injective (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) :
    Function.Injective (io (V := V) μ hθ) := cusp_form_toL2_injective _ hθ

def derInf (hθ : IsInfFam θ) (X : GlobalTheory.SmoothForms.LieN V) : Module.End ℂ (Mc θ V) :=
  ∑ τ, der hθ τ (X := (X τ).1) (X τ).2

def IsKLie {n : ℕ} (e : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  yᴴ = -y ∧ y * Formalism.REAL.Jm e = Formalism.REAL.Jm e * y

end GlobalTheory.CompanionTheory.HCCusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeries
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeries
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasDerivAt_one_sub_pow_succ_div_factorial (N : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ))
      (-((1 - s) ^ N / (N.factorial : ℝ))) s := by
  have h0 : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1)) (((N + 1 : ℕ) : ℝ) * (1 - s) ^ (N + 1 - 1) * (-1)) s :=
    h0.pow (N + 1)
  refine (h1.div_const ((N + 1).factorial : ℝ)).congr_deriv ?_
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem hasDerivAt_sum_one_sub_pow_div_factorial_smul {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s)
    (N : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t)
      (((1 - s) ^ N / (N.factorial : ℝ)) • f (N + 1) s) s := by
  induction N with
  | zero => simpa using hf 0 s
  | succ N ih =>
    have h2 := ih.add ((hasDerivAt_one_sub_pow_succ_div_factorial N s).smul (hf (N + 1) s))
    convert (preTransparency := .reducible) h2 using 1
    · funext t
      exact Finset.sum_range_succ _ _
    · rw [neg_smul]
      abel

theorem norm_chain_sub_partial_le {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s) (N : ℕ) {A : ℝ}
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f (N + 1) s‖ ≤ A) :
    ‖f 0 1 - ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0‖ ≤ A / ((N + 1).factorial : ℝ) := by
  let F : ℝ → E := fun t => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t
  have hF1 : F 1 = f 0 1 := by
    simp [F, Finset.sum_range_succ']
  have hF0 : F 0 = ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0 := by
    simp [F]
  have hD : ∀ t, HasDerivAt F (((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t) t :=
    fun t => hasDerivAt_sum_one_sub_pow_div_factorial_smul hf N t
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun t => F t - F 0) (a := 0) (b := 1)
    (f' := fun t => ((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t)
    (B := fun t => A / ((N + 1).factorial : ℝ) - A * ((1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ)))
    (B' := fun t => A * ((1 - t) ^ N / (N.factorial : ℝ)))
    (fun t _ => ((hD t).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun t _ => ((hD t).sub_const (F 0)).hasDerivWithinAt)
    (by simp [div_eq_mul_inv])
    (fun t => (((hasDerivAt_one_sub_pow_succ_div_factorial N t).const_mul A).const_sub
      (A / ((N + 1).factorial : ℝ))).congr_deriv (by ring))
    (fun t ht => by
      have hc : 0 ≤ (1 - t) ^ N / (N.factorial : ℝ) := by
        have : 0 ≤ 1 - t := by linarith [ht.2]
        positivity
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_comm A]
      exact mul_le_mul_of_nonneg_left (hA t ⟨ht.1, ht.2.le⟩) hc)
  have h1 := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simp only [hF1, hF0, sub_self, zero_pow (Nat.succ_ne_zero N), zero_div, mul_zero, sub_zero] at h1
  exact h1

theorem hasSum_chain {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s) {a : ℕ → ℝ}
    (ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m)
    (hs : Summable fun m : ℕ => a m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => ((m.factorial : ℝ)⁻¹) • f m 0) (f 0 1) := by
  have hn : Summable fun m : ℕ => ‖((m.factorial : ℝ)⁻¹) • f m 0‖ := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (ha m 0 ⟨le_rfl, zero_le_one⟩) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hn, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hs.tendsto_atTop_zero
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn1 => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [norm_sub_rev]
  exact norm_chain_sub_partial_le hf N (ha (N + 1))

end Chain

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_exp_smul_real {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end Exp

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}

theorem exp_add_smul_real (X : Matrix (Fin n) (Fin n) ℂ) (s h : ℝ) :
    NormedSpace.exp ((s + h) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (h • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right h)

theorem isSmoothVec_iterate_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H}
    (hs : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => exact hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih hX).2

theorem hasDerivAt_orbit_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H}
    (hu : IsSmoothVec G π u) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (π (NormedSpace.exp (s • X)) (dRep π X u)) s := by
  have hd := (hasDerivAt_dRep_and_isSmoothVec hG hrep hu hX).1
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G := hX
  have heq : (fun t : ℝ => π (NormedSpace.exp (t • X)) u) =
      fun t => π (NormedSpace.exp (s • X)) (π (NormedSpace.exp ((t - s) • X)) u) := by
    funext t
    have h1 : NormedSpace.exp (t • X) = NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X) := by
      rw [← exp_add_smul_real, add_sub_cancel]
    rw [h1, hrep.2 _ (hmem s) _ (hmem (t - s))]
    rfl
  rw [heq]
  have hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (dRep π X u) (s - s) := by
    rw [sub_self]
    exact hd
  have hc := hd'.comp_sub_const s s
  exact ((π (NormedSpace.exp (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hc

theorem exists_bound_orbit_Icc [CompleteSpace H] (hc : ∀ v, ContinuousOn (fun g => π g v) G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp (s • X))‖ ≤ B := by
  have hcont : ∀ w, ContinuousOn (fun s : ℝ => π (NormedSpace.exp (s • X)) w) (Set.Icc 0 1) := by
    intro w
    exact (hc w).comp (continuous_exp_smul_real X).continuousOn (fun s _ => hX s)
  have hb : ∀ w, ∃ C, ∀ i : Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp ((i : ℝ) • X)) w‖ ≤ C := by
    intro w
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont w)
    exact ⟨C, fun i => hC i i.2⟩
  obtain ⟨B, hB⟩ := banach_steinhaus (g := fun i : Set.Icc (0 : ℝ) 1 => π (NormedSpace.exp ((i : ℝ) • X))) hb
  exact ⟨B, fun s hs => hB ⟨s, hs⟩⟩

theorem norm_iterate_dRep_le {C : ℝ}
    (hb : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ HCSS.lieOf G) →
      ‖l.foldr (dRep π) v‖ ≤ C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    ‖(dRep π X)^[m] v‖ ≤ C ^ (m + 1) * m.factorial * mnorm X ^ m := by
  have hfold : ∀ k, List.foldr (dRep π) v (List.replicate k X) = (dRep π X)^[k] v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']
  have h := hb (List.replicate m X) (fun Y hY => by rw [List.eq_of_mem_replicate hY]; exact hX)
  rw [hfold, List.length_replicate, List.map_replicate, List.prod_replicate] at h
  exact h

theorem mnorm_nonneg' (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X := by
  unfold mnorm
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _

theorem hasSum_orbit_of_wordBound : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) {v : H} (hs : IsSmoothVec G π v)
    (hw : WordBound G π v), ∃ r : ℝ, 0 < r ∧ ∀ X ∈ HCSS.lieOf G, mnorm X < r →
      HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (dRep π X)^[m] v) (π (NormedSpace.exp X) v) := by
  intro n G H _ _ _ π hG hrep hc v hs hw
  obtain ⟨C, hC0, hC⟩ := hw
  refine ⟨C⁻¹, inv_pos.mpr hC0, fun X hX hXr => ?_⟩
  obtain ⟨B, hB⟩ := exists_bound_orbit_Icc hc hX
  let f : ℕ → ℝ → H := fun m s => π (NormedSpace.exp (s • X)) ((dRep π X)^[m] v)
  have hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s := by
    intro m s
    have := hasDerivAt_orbit_smooth hG hrep (isSmoothVec_iterate_dRep hG hrep hs hX m) hX s
    simpa only [f, Function.iterate_succ_apply'] using this
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hmX := mnorm_nonneg' X
  let a : ℕ → ℝ := fun m => B * (C ^ (m + 1) * m.factorial * mnorm X ^ m)
  have ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m := by
    intro m s hs'
    calc ‖f m s‖ ≤ ‖π (NormedSpace.exp (s • X))‖ * ‖(dRep π X)^[m] v‖ := (π _).le_opNorm _
      _ ≤ B * (C ^ (m + 1) * m.factorial * mnorm X ^ m) :=
        mul_le_mul (hB s hs') (norm_iterate_dRep_le hC hX m) (norm_nonneg _) hB0
  have hsum : Summable fun m : ℕ => a m / (m.factorial : ℝ) := by
    have heq : (fun m : ℕ => a m / (m.factorial : ℝ)) = fun m => (B * C) * (C * mnorm X) ^ m := by
      funext m
      have : (m.factorial : ℝ) ≠ 0 := by positivity
      simp only [a]
      field_simp
      ring
    rw [heq]
    refine Summable.mul_left _ (summable_geometric_of_lt_one (mul_nonneg hC0.le hmX) ?_)
    calc C * mnorm X < C * C⁻¹ := mul_lt_mul_of_pos_left hXr hC0
      _ = 1 := mul_inv_cancel₀ hC0.ne'
  have key := hasSum_chain hf ha hsum
  have h1 : f 0 1 = π (NormedSpace.exp X) v := by
    simp [f]
  have h2 : ∀ m, f m 0 = (dRep π X)^[m] v := by
    intro m
    simp [f, hrep.1]
  rw [h1] at key
  simp only [h2] at key
  convert key using 1
  funext m
  rw [show ((m.factorial : ℂ)⁻¹) = (((m.factorial : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.coe_smul]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeriesStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_vector_exponential_series : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v), ∃ r : ℝ, 0 < r ∧ ∀ X ∈ HCSS.lieOf G, mnorm X < r → HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (dRep π X)^[m] v) (π (NormedSpace.exp X) v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsBasisLieOfOrthogonal
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

variable {n : ℕ}

def vecOf : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun x := Matrix.of fun i j => x (i, j)
  map_add' X Y := by ext p; simp
  map_smul' r X := by ext p; simp
  left_inv X := by ext i j; simp
  right_inv x := by ext p; simp

theorem inner_vecOf (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf X, vecOf Y⟫_ℝ = (Xᴴ * Y).trace.re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [vecOf, Complex.inner]
  ring

theorem inner_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf (k * X * k⁻¹), vecOf (k * Y * k⁻¹)⟫_ℝ = ⟪vecOf X, vecOf Y⟫_ℝ := by
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hk
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv h2
  rw [inner_vecOf, inner_vecOf, hinv]
  have : (k * X * kᴴ)ᴴ * (k * Y * kᴴ) = k * (Xᴴ * Y) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc k * (Xᴴ * kᴴ) * (k * Y * kᴴ) = k * Xᴴ * (kᴴ * k) * Y * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = k * (Xᴴ * Y) * kᴴ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem exists_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : Submodule ℝ E)
    [FiniteDimensional ℝ W] :
    ∃ (d : ℕ) (e : Fin d → E), (∀ i, e i ∈ W) ∧ Orthonormal ℝ e ∧ ∀ x ∈ W, x = ∑ i, ⟪e i, x⟫_ℝ • e i := by
  let B := stdOrthonormalBasis ℝ W
  refine ⟨_, fun i => (B i : E), fun i => (B i).2, ?_, ?_⟩
  · exact B.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · intro x hx
    have := congrArg (Subtype.val) (B.sum_repr' ⟨x, hx⟩)
    simpa [Submodule.coe_sum] using this.symm

theorem orthogonal_of_preserves {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} {e : Fin d → E}
    (he : Orthonormal ℝ e) (f : Fin d → E) (hexp : ∀ i, f i = ∑ l, ⟪e l, f i⟫_ℝ • e l)
    (hf : ∀ i j, ⟪f i, f j⟫_ℝ = ⟪e i, e j⟫_ℝ) :
    (Matrix.of fun l i => ⟪e l, f i⟫_ℝ : Matrix (Fin d) (Fin d) ℝ)ᵀ * Matrix.of (fun l i => ⟪e l, f i⟫_ℝ) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h : ⟪f i, f j⟫_ℝ = ∑ l, ⟪e l, f i⟫_ℝ * ⟪e l, f j⟫_ℝ := by
    conv_lhs => rw [hexp j]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_right, mul_comm, real_inner_comm (e l) (f i)]
  rw [← h, hf, orthonormal_iff_ite.1 he, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis


open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in
theorem GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (_hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l := by
  open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in
    intro n G hG
    obtain ⟨hadd, hsmul, -, hAd⟩ := lieOf_isLieSubalgebra hG
    let L : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      { carrier := HCSS.lieOf G
        add_mem' := fun {X Y} hX hY => hadd X Y hX hY
        zero_mem' := fun t => by simpa using hG.one_mem
        smul_mem' := fun r X hX => hsmul r X hX }
    let W : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) := L.map (vecOf (n := n)).toLinearMap
    have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
      FiniteDimensional.complexToReal _
    obtain ⟨d, e, heW, hon, hexp⟩ := exists_orthonormal W
    have hmemW : ∀ X ∈ HCSS.lieOf G, vecOf X ∈ W := fun X hX => ⟨X, hX, rfl⟩
    have hbL : ∀ i, vecOf.symm (e i) ∈ HCSS.lieOf G := by
      intro i
      obtain ⟨X, hX, hXe⟩ := heW i
      have : vecOf.symm (e i) = X := by
        rw [← hXe]; simp
      rw [this]; exact hX
    have hexpM : ∀ X ∈ HCSS.lieOf G, X = ∑ i, ⟪e i, vecOf X⟫_ℝ • vecOf.symm (e i) := by
      intro X hX
      have h := hexp _ (hmemW X hX)
      have h2 := congrArg (vecOf (n := n)).symm h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simpa using h2
    refine ⟨d, fun i => vecOf.symm (e i), hbL, ?_, ?_, ?_⟩
    · exact hon.linearIndependent.map' (vecOf (n := n)).symm.toLinearMap
        (LinearMap.ker_eq_bot.2 (vecOf (n := n)).symm.injective)
    · intro X hX
      exact ⟨_, hexpM X hX⟩
    · intro k hk
      have hkG : k ∈ G := hk.1
      have hkU : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hk.2
      let f : Fin d → EuclideanSpace ℂ (Fin n × Fin n) := fun i => vecOf (k * vecOf.symm (e i) * k⁻¹)
      have hfW : ∀ i, f i ∈ W := fun i => hmemW _ (hAd k hkG _ (hbL i))
      have hO := orthogonal_of_preserves hon f (fun i => hexp _ (hfW i)) (fun i j => by
        have := inner_conj hkU (vecOf.symm (e i)) (vecOf.symm (e j))
        simpa [f] using this)
      refine ⟨_, hO, fun i => ?_⟩
      have h := hexp _ (hfW i)
      have h2 := congrArg (vecOf (n := n)).symm h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simpa [f] using h2

end
end
