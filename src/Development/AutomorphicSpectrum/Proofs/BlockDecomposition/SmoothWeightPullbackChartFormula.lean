module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZeroStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormula
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.PullDens


open Filter Topology in
theorem locDens_pullback_eq : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (c : GlobalTheory.AlgChart q σ D) (j : Fin A.n) (u : Fin D → ℂ),
      u ∈ (A.chart j).target → F ((A.chart j).symm u) ∈ c.e.source →
      AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u ∧
      locDens A (fun _ => φ.locPot.pullback F hF) j u =
        ‖LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (F ((A.chart j).symm u)) := by
  intro k _ X q σ D T _ A F hF hH B φ h c j u hu hsrc
  have hcont : ContinuousAt (F ∘ (A.chart j).symm) u :=
    hF.continuousAt.comp ((A.chart j).continuousAt_symm hu)
  have hN : ∀ᶠ w in 𝓝 u, F ((A.chart j).symm w) ∈ c.e.source :=
    hcont.eventually (c.e.open_source.mem_nhds hsrc)
  have hG : AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u := by
    refine analyticAt_pi_iff.2 fun a => ?_
    refine (hH c.U (c.x a) j u ⟨hu, c.source_subset hsrc⟩).congr ?_
    filter_upwards [hN] with w hw
    exact (c.finChart_eq_ev hw a).symm
  refine ⟨hG, ?_⟩
  set G := c.finChart ∘ F ∘ (A.chart j).symm with hGdef
  set y₀ := F ((A.chart j).symm u) with hy₀
  have hGu : G u = c.finChart y₀ := rfl
  have hsy : c.finChart.symm (G u) = y₀ := c.finChart.left_inv hsrc
  have hz : G u ∈ c.finChart.target := c.finChart.map_source hsrc
  have hma := h.maDens_eq c hz
  rw [hsy] at hma
  have hr : c.e y₀ = GlobalTheory.FinChart.toV D (G u) := rfl
  have hd := h.contDiffAt c hsrc (mem_pick φ.isLB y₀)
  rw [hr] at hd
  have hψ : ContDiffAt ℝ 2 (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) (G u) :=
    (hd.comp (G u) (GlobalTheory.FinChart.toV D).contDiff.contDiffAt).div_const 2
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ w => φ.locPot.φ y₀ (c.finChart.symm w)) G u hG
    (fun _ => hψ)
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hma] at hcomp
  rw [mul_comm, ← hcomp]
  unfold locDens
  refine maDens_congr_hessC _ _ _ fun _ => hessCGerm _ _ _ ?_
  filter_upwards [hN] with w hw
  simp only [LocPot.pullback, Function.comp_apply, hGdef]
  rw [c.finChart.left_inv hw]

end GlobalTheory.CompanionTheory.MixZ.PullDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormulaStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_weight_pullback_chart_formula : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (c : GlobalTheory.AlgChart q σ D) (j : Fin A.n) (u : Fin D → ℂ),
      u ∈ (A.chart j).target → F ((A.chart j).symm u) ∈ c.e.source →
      AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u ∧
      locDens A (fun _ => φ.locPot.pullback F hF) j u =
        ‖LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (F ((A.chart j).symm u)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq | exact GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq | (intros; apply GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairing
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreePartner

theorem isReduced_tens (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [IsReduced R] : IsReduced (R ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  haveI : Algebra.FormallySmooth F E := inferInstance
  haveI : Algebra.FinitePresentation F E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Smooth F E := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.Smooth R (R ⊗[F] E) := inferInstance
  exact GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R (R ⊗[F] E)

theorem isUnit_det_JR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (h : J.det ≠ 0) :
    IsUnit (JR (F := F) R J).det := by
  have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact (IsUnit.mk0 _ h).map _

theorem exists_partner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => x) → ∃ y : Fin M → R ⊗[F] E, hR R σ J x y = 1 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hloc x hx
  obtain ⟨-, -, -, -, hA, hRed, -, -⟩ := hloc
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  haveI : IsReduced (R ⊗[F] E) := isReduced_tens F E R
  have hinv : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z :=
    HermTop.sigR_sigR R (HermTop.sigma_sigma hσ)
  have hlip := FreeOpen.lip_of_artinian_reduced (R ⊗[F] E)
  obtain ⟨P, hP⟩ := hlip (Fin M) (Fin 1)
    (Matrix.of fun i (_ : Fin 1) => sigR R σ (x i)) (by
      intro c hc
      have h1 : ∀ i, sigR R σ (x i) * c 0 = 0 := by
        intro i
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct] using this
      have h2 : sigR R σ (c 0) • x = 0 := by
        funext i
        have := congrArg (sigR R σ) (h1 i)
        rw [map_mul, hinv, map_zero] at this
        simpa [mul_comm] using this
      have h3 := Fintype.linearIndependent_iff.mp hx (fun _ => sigR R σ (c 0)) (by simpa using h2) 0
      have h4 : c 0 = 0 := by
        have := congrArg (sigR R σ) h3
        simpa [hinv] using this
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h4)
  have hu := isUnit_det_JR (F := F) R hJ.2
  refine ⟨(JR R J)⁻¹ *ᵥ (fun j => P 0 j), ?_⟩
  have hv : JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) = fun j => P 0 j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h00 := congrFun (congrFun hP 0) 0
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq] at h00
  have hform' : hR R σ J x ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) =
      ∑ i, sigR R σ (x i) * (JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j))) i := by
    simp only [hR, hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hform', hv, ← h00]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompanionTheory.WeilSiegel.FreePartner
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_primitive_vector_pairing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => x) → ∃ y : Fin M → R ⊗[F] E, hR R σ J x y = 1 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreePartner.exists_partner | exact GlobalTheory.CompanionTheory.WeilSiegel.FreePartner.exists_partner | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreePartner.exists_partner <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackIsPotential
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackIsPotential
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

open Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MixZ

theorem isPotential_pullback_locPot : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → IsPotential A (φ.locPot.pullback F hF) := by
  intro k _ X q σ D T _ A F hF hol B φ hφ
  refine ⟨fun x j v hv => ?_, fun x x' y hy => ?_⟩
  · have hv1 : v ∈ (A.chart j).target := hv.1
    have hv2 : F ((A.chart j).symm v) ∈ ptsIn q σ (B.U (pick φ.isLB (F x))) := hv.2
    obtain ⟨W, ι, _, g, Fn, O, h₁, h₂, h₃, h₄, h₅⟩ := hφ _ _ hv2
    have hcs : ContinuousAt (fun w => F ((A.chart j).symm w)) v :=
      hF.continuousAt.comp ((A.chart j).continuousAt_symm hv1)
    have hop : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ W)) :=
      (A.chart j).isOpen_inter_preimage_symm ((isOpen_ptsIn W).preimage hF)
    have hg : ContDiffAt ℝ ∞ (fun w a => ev q σ W (g a) (F ((A.chart j).symm w))) v :=
      contDiffAt_pi.2 fun a =>
        ((hol W (g a) j v ⟨hv1, h₁⟩).restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top
    have hc : ContDiffAt ℝ ∞ (fun w => Fn fun a => ev q σ W (g a) (F ((A.chart j).symm w))) v :=
      (h₄.contDiffAt (h₂.mem_nhds h₃)).comp v hg
    have hc' : ContDiffAt ℝ ∞ (fun w => φ.φ (pick φ.isLB (F x)) (F ((A.chart j).symm w))) v :=
      hc.congr_of_eventuallyEq (hcs.eventually h₅)
    exact (hc'.div_const 2).contDiffWithinAt
  · set i := pick φ.isLB (F x) with hi
    set i' := pick φ.isLB (F x') with hi'
    have hyi : F y ∈ ptsIn q σ (B.U i) := hy.1
    have hyi' : F y ∈ ptsIn q σ (B.U i') := hy.2
    set S : Set T := F ⁻¹' ptsIn q σ (B.U i ⊓ B.U i') with hS
    have hSo : IsOpen S := (isOpen_ptsIn _).preimage hF
    have hyS : y ∈ S := mem_ptsIn_inf.2 ⟨hyi, hyi'⟩
    set g : T → ℂ := ev q σ (B.U i ⊓ B.U i') (B.g i i').val ∘ F with hg
    have hgh : A.HoloOn S g := hol _ _
    have hgc : ContinuousOn g S :=
      (continuousOn_ev (B.g i i').val).comp hF.continuousOn fun _ h => h
    have h0 : g y ≠ 0 := gv_ne_zero hyi hyi'
    refine ⟨S ∩ (fun z => g z * (g y)⁻¹) ⁻¹' Complex.slitPlane,
      (hgc.mul continuousOn_const).isOpen_inter_preimage hSo Complex.isOpen_slitPlane,
      ⟨hyS, ?_⟩, fun z => Complex.log (g z * (g y)⁻¹) + (Real.log ‖g y‖ : ℂ),
      fun j v hv => ?_, fun z hz => ?_⟩
    · simp [mul_inv_cancel₀ h0]
    · have ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v := hgh j v ⟨hv.1, hv.2.1⟩
      exact ((ha.mul analyticAt_const).clog hv.2.2).add analyticAt_const
    · have hzS : F z ∈ ptsIn q σ (B.U i ⊓ B.U i') := hz.1.1.1
      have hz0 : g z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.1.1.2)
      have e := φ.half_eq (mem_ptsIn_inf.1 hzS).1 (mem_ptsIn_inf.1 hzS).2
      have e' : Real.log ‖gv q σ B i i' (F z)‖ = Real.log ‖g z‖ := rfl
      change φ.φ i (F z) / 2 - φ.φ i' (F z) / 2 = _
      rw [e, e', Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
        Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel,
        add_sub_cancel_left]

end GlobalTheory.CompanionTheory.MixZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackIsPotentialStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_weight_pullback_is_potential : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → IsPotential A (φ.locPot.pullback F hF) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot | exact GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot | (intros; apply GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedRestrictPullBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictPullBijectiveOfForall
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmRes

theorem restrict_pull_bijective_of_forall :
    ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
      (Q : ObjectProperty C), (∀ T, Q T) →
      ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict F Q.ι).pull n) := by
  intro R _ C _ F Q h n
  haveI : Q.ι.EssSurj := ⟨fun Y => ⟨⟨Y, h Y⟩, ⟨Iso.refl _⟩⟩⟩
  haveI : Q.ι.IsEquivalence := { }
  exact CrystallineSemistableComparison.P.adj F Q.ι Q.ι.inv Q.ι.asEquivalence.toAdjunction n

end GlobalTheory.CompanionTheory.OmRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedRestrictPullBijective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmLoc

open Pb

theorem mor_mk_congr {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'} (G : C' ⥤ C)
    (τ τ' : (T : C') → F.obj (G.obj T) →ₛₗ[σ] F'.obj T) (n n') (h : τ = τ') :
    (⟨G, τ, n⟩ : CH.Mor F F' σ) = ⟨G, τ', n'⟩ := by
  subst h; rfl

theorem sq_incl_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    (incl h).sq (incl_fil h r) (incl_fil h r') =
      (CH.Mor.restrict (sq (sFil Q r) (sFil Q r')) (ObjectProperty.ιOfLE h) :) := by
  refine mor_mk_congr _ _ _ _ _ ?_
  funext T
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem chain {b : Base} {L : b.Fun} (r r' : ℤ) (Q1 Q2 Q3 : ObjectProperty (Thick L)) (h12 : Q2 ≤ Q1) (h23 : Q3 ≤ Q2) (n : ℕ)
    (b1 : Function.Bijective ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).pull n))
    (b2 : Function.Bijective (((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).pull n))
    (b3 : Function.Bijective (((incl h23).sq (incl_fil h23 r) (incl_fil h23 r')).pull n)) :
    Function.Bijective ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι).pull n) := by
  have e : CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι =
      (CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).comp
        (F' := sq (sFil Q1 r) (sFil Q1 r')) (σ' := RingHom.id _) (σ'' := RingHom.id _)
        (((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).comp (σ'' := RingHom.id _) ((incl h23).sq (incl_fil h23 r) (incl_fil h23 r'))) := by
    rw [sq_incl_eq, sq_incl_eq]
    rfl
  have f : ⇑((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι).pull n) =
      ⇑(((incl h23).sq (incl_fil h23 r) (incl_fil h23 r')).pull n) ∘
        ⇑(((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).pull n) ∘
          ⇑((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).pull n) := by
    funext x
    rw [e]
    exact (P.pull_comp _ _ n x).1.trans ((P.pull_comp _ _ n _).1)
  rw [f]
  exact b3.comp (b2.comp b1)

theorem grT_restrict_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ →
    ∀ (a s : ℕ), a < s → ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (Pb.KS q s 𝒱).ι).pull n) := by
  intro K _ X q 𝒱 h𝒱 a s has n
  have hI : ∀ T : Thick (nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)), InU ⊤ T := fun T => le_of_eq rfl
  have h12 : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {⊤} ≤ St ⊤ {⊤} :=
    fun T hT => ⟨trivial, hT.2⟩
  have h23 : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) 𝒱 ≤ St (TF 1 s) {⊤} :=
    fun T hT => ⟨hT.1, ⊤, rfl, hI T⟩
  exact chain (L := nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)) (a : ℤ) ((a : ℤ) + 1) _ _ _ h12 h23 n
    (GlobalTheory.CompanionTheory.OmRes.restrict_pull_bijective_of_forall _ _ (fun T => ⟨trivial, ⊤, rfl, hI T⟩) n)
    (Pb.refl ⊤ 1 s (Or.inl ⟨rfl, rfl⟩) {⊤} h12 (a : ℤ) ((a : ℤ) + 1) (by omega) n)
    ((Pb.zar (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) 𝒱 {⊤} h23 (by rintro W rfl; exact h𝒱.ge) n).1 (a : ℤ) ((a : ℤ) + 1))

end GlobalTheory.CompanionTheory.OmLoc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedRestrictPullBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_restrict_pull_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ →
    ∀ (a s : ℕ), a < s → ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (Pb.KS q s 𝒱).ι).pull n) := by
  first | exact @GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective | exact GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective | (intros; apply GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimClosure

private theorem exists_ringKrullDim_le_add_of_finiteType {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] (f : R →+* A) (hf : f.FiniteType) :
    ∃ N : ℕ, ringKrullDim A ≤ ringKrullDim R + N := by
  letI := f.toAlgebra
  obtain ⟨k, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
  refine ⟨k, ?_⟩
  calc ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin k) R) :=
        ringKrullDim_le_of_surjective g.toRingHom hg
    _ = ringKrullDim R + k := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem exists_open_nhd_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} (y : MP ℤ m n) :
    ∃ U : (MP ℤ m n).Opens, y ∈ U ∧ ∃ N : ℕ, topologicalKrullDim (U : Set (MP ℤ m n)) ≤ N := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  obtain ⟨U, hU, hyU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : (MP ℤ m n).Opens)) (x := y) (by simp)
  refine ⟨U, hyU, ?_⟩
  have hZ := AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of ℤ))
  have hft := AlgebraicGeometry.Scheme.Hom.finiteType_appLE (mpStr ℤ m n) hZ hU
    (by simp)
  haveI : IsNoetherianRing ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) :=
    isNoetherianRing_of_ringEquiv ℤ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv
  obtain ⟨N, hN⟩ := exists_ringKrullDim_le_add_of_finiteType _ hft
  have hZdim : ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv]
    have h1 := Ring.krullDimLE_iff.mp (IsPrincipalIdealRing.krullDimLE_one ℤ)
    exact_mod_cast h1
  haveI := hU.isOpenImmersion_fromSpec
  have htop : topologicalKrullDim (U : Set (MP ℤ m n)) =
      ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U)) := by
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  refine ⟨N + 1, ?_⟩
  rw [htop]
  calc ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U))
        ≤ ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) + N := hN
    _ ≤ 1 + N := by gcongr
    _ = ((N + 1 : ℕ) : WithBot ℕ∞) := by push_cast; exact add_comm _ _

private theorem exists_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} :
    ∃ d : ℕ, topologicalKrullDim (MP ℤ m n) ≤ d := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  haveI : CompactSpace (MP ℤ m n) :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace (mpStr ℤ m n)
  choose U hyU N hN using fun y : MP ℤ m n => exists_open_nhd_topologicalKrullDim_MP_le y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set (MP ℤ m n)))
    (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
  refine ⟨t.sup N, GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_⟩
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  refine ⟨U y, (U y).isOpen, hzy, (hN y).trans ?_⟩
  exact_mod_cast Finset.le_sup (f := N) hy

theorem exists_dim_closure_eq {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) :
    ∃ e : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (e : ℕ) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_MP_le (m := m) (n := n)
  have hle : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) ≤ d :=
    (topologicalKrullDim_subspace_le _ _).trans hd
  have hnn : 0 ≤ topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) := by
    haveI : Nonempty (IrreducibleCloseds (closure ({x} : Set (MP ℤ m n)))) :=
      ⟨⟨closure {(⟨x, subset_closure (Set.mem_singleton x)⟩ : closure ({x} : Set (MP ℤ m n)))},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    unfold topologicalKrullDim
    exact Order.krullDim_nonneg
  generalize topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = D at hle hnn ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h5 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top d (top_le_iff.mp (WithBot.coe_le_coe.mp h5))
    | coe e => exact ⟨e, rfl⟩

theorem dim_closure_iff_isArithVar : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ),
    CharZero ((MP ℤ m n).residueField x) →
      (topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) ↔ Geo.IsArithVar (ptIdeal x) d) := by
  intro m n x d hc
  refine ⟨GlobalTheory.T.arithmetic_variety_point_dimension m n x d hc, fun h => ?_⟩
  obtain ⟨e, he⟩ := exists_dim_closure_eq x
  have h' := GlobalTheory.T.arithmetic_variety_point_dimension m n x e hc he
  have h1 := h.2.2.2
  have h2 := h'.2.2.2
  have hde : d = e := by
    have h3 := h1.symm.trans h2
    have h4 : d + Fintype.card (Fin (m + 1)) = e + Fintype.card (Fin (m + 1)) := by exact_mod_cast h3
    omega
  rw [he, hde]

end GlobalTheory.CompanionTheory.MPDict.DimClosure
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVarietyStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_dim_iff_arithmetic_variety : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → (topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) ↔ Geo.IsArithVar (ptIdeal x) d) := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.DimClosure.dim_closure_iff_isArithVar | exact GlobalTheory.CompanionTheory.MPDict.DimClosure.dim_closure_iff_isArithVar | (intros; apply GlobalTheory.CompanionTheory.MPDict.DimClosure.dim_closure_iff_isArithVar <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneWeightedSumZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneWeightedSumZero
namespace GlobalTheory.CompanionTheory.Tempered

theorem weighted_antitone_eq_zero_of_tails_nonneg :
    ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 →
      (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) →
      ∀ i, e i = 0 := by
  intro h d e hd he hsum htail
  have hnn : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hneg
    rw [not_le] at hneg
    have hlt : ∑ k ∈ Finset.univ.filter (fun k => i ≤ k), d k * e k < 0 := by
      apply Finset.sum_neg
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact mul_neg_of_pos_of_neg (hd k) (lt_of_le_of_lt (he hk) hneg)
      · exact ⟨i, by simp⟩
    linarith [htail i]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hd k).le (hnn k)).1 hsum
  intro i
  rcases mul_eq_zero.1 (hz i (Finset.mem_univ i)) with h1 | h1
  · exact absurd h1 (hd i).ne'
  · exact h1

end GlobalTheory.CompanionTheory.Tempered
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneWeightedSumZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antitone_weighted_sum_zero : ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 → (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) → ∀ i, e i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg | exact GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg | (intros; apply GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrable
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.TemperedCore

theorem exists_lFactors_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecTemp k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsTemperedCoeff π → IsL 𝔪 π → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ ∀ (a : Fin h) (t : kˣ) (c : ℂ), Zl.ScalarBy (x a) t c → ‖c‖ = 1 := by
  intro k _ _ _ _ hSoc hCas hSeg 𝔪 N V _ _ π hN hsm hirr htemp hL
  have hy : ∀ Δ : Segment k, ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := fun Δ => by
    obtain ⟨ρ, hρ⟩ := hSeg Δ
    exact ⟨IrrGL.of ρ.ρ ρ.smooth ρ.irr, hρ.of_equiv (IrrGL.equivOf _ _ _)⟩
  choose y hyL using hy
  have hypos : ∀ Δ : Segment k, 0 < (y Δ).1 := fun Δ => by
    rw [← (hyL Δ).deg_eq]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  have hs : ∀ Δ : Segment k, ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y Δ) t c →
      ‖c‖ = nabs k t ^ (((y Δ).1 : ℝ) * s) := fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hypos Δ)
  choose f hf using hs
  obtain ⟨h, Δ, hΔ, hanti, hnp⟩ := GlobalTheory.T.multiset_antitone_enumeration 𝔪 f Segment.Precedes (fun a b hab =>
    GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (f a) (f b) (hyL a) (hyL b) (hf a) (hf b) hab)
  let x : Fin h → IrrGL (k := k) := fun a => y (Δ a)
  have hLF : LFactors 𝔪 x := ⟨Δ, ⟨hΔ, hnp⟩, fun i => hyL _⟩
  have hsumdeg : ∀ {h' : ℕ} (Δ' : Fin h' → Segment k) (x' : Fin h' → IrrGL (k := k)),
      Finset.univ.val.map Δ' = 𝔪 → (∀ i, IsLSeg (Δ' i) (x' i).rep) →
      ∑ a, (x' a).1 = (𝔪.map Segment.deg).sum := by
    intro h' Δ' x' hm hx'
    rw [← hm, Multiset.map_map]
    exact Finset.sum_congr rfl fun a _ => ((hx' a).deg_eq).symm
  have hdeg : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨Δ', ⟨hΔ', -⟩, hx'⟩, -⟩ := hL
    rw [hsumdeg Δ x hΔ (fun i => hyL _), ← hsumdeg Δ' x' hΔ' hx', hd']
  have hdrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hdeg]
    exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  have hsoc := hSoc 𝔪 h N x hdrev hLF π hL
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hdrev π hsm (fun a => hypos _) hsoc
  have hW := hCas N π hN hsm hirr htemp h (x ∘ Fin.rev) hdrev (fun a => hypos _) hjm
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have ht1 : nabs k t < 1 := GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero k t ht
  have ht0 : 0 < nabs k t := by
    have h0 : (MeasureTheory.distribHaarChar k t : NNReal) ≠ 0 := fun h0 => by
      have := map_mul (MeasureTheory.distribHaarChar k) t t⁻¹
      simp [h0] at this
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
  have hge : ∀ r : ℝ, nabs k t ^ r ≤ 1 → 0 ≤ r := fun r hr => by
    by_contra hneg
    exact absurd hr (not_le.2 (Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht0 ht1 (not_le.1 hneg)))
  choose c hc using fun a => GlobalTheory.T.central_character_exists k (x a) t
  obtain ⟨hpart, htot⟩ := hW t ht (c ∘ Fin.rev) (fun i => hc _)
  let e : Fin h → ℝ := fun i => f (Δ i)
  let d : Fin h → ℝ := fun i => ((x i).1 : ℝ)
  have hnorm : ∀ i, ‖c i‖ = nabs k t ^ (d i * e i) := fun i => hf (Δ i) t (c i) (hc i)
  have hprod : ∀ S : Finset (Fin h), ∏ i ∈ S, ‖c i‖ = nabs k t ^ (∑ i ∈ S, d i * e i) := fun S => by
    rw [Real.rpow_sum_of_pos ht0]
    exact Finset.prod_congr rfl fun i _ => hnorm i
  have hsum : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, ‖c i‖ = 1 := by
      rw [← htot]
      exact (Equiv.prod_comp Fin.revPerm (fun i => ‖c i‖)).symm
    rw [hprod] at h1
    refine le_antisymm ?_ (hge _ h1.le)
    have := hge (-∑ i, d i * e i) (by rw [Real.rpow_neg ht0.le, h1, inv_one])
    linarith
  have htail : ∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i := by
    intro j
    by_cases hj : (Fin.rev j).val + 1 < h
    · have h1 := hpart (Fin.rev j) hj
      have h2 := GlobalTheory.T.prod_le_rev_eq_prod_ge h (fun i => ‖c i‖) (Fin.rev j)
      rw [Fin.rev_rev] at h2
      have h3 : ∏ i ∈ Finset.univ.filter (fun i => i ≤ Fin.rev j), ‖(c ∘ Fin.rev) i‖ =
          ∏ i ∈ Finset.univ.filter (fun i => j ≤ i), ‖c i‖ := h2
      rw [h3, hprod] at h1
      exact hge _ h1
    · have hj0 : j.val = 0 := by
        have := j.isLt
        rw [Fin.val_rev] at hj
        omega
      have hf' : Finset.univ.filter (fun i => j ≤ i) = Finset.univ := by
        ext i
        simp [Fin.le_def, hj0]
      rw [hf', hsum]
  have he := GlobalTheory.T.antitone_weighted_sum_zero h d e (fun i => Nat.cast_pos.2 (hypos (Δ i))) hanti hsum htail
  refine ⟨h, x, hdeg, hLF, fun a t' c' hsc => ?_⟩
  have h1 := hf (Δ a) t' c' hsc
  have h2 : f (Δ a) = 0 := he a
  rw [h1, h2, mul_zero, Real.rpow_zero]

end GlobalTheory.CompanionTheory.TemperedCore
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrableStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_langlands_factors_square_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecTemp k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsTemperedCoeff π → IsL 𝔪 π → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ ∀ (a : Fin h) (t : kˣ) (c : ℂ), Zl.ScalarBy (x a) t c → ‖c‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.TemperedCore.exists_lFactors_unitary | exact GlobalTheory.CompanionTheory.TemperedCore.exists_lFactors_unitary | (intros; apply GlobalTheory.CompanionTheory.TemperedCore.exists_lFactors_unitary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulticonePointDescendsToSubvariety
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulticonePointDescendsToSubvariety
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderSub

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)
open GlobalTheory.CompanionTheory.MPDict.Onto GlobalTheory.CompanionTheory.MPDict.Under

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem point_eq_pt {N : ℕ} (t : Fin (N + 1) → ℂ) (ht : t ≠ 0) (hu : Ideal.span (Set.range t) = ⊤) :
    GlobalTheory.TuplePoint.point ℤ t ht = GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) t hu := by
  unfold GlobalTheory.TuplePoint.point GlobalTheory.ProjSpace.pt
  congr 1

theorem le_mCoordIdeal_of_mem_mcPts {P : Ideal (Geo.MRing (Bk n))} (hP : Geo.IsMultiHomogIdeal P)
    {z : (Σ k, Bk n k) → ℂ} (hz : z ∈ mcPts P) : P ≤ Geo.mCoordIdeal z := by
  obtain ⟨S, hS, hPS⟩ := hP
  have h0 := hz.2
  rw [hPS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have e : aeval z f = 0 := by
    have := h0 f (hPS ▸ Ideal.subset_span hf)
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
    simpa using this
  rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, e, C_0, mul_zero]

theorem ptIdeal_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {w : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder w z) :
    ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) = Geo.mCoordIdeal z := by
  have ht := blockVec_ne_zero hz'
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => z ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hz' k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
  let g : Sp ℂ ⟶ MP ℤ m n := w.1
  have hg : ∀ k, g ≫ prB n k = a k := fun k =>
    (comp_of_isUnder ht hz' H k).trans (point_eq_pt _ _ (hu k))
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  let x : MP ℤ m n := g p
  let θ : ℂ →+* (Sp ℂ).residueField p :=
    ((Sp ℂ).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp ℂ).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (z ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (z ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp ℂ).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : ℂ, ((Sp ℂ).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp ℂ).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (z ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  change ptIdeal x = _
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ z,
    ← mCoordIdeal_blockScale (fun k => θ (z ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

theorem exists_cxPt_of_mem_mcPts : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (z : (Σ k, Bk n k) → ℂ), z ∈ mcPts (ptIdeal (i (genericPoint X))) →
    ∃ y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀, IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ z hz
  obtain ⟨w, hw, -⟩ := existsUnique_isUnder m n z hz.1
  have hP : ptIdeal (i (genericPoint X)) ≤ ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) := by
    rw [ptIdeal_of_isUnder hz.1 hw]
    exact le_mCoordIdeal_of_mem_mcPts (isMultiProjPrime_ptIdeal m n _).2.1 hz
  have hs := (GlobalTheory.T.specializes_iff_point_ideal_le m n _ _).2 hP
  have hr : w.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range i :=
    hs.mem_closed i.isClosedEmbedding.isClosed_range ⟨_, rfl⟩
  have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨f, hf⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i w.1 Set.univ dense_univ
    fun q _ => by rwa [Subsingleton.elim q (IsLocalRing.closedPoint ℂ)]
  refine ⟨⟨f, by rw [← Category.assoc, hf]; exact w.2⟩, ?_⟩
  have e : PtsOver.map i rfl _ (⟨f, by rw [← Category.assoc, hf]; exact w.2⟩ : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) = w :=
    Subtype.ext hf
  rw [e]
  exact hw

end GlobalTheory.CompanionTheory.MPDict.UnderSub
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulticonePointDescendsToSubvarietyStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multicone_point_descends_to_subvariety : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (z : (Σ k, Bk n k) → ℂ), z ∈ mcPts (ptIdeal (i (genericPoint X))) →
    ∃ y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀, IsUnder (PtsOver.map i rfl _ y) z := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts | exact GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLev

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem trace_red_mul {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k A * red ϖ k B) = Ideal.Quotient.mk (lev ϖ k) (∑ a, ∑ c, A a c * B c a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, red, Matrix.map_apply, map_sum, map_mul]

theorem psiLev_holds : PositivityTheory.SiegelWeilFormula.Gunr.PsiLev := by
  unfold PositivityTheory.SiegelWeilFormula.Gunr.PsiLev
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT k X hX
  rw [trace_red_mul]
  show _ = PositivityTheory.SiegelWeilFormula.Gunr.psiF ψv ϖ _ k _
  unfold PositivityTheory.SiegelWeilFormula.Gunr.psiF PositivityTheory.PfSWUS.Loc.trPair
  congr 1
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.hermOf, PositivityTheory.SiegelWeilFormula.Gunr.GoodLoc.hermLev, PositivityTheory.SiegelWeilFormula.Gunr.matS,
    Matrix.map_apply, Matrix.of_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
    mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]
  rw [one_div, map_inv₀, map_ofNat]
  ring

end GlobalTheory.CompanionTheory.GunrLev

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.PsiLev := by
  first | exact @GlobalTheory.CompanionTheory.GunrLev.psiLev_holds | exact GlobalTheory.CompanionTheory.GunrLev.psiLev_holds | (intros; apply GlobalTheory.CompanionTheory.GunrLev.psiLev_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramified
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramified
namespace GlobalTheory.CompanionTheory.Exhaustion

open Filter Topology

variable {α E : Type*} [NormedAddCommGroup E]

theorem exists_subset_of_exhaustion {C : ℕ → Finset α} (hC : Monotone C) (hex : ∀ a, ∃ k, a ∈ C k)
    (s : Finset α) : ∃ k, s ⊆ C k :=
  ((tendsto_atTop_finset_of_monotone hC hex).eventually (eventually_ge_atTop s)).exists

theorem summable_norm_of_exhaustion {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable fun a => ‖f a‖ := by
  refine summable_of_sum_le (c := K) (fun a => norm_nonneg _) fun s => ?_
  obtain ⟨k, hk⟩ := exists_subset_of_exhaustion hC hex s
  exact (Finset.sum_le_sum_of_subset_of_nonneg hk fun _ _ _ => norm_nonneg _).trans (hK k)

theorem tsum_exhaust [CompleteSpace E] {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable f ∧ Tendsto (fun k => ∑ a ∈ C k, f a) atTop (𝓝 (∑' a, f a)) := by
  have hs : Summable f := (summable_norm_of_exhaustion hC hex hK).of_norm
  exact ⟨hs, hs.hasSum.comp (tendsto_atTop_finset_of_monotone hC hex)⟩

theorem tsum_exhaust_prop : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  intro α f C hC hex ⟨K, hK⟩
  exact ⟨summable_norm_of_exhaustion hC hex hK, (tsum_exhaust hC hex hK).2⟩

end GlobalTheory.CompanionTheory.Exhaustion
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramifiedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_exhaustion_unramified : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  first | exact @GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | exact GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | (intros; apply GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop <;> assumption)
end
end
