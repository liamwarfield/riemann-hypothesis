module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeights
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis

theorem zetaHolValueAt_of_heightBounds (l1 : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) (l2 : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q) : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) := by
  intro D V μ hμ m hm Φ hE ha hreg f₁ f₂ h₁ h₂ hZ s₀ E₀ hv
  obtain ⟨C', c, hio⟩ := l1 D V
  have key : ∀ (H : ℂ → GA D (dblSp V) → ℂ) (z : ℂ) (r : ℝ), 0 < r →
      (∀ s ∈ ball z r, LeftInv (GQ (dblSp V)) (H s)) →
      (∀ g, DifferentiableOn ℂ (H · g) (ball z r)) →
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball z r ×ˢ univ) →
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball z r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
      (∀ s ∈ ball z r, DblConv V μ m (H s) f₁ f₂) ∧
        DifferentiableOn ℂ (fun s => dblInt V μ m (H s) f₁ f₂) (ball z r) := by
    rintro H z r hr hinv hd hc ⟨C, N, hb⟩
    obtain ⟨bound, hbi, hbd⟩ := l2 D V μ m hm f₁ f₂ h₁ h₂ C' c hio C N
    have hcont : ∀ s ∈ ball z r, Continuous (H s) := fun s hs =>
      hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    have hli : ∀ s ∈ ball z r, LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (H s) f₁ f₂) := fun s hs =>
      leftInv_dblIntegrand hμ (hinv s hs) h₁.1 h₂.1
    have hmeas : ∀ s ∈ ball z r, AEStronglyMeasurable (dblIntegrandQ V μ (H s) f₁ f₂)
        ((autMeasure V m).prod (autMeasure V m)) := by
      intro s hs
      have e' : dblIntegrandQ V μ (H s) f₁ f₂ =
          dblIntegrand V μ (H s) f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
        funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk (hli s hs) _ _)
      rw [e']
      exact ((continuous_dblIntegrand hμ (hcont s hs) h₁.continuous h₂.continuous).measurable.comp
        (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
    refine ⟨fun s hs => ⟨hli s hs, hbi.mono' (hmeas s hs) (ae_of_all _ fun q => hbd (H s) (hinv s hs) (hb s hs) q)⟩, ?_⟩
    have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
      (μ := (autMeasure V m).prod (autMeasure V m)) (F := fun q s => dblIntegrandQ V μ (H s) f₁ f₂ q)
      (isOpen_ball (x := z) (ε := r)) hmeas
      (ae_of_all _ fun q => by
        simp only [dblIntegrandQ, dblIntegrand]
        exact (((hd _).mul_const _).mul_const _).mul_const _)
      fun x hx => ⟨ball z r, isOpen_ball.mem_nhds hx, bound, hbi,
        ae_of_all _ fun q y hy => hbd (H y) (hinv y hy) (hb y hy) q⟩
    exact this.1
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  set Z : ℂ → ℂ := fun s => dblInt V μ m (eisCont V Φ s) f₁ f₂ with hZdef
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, r, H, hr, e, hd, hc, C, N, hb⟩ := hreg s₁
    have hinvH : ∀ s ∈ ball s₁ r, LeftInv (GQ (dblSp V)) (H s) := by
      intro s hs γ hγ g
      rcases eq_or_ne s s₁ with rfl | h0
      · have t1 := ((hd (γ * g)).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        have t2 := ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        refine tendsto_nhds_unique t1 (t2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with w h1 h2
        rw [e w h2 h1, e w h2 h1, hinvE w γ hγ g]
      · rw [e s hs h0, e s hs h0, hinvE s γ hγ g]
    have han : AnalyticAt ℂ (fun s => dblInt V μ m (H s) f₁ f₂) s₁ :=
      (key H s₁ r hr hinvH hd hc ⟨C, N, hb⟩).2.analyticAt (ball_mem_nhds _ hr)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * dblInt V μ m (H s) f₁ f₂) s₁ := by
      have : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
      exact (this.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr)] with w h1 h2
    have e1 : eisCont V Φ w = ((w - s₁) ^ k)⁻¹ • H w := by
      funext g
      rw [Pi.smul_apply, e w h2 h1 g, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H w) (f₁ := f₁) (f₂ := f₂) ((w - s₁) ^ k)⁻¹ 1 1
    simp only [one_smul, map_one, mul_one] at e2
    simp only [Z, e1, e2]
  have hext : IsMerExt (zeta V μ m Φ f₁ f₂) univ Z := by
    refine ⟨isRightDomain_univ, fun s _ => hmer s, (V.rank : ℝ) / 2, fun s hs => ?_⟩
    have : eisCont V Φ s = eis V (Φ s) := funext fun g => eqOn_cont (ha g) hs
    simp only [Z, zeta, this]
  obtain ⟨k, hk⟩ := hreg s₀
  obtain ⟨r, hr, hd, hc, C, N, hb⟩ := hk.of_eisValueAt hv
  obtain ⟨hconv, hdiff⟩ := key (eisCont V Φ) s₀ r hr (fun s _ => hinvE s) hd hc ⟨C, N, hb⟩
  have e0 := hv.eisCont_eq
  refine ⟨e0 ▸ hconv s₀ (mem_ball_self hr), hZ, Z, hext.isExtAt trivial, hdiff.analyticAt (ball_mem_nhds _ hr), ?_⟩
  simp only [Z, e0]

theorem zetaHolValueAt_of_eisValueAt : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) :=
  zetaHolValueAt_of_heightBounds GlobalTheory.T.exists_height_doublingEmbedding_le_pow_mul_heights GlobalTheory.T.exists_integrable_bound_doubling_integrand_quotient

end GlobalTheory.Eis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPointStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_zeta_value_at_eisenstein_holomorphic_point : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) := by
  first | exact @GlobalTheory.Eis.zetaHolValueAt_of_eisValueAt | exact GlobalTheory.Eis.zetaHolValueAt_of_eisValueAt | (intros; apply GlobalTheory.Eis.zetaHolValueAt_of_eisValueAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealIntertwinerNeZeroKFiniteTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealIntertwinerNeZeroKFiniteTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.ItNe

open GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

theorem exists_ne_zero_inclK : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ h' : GlobalTheory.Chain.IoLift.KSm M', ∃ φ y, It φ (GlobalTheory.Chain.IoLift.inclK h' y) ≠ 0 := by
  classical
  intro hHC D V W S S' M M' θ ω pt It hIt h'
  apply Classical.byContradiction
  intro hcon
  push_neg at hcon
  apply hIt.ne
  have key : ∀ φ (w : ∀ τ, M.H τ) (s : Finset D.what₂.Tau) (v : M'.Vec),
      (∀ τ ∉ s, (v τ : M'.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ) →
      ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) = 0 := by
    intro φ w s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have e : PiTensorProduct.tprod ℂ v =
          GlobalTheory.Chain.IoLift.inclK h' (PiTensorProduct.tprod ℂ fun τ => ⟨v τ, hv τ (by simp)⟩) := by
        rw [GlobalTheory.Chain.IoLift.inclK, PiTensorProduct.map_tprod]; rfl
      rw [e, hcon, map_zero, map_zero]
    | insert τ s hτ ih =>
      intro v hv
      obtain ⟨c, hc⟩ := hIt.bdd φ w
      let ℓ₀ : M'.sm τ →ₗ[ℂ] ℂ :=
        (ellT M w ∘ₗ inclT M ∘ₗ It φ) ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
      obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
      have hℓv : ∀ y : M'.sm τ, ℓ (y : M'.H τ) =
          ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := fun y => by
        have := LinearMap.congr_fun hℓ y
        simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
      have hsob : Formalism.L2.Theta.Sobolev₂ (lieAt W τ) (M'.rep τ) ℓ := by
        refine ⟨[[]], c * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, by simp, fun u hu => ?_⟩
        have hy : u ∈ M'.sm τ := Submodule.subset_span hu
        have h1 := hc (Function.update v τ ⟨u, hy⟩)
        rw [← hℓv ⟨u, hy⟩] at h1
        have h2 : ∏ ρ, ‖((Function.update v τ ⟨u, hy⟩ ρ : M'.sm ρ) : M'.H ρ)‖ =
            ‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖ := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
          congr 1
          refine Finset.prod_congr rfl fun ρ hρ => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
        rw [h2] at h1
        simp only [List.map_cons, List.map_nil, List.foldr_nil, List.sum_cons, List.sum_nil, add_zero]
        calc ‖ℓ u‖ ≤ c * (‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) := h1
          _ = c * (∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) * ‖u‖ := by ring
      have hk : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ, ℓ u = 0 := by
        intro u hu
        have hy : u ∈ M'.sm τ := h' τ hu
        rw [show u = ((⟨u, hy⟩ : M'.sm τ) : M'.H τ) from rfl, hℓv]
        refine ih _ fun ρ hρ => ?_
        by_cases e : ρ = τ
        · subst e; rw [Function.update_self]; exact hu
        · rw [Function.update_of_ne e]; exact hv ρ (by simp [e, hρ])
      have h0 := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D W S' M' τ ℓ hsob hk (v τ) (v τ).2
      rwa [hℓv, Function.update_eq_self] at h0
  refine LinearMap.ext fun φ => LinearMap.ext fun x => ?_
  simp only [LinearMap.zero_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul]
    have h0 : It φ (PiTensorProduct.tprod ℂ v) = 0 := by
      refine (tensorLaw D V S M).inj ?_
      rw [map_zero]
      exact (tensorLaw D V S M).sep _ fun w => key φ w Finset.univ v (by simp)
    rw [h0, smul_zero]
  | add a b ha hb => rw [map_add (f := _), ha, hb, add_zero]

end GlobalTheory.Chain.IoLift.ItNe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealIntertwinerNeZeroKFiniteTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiner_ne_zero_KFinite_tensor : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ h' : GlobalTheory.Chain.IoLift.KSm M', ∃ φ y, It φ (GlobalTheory.Chain.IoLift.inclK h' y) ≠ 0 := by
  first | exact @GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK | exact GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK | (intros; apply GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ItOnto
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin maxCpt)
open GlobalTheory.Chain.IoLift

theorem kfin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ = kFin M τ := Submodule.span_eq (kFin M τ)

theorem span_le_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) :
    Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} ≤ LinearMap.range (inclK h) := by
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨PiTensorProduct.tprod ℂ fun τ => ⟨(v τ : M.H τ), (kfin_eq M τ) ▸ hv τ⟩, ?_⟩
  rw [inclK_tprod]

theorem range_le_span {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) (y : KT M) :
    inclK h y ∈ Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [map_smul, inclK_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => (kfin_eq M τ).symm ▸ (u τ).2, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem kfinSpan_le_span_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = It P v} := by
  intro hD hH D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  choose hs a ha hirr using fun τ => GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D V S M τ
  have h : KSm M := hs
  have h' : KSm M' := fun τ => (GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D W S' M' τ).1
  have hval := GlobalTheory.T.real_intertwiner_values_kFinite D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  have inj := inclK_injective h
  obtain ⟨I, hI⟩ : ∃ I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M,
      ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)
    refine ⟨(It.compl₂ (inclK h')).compr₂ g, fun φ y => ?_⟩
    obtain ⟨z, hz⟩ := span_le_range M h (hval φ (inclK h' y))
    change inclK h (g (It φ (inclK h' y))) = _
    rw [← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]
  obtain ⟨χS, χT, hω, hexp⟩ := hW
  have hL := fun τ => GlobalTheory.T.lieAction_fockOperators_scalars_trace D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ (aS τ) (aT τ) hθ hω
    (hexp τ).1 (hexp τ).2 (isVacF_of_isVacVec hf)
  have hstep : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ, ∃ φ', ∀ y, intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) = I φ' y := by
    intro τ X hX φ
    obtain ⟨φ', hd⟩ : ∃ φ', ∀ v, DerT M τ X (It φ v) (It φ' v) := ⟨_, hIt.eqg τ X hX φ _ ((hL τ).1 X hX φ)⟩
    refine ⟨φ', fun y => inj ?_⟩
    have e := hd (inclK h' y)
    rw [← hI] at e
    rw [hI]
    exact derT_unique ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _) e
  obtain ⟨N, hNd⟩ : ∃ N : Submodule ℂ (KT M), N = Submodule.span ℂ {x | ∃ φ y, I φ y = x} := ⟨_, rfl⟩
  have hN : ∀ τ (X : lieAt V τ), ∀ x ∈ N, intersection_update_fsHerm_neg_one τ (a τ X) x ∈ N := by
    intro τ X x hx
    rw [hNd] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, y, rfl⟩ := hx
      obtain ⟨φ', hφ'⟩ := hstep τ X X.2 φ
      exact Submodule.subset_span ⟨φ', y, (hφ' y).symm⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h0 : N ≠ ⊥ := by
    obtain ⟨φ, y, hne⟩ := GlobalTheory.T.exists_realIntertwiner_ne_zero_KFinite_tensor hH D V W S S' M M' θ ω _ It hIt h'
    intro e
    refine hne ?_
    have : I φ y ∈ N := hNd ▸ Submodule.subset_span ⟨φ, y, rfl⟩
    rw [e, Submodule.mem_bot] at this
    rw [← hI, this, map_zero]
  have htop := GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable D.what₂.Tau (fun τ => kFin M τ) (fun τ => lieAt V τ) (fun τ X => a τ X) hirr N hN h0
  intro w hw
  obtain ⟨z, rfl⟩ := span_le_range M h hw
  have hz : z ∈ N := htop ▸ Submodule.mem_top
  rw [hNd] at hz
  clear hw
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, y, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ, inclK h' y, range_le_span M' h' y, (hI φ y)⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ItOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValuesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFiniteSpan_le_span_realIntertwiner_values : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = It P v} := by
  first | exact @GlobalTheory.ItOnto.kfinSpan_le_span_it | exact GlobalTheory.ItOnto.kfinSpan_le_span_it | (intros; apply GlobalTheory.ItOnto.kfinSpan_le_span_it <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SchwartzMaj

variable {D : D7}

theorem finPart_section (D : D7) : Continuous (finPart D) ∧
    ∃ s : (Af D.host.F ⊗[D.host.F] D.host.E) → AE D, Continuous s ∧ ∀ z, finPart D (s z) = z := by
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨?_, fun z => e.symm (0, z), hes.comp (continuous_const.prodMk continuous_id), fun z => ?_⟩
  · have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  · rw [← (he _).2, RingEquiv.apply_symm_apply]

theorem maj_mono (θ : InfFam D) {m n : ℕ} {K K' : Set (Mx D m n)} (h : K ⊆ K') (N : ℕ) (x : Mx D m n) :
    GlobalTheory.Unf.maj θ K N x ≤ GlobalTheory.Unf.maj θ K' N x := by
  by_cases hx : GlobalTheory.Unf.InBox K x
  · have hx' : GlobalTheory.Unf.InBox K' x := let ⟨k, hk, h0⟩ := hx; ⟨k, h hk, h0⟩
    unfold GlobalTheory.Unf.maj
    rw [if_pos hx, if_pos hx']
  · have h0 : GlobalTheory.Unf.maj θ K N x = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hx]
    rw [h0]
    exact GlobalTheory.Unf.maj_nonneg θ K' N x

theorem realSize_le (θ : InfFam D) (m n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Mx D m n,
    1 + GlobalTheory.Unf.realSize θ x ≤
      c * (1 + ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖) := by
  set a : ℝ := ∑ _τ : D.what₂.Tau, ∑ _i : Fin m, ∑ _j : Fin n, (1 : ℝ) with ha
  have ha0 : 0 ≤ a :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one
  refine ⟨1 + a, by linarith, fun x => ?_⟩
  set y : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hy
  have h1 : GlobalTheory.Unf.realSize θ x ≤ a * ‖y‖ := by
    rw [ha]
    simp only [Finset.sum_mul, one_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact (norm_le_pi_norm (y τ i) j).trans ((norm_le_pi_norm (y τ) i).trans (norm_le_pi_norm y τ))
  have h2 := norm_nonneg y
  nlinarith

def HasMaj (θ : InfFam D) {m n : ℕ} (φ : Mx D m n → ℂ) : Prop :=
  Continuous φ ∧ ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * GlobalTheory.Unf.maj θ K N x

theorem HasMaj.zero (θ : InfFam D) (m n : ℕ) : HasMaj θ (0 : Mx D m n → ℂ) :=
  ⟨continuous_const, ∅, isCompact_empty, fun _ => ⟨0, fun _ => by simp⟩⟩

theorem HasMaj.add {θ : InfFam D} {m n : ℕ} {φ φ' : Mx D m n → ℂ} (h : HasMaj θ φ) (h' : HasMaj θ φ') :
    HasMaj θ (φ + φ') := by
  obtain ⟨hc, K, hK, hb⟩ := h
  obtain ⟨hc', K', hK', hb'⟩ := h'
  refine ⟨hc.add hc', K ∪ K', hK.union hK', fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  obtain ⟨C', hC'⟩ := hb' N
  refine ⟨|C| + |C'|, fun x => ?_⟩
  have h1 : ‖φ x‖ ≤ |C| * GlobalTheory.Unf.maj θ (K ∪ K') N x :=
    (hC x).trans (mul_le_mul (le_abs_self C) (maj_mono θ Set.subset_union_left N x) (GlobalTheory.Unf.maj_nonneg θ K N x)
      (abs_nonneg C))
  have h2 : ‖φ' x‖ ≤ |C'| * GlobalTheory.Unf.maj θ (K ∪ K') N x :=
    (hC' x).trans (mul_le_mul (le_abs_self C') (maj_mono θ Set.subset_union_right N x) (GlobalTheory.Unf.maj_nonneg θ K' N x)
      (abs_nonneg C'))
  rw [add_mul]
  exact (norm_add_le (φ x) (φ' x)).trans (add_le_add h1 h2)

theorem HasMaj.smul {θ : InfFam D} {m n : ℕ} {φ : Mx D m n → ℂ} (a : ℂ) (h : HasMaj θ φ) : HasMaj θ (a • φ) := by
  obtain ⟨hc, K, hK, hb⟩ := h
  refine ⟨hc.const_smul a, K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  refine ⟨‖a‖ * C, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg a)

theorem hasMaj_pure {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    HasMaj θ fun x : Mx D m n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j)) := by
  obtain ⟨hfc, s, hs, hsec⟩ := finPart_section D
  have hgc : Continuous g := hg.1.continuous
  have hgs : HasCompactSupport g := hg.2
  have hy : Continuous fun x : Mx D m n => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ m n).matrix_elem i j
  have hz : Continuous fun x : Mx D m n =>
      (fun i j => finPart D (x i j) : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    continuous_pi fun i => continuous_pi fun j => hfc.comp (continuous_id.matrix_elem i j)
  let t : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → Mx D m n := fun z => Matrix.of fun i j => s (z i j)
  have ht : Continuous t :=
    continuous_matrix fun i j => hs.comp ((continuous_apply j).comp (continuous_apply i))
  refine ⟨(f.continuous.comp hy).mul (hgc.comp hz), t '' tsupport g, hgs.isCompact.image ht, fun N => ?_⟩
  obtain ⟨G, hG⟩ := hgs.exists_bound_of_continuous hgc
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  obtain ⟨c, hc0, hc⟩ := realSize_le θ m n
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖f y‖ ≤ S := by
    have h := fun y =>
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f y
    simp only [norm_iteratedFDeriv_zero] at h
    exact ⟨_, h⟩
  have hS0 : 0 ≤ S := le_trans (by positivity) (hS 0)
  refine ⟨c ^ N * S * G, fun x => ?_⟩
  by_cases h0 : g (fun i j => finPart D (x i j)) = 0
  · simp only [h0, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (GlobalTheory.Unf.maj_nonneg θ _ N x)
  · have hin : GlobalTheory.Unf.InBox (t '' tsupport g) x := by
      refine ⟨t fun i j => finPart D (x i j), ⟨_, subset_tsupport g h0, rfl⟩, ?_⟩
      ext i j
      change finPart D (x i j - s (finPart D (x i j))) = 0
      rw [(finPart D).map_sub, hsec, sub_self]
    have hr := GlobalTheory.Unf.realSize_nonneg θ x
    unfold GlobalTheory.Unf.maj
    rw [if_pos hin, le_mul_inv_iff₀ (by positivity), norm_mul]
    have h1 := hc x
    have h2 := hS (fun τ i j => compAt θ τ x i j)
    have h3 := hG (fun i j => finPart D (x i j))
    generalize (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) = y at h1 h2 ⊢
    generalize g (fun i j => finPart D (x i j)) = b at h3 ⊢
    have h4 : (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ c ^ N * (1 + ‖y‖) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) h1 N
    calc ‖f y‖ * ‖b‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ ‖f y‖ * G * (c ^ N * (1 + ‖y‖) ^ N) := by gcongr
      _ = c ^ N * ((1 + ‖y‖) ^ N * ‖f y‖) * G := by ring
      _ ≤ c ^ N * S * G := by gcongr

theorem hasMaj_of_mem {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n) : HasMaj θ φ := by
  refine Submodule.span_induction (p := fun φ _ => HasMaj θ φ) ?_ (HasMaj.zero θ m n)
    (fun _ _ _ _ h h' => h.add h') (fun a _ _ h => h.smul a) hφ
  rintro _ ⟨f, g, hg, rfl⟩
  exact hasMaj_pure hθ f g hg

theorem continuous_and_le_maj : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → Continuous φ ∧ ∃ K : Set (Mx D m n), IsCompact K ∧
      ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * GlobalTheory.Unf.maj θ K N x :=
  fun D θ hθ m n φ hφ => hasMaj_of_mem hθ ((GlobalTheory.T.isSchwartzBruhat_iff_mem_adelicMatrixSchwartzSpace D θ hθ m n φ).1 hφ)

end GlobalTheory.SchwartzMaj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → Continuous φ ∧ ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * GlobalTheory.Unf.maj θ K N x := by
  first | exact @GlobalTheory.SchwartzMaj.continuous_and_le_maj | exact GlobalTheory.SchwartzMaj.continuous_and_le_maj | (intros; apply GlobalTheory.SchwartzMaj.continuous_and_le_maj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.RealPar

variable {D : D7}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem finPart_cA_eq (z : AE D) :
    finPart D (cA D z) = Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, sigR, finPart]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]


open Classical in
theorem exists_real_point {θ : InfFam D} (hθ : IsInfFam θ) (τ₀ : D.what₂.Tau) (t : ℝ) :
    ∃ x : Ainf D.host.F, ∀ τ, θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = if τ = τ₀ then (t : ℂ) else 0 := by
  obtain ⟨w, ⟨hw, hf⟩, -⟩ := exists_unique_of_comp_finPart D θ hθ 1 1
    (fun τ => fun _ _ => if τ = τ₀ then (t : ℂ) else 0) 0
  set a : AE D := w 0 0 with ha
  have hcomp : ∀ τ, θ τ (infPart D a) = if τ = τ₀ then (t : ℂ) else 0 := fun τ => by
    have := congrFun (congrFun (hw τ) 0) 0
    simpa [compAt] using this
  have hfin : finPart D a = 0 := by
    have := congrFun (congrFun hf 0) 0
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.zero_apply, map_zero] at this
    exact this
  have hRC := RealComp.real_components D θ hθ
  have hc : cA D a = a := by
    have h0 : cA D a - a = 0 := by
      apply hRC.2.2.2
      · intro τ
        rw [map_sub, map_sub, hRC.2.1 a τ, hcomp τ]
        split_ifs <;> simp
      · rw [map_sub, finPart_cA_eq, hfin]
        simp
    exact sub_eq_zero.mp h0
  obtain ⟨y, hy⟩ := GlobalTheory.DetRootRows.fixed_mem_range a hc
  refine ⟨fstA D.host.F y, fun τ => ?_⟩
  rw [← hcomp τ, ← hy]
  rfl

theorem realPar_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ l l' : D.what₂.Tau → ℝ, HasRealPar ψ θ l → HasRealPar ψ θ l' → l = l' := by
  classical
  intro D ψ θ hθ l l' hl hl'
  funext τ₀
  by_contra hne
  have hd : l τ₀ - l' τ₀ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨x, hx⟩ := exists_real_point hθ τ₀ (1 / (2 * (l τ₀ - l' τ₀)))
  have e := (hl x).symm.trans (hl' x)
  simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp e
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h1 : ((l τ₀ : ℂ) - l' τ₀) * ((1 / (2 * (l τ₀ - l' τ₀)) : ℝ) : ℂ) = n := by
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have h2 : ((l τ₀ : ℂ) - l' τ₀) * ((1 / (2 * (l τ₀ - l' τ₀)) : ℝ) : ℂ) = 1 / 2 := by
    have hd' : ((l τ₀ : ℂ) - l' τ₀) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp
  rw [h2] at h1
  have h3 : ((n : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; exact h1.symm
  have h4 : (n : ℝ) = 1 / 2 := by exact_mod_cast h3
  have h5 : (2 : ℝ) * n = 1 := by rw [h4]; norm_num
  have h6 : (2 : ℤ) * n = 1 := by exact_mod_cast h5
  omega

end GlobalTheory.StdUnn.RealPar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUniqueStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_parameters_addChar_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ l l' : D.what₂.Tau → ℝ, HasRealPar ψ θ l → HasRealPar ψ θ l' → l = l' := by
  first | exact @GlobalTheory.StdUnn.RealPar.realPar_unique | exact GlobalTheory.StdUnn.RealPar.realPar_unique | (intros; apply GlobalTheory.StdUnn.RealPar.realPar_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isHeight_hgtStd : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → IsHeight (hgtStd A a κ p) := by
  intro D A μ hμ κ hκ a p hc p₁ hp₁ α hα k hk
  have hq : κ.symm p₁ ∈ siegel A := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ (κ.symm p₁)).2 (by simpa using hp₁)
  set q : siegel A := ⟨κ.symm p₁, hq⟩ with hqdef
  have hk' : (p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hc]; simpa [mul_assoc] using hk
  have e : κ.symm (p₁ * k) * (p : GA D (dblSp A))⁻¹ =
      ((q * p⁻¹ : siegel A) : GA D (dblSp A)) * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹) := by
    simp [hqdef, map_mul, mul_assoc]
  have hdet : aP A q = Matrix.GeneralLinearGroup.det α :=
    GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D A μ hμ κ hκ q α (by simpa [hqdef] using hα)
  show hgt A a (κ.symm (p₁ * k) * (p : GA D (dblSp A))⁻¹) * absA D (aP A p) = absA D (Matrix.GeneralLinearGroup.det α)
  rw [e, hgt_mul A a (q * p⁻¹) hk', ← map_mul, ← map_mul, inv_mul_cancel_right, hdet]

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunctionStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryHeight_isSiegelHeightFunction : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → IsHeight (hgtStd A a κ p) := by
  first | exact @GlobalTheory.StdUnn.isHeight_hgtStd | exact GlobalTheory.StdUnn.isHeight_hgtStd | (intros; apply GlobalTheory.StdUnn.isHeight_hgtStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousConjA
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (cE cE_cE cA_inc cA_cA ConjIsom conj_map_mem_unitaryGroup)
open scoped TensorProduct

namespace GlobalTheory.ConjAutProps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem continuous_conjA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

end GlobalTheory.ConjAutProps

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.CondBound

open Filter Topology

variable (D : D7)

abbrev line : HSp D :=
  Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E)
    Formalism.BasicNotions.Examples₂.star_isIntegral 1

def o : Fin (line D).rank := ⟨0, Nat.one_pos⟩

theorem sum_line (f : Fin (line D).rank → AE D) : ∑ i, f i = f (o D) := Fin.sum_univ_one f

theorem hO_line (x y : WO (line D) (line D)) :
    hO (line D) (line D) x y = incA D ((line D).gram⁻¹ (o D) (o D)) * cA D (y (o D) (o D)) *
      incA D ((line D).gram (o D) (o D)) * x (o D) (o D) := by
  unfold hO
  simp only [sum_line]

abbrev latL : AddSubgroup (WO (line D) (line D)) :=
  latO (line D) (line D) (GlobalTheory.PlaceModel.latFrame (line D) : Set (Fin (line D).rank → D.host.E))
    (GlobalTheory.PlaceModel.latFrame (line D) : Set (Fin (line D).rank → D.host.E)) fun _ => True

theorem infPart_latL {u : WO (line D) (line D)} (hu : u ∈ latL D) : infPart D (u (o D) (o D)) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hw
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_apply, RingHom.map_add (f := _), hx, hy, add_zero]
  | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem infPart_r (a : Af D.host.F) : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a)) = 0 := by
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem finPart_r (N : ℕ) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (N : Af D.host.F))) = finPart D (incA D (N : D.host.E)) := by
  rw [map_natCast, map_natCast]
  show (N : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [← map_natCast (algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) N]
  rfl

theorem den_latL : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latL D, M • finPart D (u (o D) (o D)) ∈ intAE D := by
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := line D) (T := line D) hΛ.1.fg hΛ.1.fg
  refine ⟨M, hM, fun u hu => ?_⟩
  have h2 : toEAf D ((M : AE D) * u (o D) (o D)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [RingHom.map_mul, map_natCast]; exact hden u hu (o D) (o D)
  have h3 := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h2
  rw [RingHom.map_mul, map_natCast] at h3
  rw [nsmul_eq_mul]
  exact h3

theorem exists_compact_fin (M : ℕ) (hM : 0 < M) : ∃ K0 : Set (AE D), IsCompact K0 ∧
    ∀ z : AE D, infPart D z = 0 → M • finPart D z ∈ intAE D → z ∈ K0 := by
  obtain ⟨C, hC, hCd⟩ := GlobalTheory.SmoothForms.Cover.exists_compact_denom D M hM
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm '' ({0} ×ˢ C), (isCompact_singleton.prod hC).image hc, fun z h1 h2 => ?_⟩
  have e1 : (e z).1 = 0 := by have := (he z).1; exact this.trans h1
  have e2 : M • (e z).2 ∈ intAE D := by have := (he z).2; rw [this]; exact h2
  exact ⟨e z, Set.mk_mem_prod (Set.mem_singleton_iff.2 e1) (hCd _ e2), e.symm_apply_apply z⟩

theorem tendsto_r : Tendsto (fun n : ℕ => algebraMap (AF D.host.F) (AE D)
    (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F))) atTop (𝓝 0) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun n : ℕ => pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) atTop (𝓝 (0 : AF D.host.F)) :=
    (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds
      (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele D.host.F)
  have hcont : Continuous (algebraMap (AF D.host.F) (AE D)) := by
    have hfun : (algebraMap (AF D.host.F) (AE D) : AF D.host.F → AE D) = fun t => t • (1 : AE D) := by
      funext t; exact Algebra.algebraMap_eq_smul_one t
    haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
    rw [hfun]; exact continuous_id.smul (continuous_const (y := (1 : AE D)))
  have := (hcont.tendsto 0).comp h
  rwa [map_zero] at this

theorem exists_small (C' : Set (AE D)) (hC' : IsCompact C') (U : AddSubgroup (AE D)) (hU : IsOpen (U : Set (AE D))) :
    ∃ n : ℕ, ∀ z ∈ C', algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * z ∈ U := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hev : ∀ᶠ t in 𝓝 (0 : AE D), ∀ z ∈ C', t * z ∈ U := by
    refine hC'.eventually_forall_of_forall_eventually fun z _ => ?_
    have h0 : ((0 : AE D), z).1 * ((0 : AE D), z).2 ∈ U := by rw [zero_mul]; exact U.zero_mem
    exact (continuous_mul.continuousAt (x := ((0 : AE D), z))).preimage_mem_nhds (hU.mem_nhds h0)
  exact ((tendsto_r D).eventually hev).exists

theorem isCompact_mul (c : AE D) {K : Set (AE D)} (hK : IsCompact K) : IsCompact ((fun z => c * z) '' K) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact hK.image (continuous_const.mul continuous_id)

theorem isCompact_mul_conj (c : AE D) {K : Set (AE D)} (hK : IsCompact K) :
    IsCompact ((fun z => c * cA D z) '' K) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact hK.image (continuous_const.mul (GlobalTheory.ConjAutProps.continuous_conjA D))


set_option maxHeartbeats 1000000 in
theorem annihilator_finPart_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (AE D),
    IsOpen (U : Set (AE D)) → ∃ K : Set (AE D), IsCompact K ∧ ∀ x : AE D,
      (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) →
        ∃ k ∈ K, finPart D (x - k) = 0 := by
  intro D ψ hψ U hU
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := den_latL D
  obtain ⟨K0, hK0c, mem0⟩ := exists_compact_fin D M hM
  have memL : ∀ u ∈ latL D, u (o D) (o D) ∈ K0 := fun u hu => mem0 _ (infPart_latL D hu) (hden u hu)
  let c0 : AE D := incA D D.host.xi0 * incA D ((line D).gram⁻¹ (o D) (o D)) * incA D ((line D).gram (o D) (o D))
  obtain ⟨n, hn⟩ := exists_small D _ (isCompact_mul_conj D c0 hK0c) U hU
  let r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F))
  have hN : ((n.factorial : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos n).ne'
  refine ⟨(fun z => incA D ((n.factorial : ℕ) : D.host.E)⁻¹ * z) '' K0, isCompact_mul D _ hK0c, ?_⟩
  intro x hx
  let u : WO (line D) (line D) := Matrix.of fun _ _ => x * r
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    show infPart D (x * r) = 0
    rw [RingHom.map_mul, infPart_r, mul_zero]
  have huL : u ∈ latL D := by
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ (line D) (line D) _ _ hψ hΛ hΛ).1 u hu0).2 fun u' hu' => ?_
    have ha : r * (c0 * cA D (u' (o D) (o D))) ∈ U := hn _ ⟨_, memL u' hu', rfl⟩
    have hai : infPart D (r * (c0 * cA D (u' (o D) (o D)))) = 0 := by
      rw [RingHom.map_mul, infPart_r, zero_mul]
    have h := hx _ ha hai
    rw [symplO, hO_line]
    convert h using 3
    show _ = x * _
    simp only [c0, u, Matrix.of_apply]
    ring
  refine ⟨_, ⟨_, memL u huL, rfl⟩, ?_⟩
  show finPart D (x - incA D ((n.factorial : ℕ) : D.host.E)⁻¹ * (x * r)) = 0
  have h1 : finPart D (incA D ((n.factorial : ℕ) : D.host.E)⁻¹) * finPart D r = 1 := by
    rw [finPart_r, ← RingHom.map_mul, ← RingHom.map_mul, inv_mul_cancel₀ hN, map_one, map_one]
  rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, mul_left_comm, h1, mul_one, sub_self]

end GlobalTheory.CondBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_annihilator_openSubgroup_finPart_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) → ∃ K : Set (AE D), IsCompact K ∧ ∀ x : AE D, (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) → ∃ k ∈ K, finPart D (x - k) = 0 := by
  first | exact @GlobalTheory.CondBound.annihilator_finPart_compact | exact GlobalTheory.CondBound.annihilator_finPart_compact | (intros; apply GlobalTheory.CondBound.annihilator_finPart_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinate_decay_realEntries : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (N : ℕ), ∃ C : ℝ≥0, ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ * ENNReal.ofReal ((1 + realSize θ x) ^ N) ≤ C * supSob ψ θ N f := by
  first | exact @GlobalTheory.Unf.mixS_decay | exact GlobalTheory.Unf.mixS_decay | (intros; apply GlobalTheory.Unf.mixS_decay <;> assumption)
end
