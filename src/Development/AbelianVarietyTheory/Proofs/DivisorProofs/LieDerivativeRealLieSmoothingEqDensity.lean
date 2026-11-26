module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem integral_mul_fderiv_lmul_eq_dens (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) (X : Lie E a) {G : Lie E a → ℂ} (hG : ContDiffOn ℝ ∞ G (invSet E a)) :
    ∫ x, α x * fderiv ℝ G x (lmul X x) ∂ν = ∫ x, dens X α x * G x ∂ν := by
  set L := lmul X with hL
  let b := Module.finBasis ℝ (Lie E a)
  let c : Fin (Module.finrank ℝ (Lie E a)) → Lie E a → ℂ := fun i x => α x * (b.repr (L x) i : ℝ)
  have hc : ∀ i, IsTest (invSet E a) (c i) := fun i => hα.mul (Complex.ofRealCLM.contDiff.comp
    ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp L.contDiff))
  have hG' : ∀ v, ContinuousOn (fun x => fderiv ℝ G x v) (invSet E a) := fun v =>
    (hG.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply continuousOn_const
  have e : ∀ x, α x * fderiv ℝ G x (L x) = ∑ i, c i x * fderiv ℝ G x (b i) := fun x => by
    conv_lhs => rw [← b.sum_repr (L x)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.mul_sum, c, Complex.real_smul, mul_assoc]
  have hdc : ∀ i x, fderiv ℝ (c i) x (b i) =
      α x * (b.repr (L (b i)) i : ℝ) + (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i) := by
    intro i x
    have h1 : HasFDerivAt (fun x => ((b.repr (L x) i : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) x :=
      (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)).hasFDerivAt
    have h2 := ((hα.1.differentiable (by simp) x).hasFDerivAt).mul h1
    rw [show c i = (α * fun x => ((b.repr (L x) i : ℝ) : ℂ)) from rfl, h2.fderiv]
    simp [Module.Basis.coord_apply, smul_eq_mul]
  have key : ∀ x, ∑ i, fderiv ℝ (c i) x (b i) = -dens X α x := by
    intro x
    have h3 : fderiv ℝ α x (L x) = ∑ i, (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i) := by
      calc fderiv ℝ α x (L x) = fderiv ℝ α x (∑ i, b.repr (L x) i • b i) := by rw [b.sum_repr]
        _ = _ := by rw [map_sum]; simp only [map_smul, Complex.real_smul]
    have h4 : (LinearMap.trace ℝ (Lie E a) L.toLinearMap : ℂ) = ∑ i, ((b.repr (L (b i)) i : ℝ) : ℂ) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
      simp [LinearMap.toMatrix_apply]
    simp only [hdc, Finset.sum_add_distrib, dens, neg_neg, ← hL, h3, h4, Finset.sum_mul]
    rw [add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have hi1 : ∀ i, Integrable (fun x => c i x * fderiv ℝ G x (b i)) ν := fun i =>
    (hc i).integrable_mul ν isOpen_invSet (hG' _)
  have hi2 : ∀ i, Integrable (fun x => fderiv ℝ (c i) x (b i) * G x) ν := fun i => by
    simpa using (((hc i).fderiv (b i)).mul contDiff_const (β := fun _ => (1 : ℂ))).integrable_mul ν isOpen_invSet
      hG.continuousOn
  calc ∫ x, α x * fderiv ℝ G x (L x) ∂ν = ∫ x, ∑ i, c i x * fderiv ℝ G x (b i) ∂ν := integral_congr_ae (.of_forall e)
    _ = ∑ i, ∫ x, c i x * fderiv ℝ G x (b i) ∂ν := integral_finsetSum _ fun i _ => hi1 i
    _ = ∑ i, ∫ x, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi2 i) (hi1 i)
        ((hc i).integrable_mul ν isOpen_invSet hG.continuousOn)
        (fun x _ => (hc i).1.differentiable (by simp) x)
        (fun x hx => (hG.contDiffAt (isOpen_invSet.mem_nhds ((hc i).2.2 hx))).differentiableAt (by simp)),
        integral_neg]
    _ = ∫ x, ∑ i, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := (integral_finsetSum _ fun i _ => (hi2 i).neg).symm
    _ = ∫ x, dens X α x * G x ∂ν := by
      refine integral_congr_ae (.of_forall fun x => ?_)
      dsimp only
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, key, neg_mul, neg_neg]

namespace SmoothingDeriv


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_rmul_fun : Continuous (fun y : Lie E a => rmul y) := by
  let R : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) :=
    { toFun := rmul
      map_add' := fun x y => ContinuousLinearMap.ext fun z =>
        show Matrix.of z * Matrix.of (x + y) = Matrix.of z * Matrix.of x + Matrix.of z * Matrix.of y by
          rw [← Matrix.of_add_of, Matrix.mul_add]
      map_smul' := fun c x => ContinuousLinearMap.ext fun z =>
        show Matrix.of z * Matrix.of (c • x) = c • (Matrix.of z * Matrix.of x) by
          rw [← Matrix.smul_of, Matrix.mul_smul] }
  exact R.continuous_of_finiteDimensional

omit [_root_.NumberField.IsTotallyComplex E] in
theorem lmul_oneL (y : Lie E a) : lmul (oneL E a) y = y := one_mul (Matrix.of y)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_lmul_pair : Continuous fun p : Lie E a × Lie E a => lmul p.1 p.2 :=
  Continuous.matrix_mul (A := fun p : Lie E a × Lie E a => Matrix.of p.1) (B := fun p : Lie E a × Lie E a => Matrix.of p.2)
    continuous_fst continuous_snd

theorem chart_smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (ψ : GA E a → ℂ) (g : GA E a) :
    chart (smoothing ν α ψ) g = fun z => ∫ y, α y * chart ψ g (lmul z y) ∂ν := by
  funext z
  by_cases h : IsUnit (Matrix.of z)
  · obtain ⟨u, hu⟩ := h
    obtain rfl : z = toL u.val := hu.symm
    rw [chart_val, smoothing, chart_mul]
    rfl
  · have h' : ∀ y, chart ψ g (lmul z y) = 0 := fun y => by
      have hn : ¬ IsUnit (Matrix.of (lmul z y)) := fun hy => h (by
        have h2 := (Matrix.isUnit_iff_isUnit_det _).1 hy
        change IsUnit (Matrix.of z * Matrix.of y).det at h2
        rw [Matrix.det_mul] at h2
        exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left h2))
      simp [chart, hn]
    simp only [h', mul_zero, integral_zero]
    simp [chart, h]

end SmoothingDeriv


open SmoothingDeriv in
theorem lieD_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {ψ : GA E a → ℂ} (hψ : ψ ∈ Sm E a) (X : Lie E a) (g : GA E a) :
    lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g := by
  set f := chart ψ g with hf
  have hfs : ContDiffOn ℝ ∞ f (invSet E a) := hψ g
  have hfd : ContinuousOn (fderiv ℝ f) (invSet E a) :=
    hfs.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
  have hmul : ∀ z y, z ∈ invSet E a → y ∈ invSet E a → lmul z y ∈ invSet E a :=
    fun z y hz hy => IsUnit.mul hz hy
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 isOpen_invSet (oneL E a) isUnit_one
  have hr : 0 < ε / 2 := half_pos ε0
  have hball : Metric.closedBall (oneL E a) (ε / 2) ⊆ invSet E a :=
    (Metric.closedBall_subset_ball (half_lt_self ε0)).trans hε
  set K := (fun p : Lie E a × Lie E a => lmul p.1 p.2) '' (Metric.closedBall (oneL E a) (ε / 2) ×ˢ tsupport α)
  have hKc : IsCompact K := ((isCompact_closedBall _ _).prod hα.2.1.isCompact).image continuous_lmul_pair
  have hKs : K ⊆ invSet E a := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hmul _ _ (hball hp1) (hα.2.2 hp2)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hfd.mono hKs)
  let F : Lie E a → Lie E a → ℂ := fun z y => α y * f (lmul z y)
  let F' : Lie E a → Lie E a → (Lie E a →L[ℝ] ℂ) := fun z y => α y • (fderiv ℝ f (lmul z y)).comp (rmul y)
  have hcontOn : ∀ z ∈ invSet E a, ContinuousOn (fun y => f (lmul z y)) (invSet E a) := fun z hz =>
    hfs.continuousOn.comp (lmul z).continuous.continuousOn fun y hy => hmul z y hz hy
  have hF'c : Continuous (F' (oneL E a)) := by
    refine continuous_of_tsupport fun y hy => ?_
    have hy' : y ∈ invSet E a := hα.2.2 (tsupport_smul_subset_left _ _ hy)
    simp only [F', lmul_oneL]
    exact hα.1.continuous.continuousAt.smul
      ((hfd.continuousAt (isOpen_invSet.mem_nhds hy')).clm_comp continuous_rmul_fun.continuousAt)
  have hbound : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), ‖F' z y‖ ≤ ‖α y‖ * (C * ‖rmul y‖) := by
    intro y z hz
    by_cases h0 : α y = 0
    · simp [F', h0]
    have hy : y ∈ tsupport α := subset_tsupport _ h0
    have hK : lmul z y ∈ K := ⟨(z, y), ⟨Metric.ball_subset_closedBall hz, hy⟩, rfl⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC _ hK) (norm_nonneg _))) (norm_nonneg _)
  have hbi : Integrable (fun y => ‖α y‖ * (C * ‖rmul y‖)) ν :=
    (hα.1.continuous.norm.mul (continuous_const.mul continuous_rmul_fun.norm)).integrable_of_hasCompactSupport
      hα.2.1.norm.mul_right
  have hdiff : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), HasFDerivAt (fun z => F z y) (F' z y) z := by
    intro y z hz
    by_cases h0 : α y = 0
    · simp only [F, F', h0, zero_mul, zero_smul]; exact hasFDerivAt_const 0 z
    have hy : y ∈ invSet E a := hα.2.2 (subset_tsupport _ h0)
    have hw : lmul z y ∈ invSet E a := hmul _ _ (hball (Metric.ball_subset_closedBall hz)) hy
    have h1 : HasFDerivAt f (fderiv ℝ f (lmul z y)) (rmul y z) :=
      ((hfs.contDiffAt (isOpen_invSet.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp z (rmul y).hasFDerivAt).const_mul (α y)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := F) (F' := F') (Metric.ball_mem_nhds _ hr)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) fun z hz =>
      (hα.continuous_mul isOpen_invSet (hcontOn z (hball (Metric.ball_subset_closedBall hz)))).aestronglyMeasurable)
    (hα.integrable_mul ν isOpen_invSet (hcontOn _ isUnit_one)) hF'c.aestronglyMeasurable
    (.of_forall hbound) hbi (.of_forall hdiff)
  have hint : Integrable (F' (oneL E a)) ν :=
    hbi.mono' hF'c.aestronglyMeasurable (.of_forall fun y => hbound y _ (Metric.mem_ball_self hr))
  rw [lieD, chart_smoothing, ← hf, hmain.fderiv, ContinuousLinearMap.integral_apply hint, smoothing,
    ← integral_mul_fderiv_lmul_eq_dens ν hα X hfs]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [F', lmul_oneL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

theorem lieD_smoothing_eq_dens : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a,
    ∀ (X : Lie E a) (g : GA E a), lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g :=
  fun _ _ _ _ _ ν _ _ hα _ hψ X g => lieD_smoothing ν hα hψ X g

end GlobalTheory.AutGrowth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensityStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieDerivative_realLieSmoothing_eq_density : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a, ∀ (X : Lie E a) (g : GA E a), lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g := by
  first | exact @GlobalTheory.AutGrowth.lieD_smoothing_eq_dens | exact GlobalTheory.AutGrowth.lieD_smoothing_eq_dens | (intros; apply GlobalTheory.AutGrowth.lieD_smoothing_eq_dens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

abbrev ksOpen (i : M.K.bundle.ι) (k : X.F.J) : M.X.Opens :=
  M.off ⊓ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)

def KSRel (i : M.K.bundle.ι) (k : X.F.J) {K : Type} [Field K] (z : Sp K ⟶ M.X) (x : K) : Prop :=
  ∀ [Algebra c.F K] (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K))
    (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k),
    X.F.ChartFr k (z ≫ toFlag M) hk Q → FrBor t Q P → IsTanFrame (psiSet H) P v →
    (∀ b, zv b ≫ toFlag M = X.ptY (v b)) →
    x * (Matrix.of fun a b =>  (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g)

theorem isKS_iff_ksRel (ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off) :
    IsKS M ω ↔ ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι) (k : X.F.J) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
      (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)),
      KSRel M i k z (H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω) :=
  ⟨fun h K _ z i k ho hi _ P Q t v zv O hO g hz hzv hk hQ ht hv hl =>
      h K P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl,
    fun h K _ _ P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl =>
      h K z i k ho hi P Q t v zv O hO g hz hzv hk hQ ht hv hl⟩

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpan
noncomputable section

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta CategoryTheory

namespace GlobalTheory.DlogSpan

theorem ker_finite_free {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {h : ℕ}
    (b : (Fin h → O) →ₗ[O] (Fin h → O)) :
    Module.Finite O (LinearMap.ker b) ∧ Module.Free O (LinearMap.ker b) := by
  have flat : ∀ S : Submodule O (Fin h → O), Module.Flat O S := fun S => by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have h1 : (a : O) • (x : Fin h → O) = 0 := congrArg Subtype.val ha
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero a.2)
  haveI := flat (LinearMap.range b)
  haveI : Module.Free O (LinearMap.range b) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property b.rangeRestrict LinearMap.id
    b.surjective_rangeRestrict
  have hs' : ∀ y, b (s y) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let π : (Fin h → O) →ₗ[O] LinearMap.ker b :=
    (LinearMap.id - s ∘ₗ b.rangeRestrict).codRestrict _ fun x => by
      simp [LinearMap.mem_ker, hs']
  have hπ : Function.Surjective π := fun x => ⟨x, by
    apply Subtype.ext
    have h0 : b.rangeRestrict x = 0 := Subtype.ext x.2
    simp [π, h0]⟩
  haveI hfin : Module.Finite O (LinearMap.ker b) := Module.Finite.of_surjective π hπ
  haveI := flat (LinearMap.ker b)
  exact ⟨hfin, Module.free_of_flat_of_isLocalRing⟩

theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) : ζ - 1 ∣ (k : O) := by
  have h0 := hζ.geom_sum_eq_zero hk
  have h1 : (k : O) = -∑ i ∈ Finset.range k, (ζ ^ i - 1) := by
    rw [Finset.sum_sub_distrib, h0]; simp
  rw [h1, dvd_neg]
  exact Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one ζ i

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

def pDivGroupOmegaBidualEquiv (G : PDivGroup p O) : G.omega ≃ₗ[O] G.dual.dual.omega :=
  LinearEquiv.ofLinear (omegaMap _ _ G.bidual.inv) (omegaMap _ _ G.bidual.hom)
    (by rw [← omegaMap_comp, Iso.inv_hom_id, omegaMap_id])
    (by rw [← omegaMap_comp, Iso.hom_inv_id, omegaMap_id])

theorem pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate (G : PDivGroup p O) (χ : G.dual.Tate) :
    pDivGroupOmegaBidualEquiv G (dlog G χ) = hodgeTate G.dual χ := by
  rw [hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap]
  rfl

theorem finite_free_and_sq_smul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), v.Integers O → GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ G : PDivGroup p O, Module.Finite O G.omega ∧ Module.Free O G.omega ∧ ∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G))) := by
  intro p hp C _ _ _ v O _ _ _ _ _ ε hε hv hS G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨u₁, u₂, hS⟩ := hS
  obtain ⟨D, e, fil, lie, hR⟩ := hS G.dual ℤ_[p] (padicAction _)
  let Ψ : G.omega ≃ₗ[O] D.Fil := pDivGroupOmegaBidualEquiv G ≪≫ₗ fil
  obtain ⟨hfin, hfree⟩ := ker_finite_free D.bb
  haveI : Module.Finite O D.Fil := hfin
  haveI : Module.Free O D.Fil := hfree
  refine ⟨Module.Finite.equiv Ψ.symm, Module.Free.of_equiv Ψ.symm, fun w => ?_⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by
    have h := hε 1
    rw [pow_one] at h
    exact h
  obtain ⟨-, -, -, hb, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have hθ : WittVector.fontaineTheta O p (nu ε) = (root ε).untilt - 1 := by
    rw [nu, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
  have hal : ∀ χ : G.dual.Tate, D.al (toO e χ) = (Ψ ((u₁ : O) • dlog G χ) : Fin _ → O) := by
    intro χ
    rw [hR.al_eq, ← hodgeTate_eq_omegaMap, ← pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate, map_smul]
    rfl
  have key : ∀ y, ∃ s ∈ Submodule.span O (Set.range (dlog G)),
      D.al y = (Ψ s : Fin _ → O) := by
    intro y
    refine ⟨∑ i, y i • (u₁ : O) • dlog G (e.symm (Pi.single i 1)), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · have hy : y = ∑ i, y i • toO e (e.symm (Pi.single i 1)) := by
        ext j
        simp [toO, Finset.sum_apply, Pi.single_apply, apply_ite]
      conv_lhs => rw [hy]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hal, map_smul Ψ (y i), Submodule.coe_smul]
  obtain ⟨y, hy⟩ := hb (Ψ w) (Ψ w).2
  obtain ⟨s, hs, hys⟩ := key y
  have h1 : WittVector.fontaineTheta O p (nu ε) • w = s := by
    apply Ψ.injective
    apply Subtype.ext
    rw [map_smul, Submodule.coe_smul, ← hy, hys]
  obtain ⟨c, hc⟩ := sub_one_dvd hζ hp.out.one_lt
  have h2 : (p : O) ^ 2 • w = ((p : O) * c) • s := by
    rw [← h1, hθ, smul_smul, pow_two]
    congr 1
    rw [mul_assoc, mul_comm c, ← hc]
  rw [h2]
  exact Submodule.smul_mem _ _ hs

end GlobalTheory.DlogSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_omega_finite_free_and_p_sq_mem_dlog_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), v.Integers O → GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ G : PDivGroup p O, Module.Finite O G.omega ∧ Module.Free O G.omega ∧ ∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G))) := by
  first | exact @GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span | exact GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span | (intros; apply GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lagAt {n d m : ℕ} (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  {u | At (evFin F v) u ∧ ∃ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), u = z * Cᵀ}

def IsLagrAt (σ : E →ₐ[F] E) {d m : ℕ} (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Prop :=
  IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) W.J) (C.map (compFin F E v))

def HeisInv {σ : E →ₐ[F] E} {n d m : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u ∈ lagAt v C, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → l φ₁ = l φ

end GlobalTheory.InertVacLag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PPAS

variable {S S' : Scheme.{0}}

theorem one_comp_of_isGrpPullback {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) :
    (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h A'))
  let g : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have e2 : g ≫ (1 : A ⟶ A) = 1 := by simp
  have e3 := congrArg (fun z : Over.mk (A'.hom ≫ f) ⟶ A => z.left) e2
  simp only [Over.comp_left] at e3
  rw [← e3] at e
  exact e

end GlobalTheory.PPAS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.WeilIntegral


set_option autoImplicit false in
open scoped TensorProduct in
theorem _root_.GlobalTheory.WeilIntegral.isAlgebraic_of_etale (S B : Type) [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
    [Algebra.Etale S B] (f : B) : IsAlgebraic S f := by
  classical
  let K := FractionRing S
  haveI : Algebra.Etale K (TensorProduct S K B) := Algebra.Etale.baseChange S B K
  haveI : Module.Finite K (TensorProduct S K B) :=
    Algebra.FormallyUnramified.finite_of_free K (TensorProduct S K B)
  haveI hal : Algebra.IsAlgebraic K (TensorProduct S K B) := Algebra.IsAlgebraic.of_finite K _
  obtain ⟨p, hp0, hp⟩ := hal.isAlgebraic ((1 : K) ⊗ₜ[S] f)
  set q := IsLocalization.integerNormalization (nonZeroDivisors S) p
  have hq0 : q ≠ 0 := fun h0 =>
    hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h0)
  have hq : Polynomial.aeval ((1 : K) ⊗ₜ[S] f) q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ p hp
  have hmap : (1 : K) ⊗ₜ[S] Polynomial.aeval f q = 0 := by
    rw [← hq, ← Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_algHom_apply]
    rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K B 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).2 (TensorProduct.isBaseChange S B K)
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S) (TensorProduct.mk S K B 1)).1 hmap
  refine ⟨Polynomial.C (s : S) * q, ?_, ?_⟩
  · exact mul_ne_zero (Polynomial.C_ne_zero.2 (nonZeroDivisors.coe_ne_zero s)) hq0
  · rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def]
    exact hs

end GlobalTheory.WeilIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat GlobalTheory.KernelNoTorsion GlobalTheory.HodgeTateTest GlobalTheory.PDiv GlobalTheory.SplitTorusPow
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusTateLie

section Torus

variable (C : Type) [Field C] {O : Type} [CommRing O] [Algebra O C] {X : Type} [AddCommGroup X]

def evalChar (χ : X) : (specO O O ⟶ splitTorus (Sp O) X) →* Cˣ :=
  (Units.map ((algebraMap O C).comp (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom).toMonoidHom).comp
    ((MonoidHom.eval (Multiplicative.ofAdd χ)).comp
      (splitTorusPointsEquiv (Sp O) X (specO O O)).toMonoidHom)

def lieMap {G G' : Over (Sp O)} [GrpObj G] [GrpObj G'] (φ : G ⟶ G') [IsMonHom φ] (x : LieG G) : LieG G' :=
  ⟨x.1 ≫ φ, by rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩

variable {C} {p : ℕ} [Fact p.Prime]

end Torus

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (φ : GmO O ⟶ P.Gt) [IsMonHom φ]
  (ζ : Tate p (specO O O ⟶ GmO O)) (hζ : Tate.map p (evalChar C (ULift.up (1 : ℤ))) ζ = P.eps.1)

include hζ

variable [Algebra ℤ_[p] O]

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

end AtPoint

end GlobalTheory.TorusTateLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology Set
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiff_lmul_uncurry : ContDiff ℝ ∞ fun q : Lie E a × Lie E a => lmul q.1 q.2 := by
  have e : (fun q : Lie E a × Lie E a => lmul q.1 q.2) = fun q i j => ∑ k, q.1 i k * q.2 k j := by
    funext q i j
    rfl
  rw [e]
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ContDiff.sum fun k _ => ?_
  exact ((contDiff_apply ℝ _ k).comp ((contDiff_apply ℝ _ i).comp contDiff_fst)).mul
    ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_snd))

theorem contDiffOn_smoothing_integrand {α : Lie E a → ℂ} (hα : IsTest (invSet E a) α) {ψ : GA E a → ℂ}
    (hψ : ψ ∈ Sm E a) (g : GA E a) :
    ContDiffOn ℝ ∞ (fun q : Lie E a × Lie E a => α (-q.2) * chart ψ g (lmul q.1 (-q.2))) (invSet E a ×ˢ univ) := by
  rintro ⟨p, t⟩ ⟨hp, -⟩
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases ht : -t ∈ tsupport α
  · have hpt : lmul p (-t) ∈ invSet E a := IsUnit.mul hp (hα.2.2 ht)
    have h1 : ContDiffAt ℝ ∞ (fun q : Lie E a × Lie E a => lmul q.1 (-q.2)) (p, t) :=
      (contDiff_lmul_uncurry.comp (contDiff_fst.prodMk contDiff_snd.neg)).contDiffAt
    have h3 : ContDiffAt ℝ ∞ (fun q : Lie E a × Lie E a => chart ψ g (lmul q.1 (-q.2))) (p, t) :=
      by
        have h4 := contDiffAt_chart hψ g hpt
        exact h4.comp (p, t) h1
    exact (hα.1.comp contDiff_snd.neg).contDiffAt.mul h3
  · have h0 : α =ᶠ[𝓝 (-t)] 0 := notMem_tsupport_iff_eventuallyEq.1 ht
    have h2 : (fun q : Lie E a × Lie E a => α (-q.2)) =ᶠ[𝓝 (p, t)] fun _ => 0 :=
      ((continuous_snd.neg).continuousAt.tendsto (x := (p, t))).eventually h0
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [h2] with q hq
    simp [hq]

theorem smoothing_mem_Sm (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ) (hα : IsTest (invSet E a) α)
    (ψ : GA E a → ℂ) (hψ : ψ ∈ Sm E a) : smoothing ν α ψ ∈ Sm E a := by
  intro g
  let G : Lie E a → Lie E a → ℂ := fun p t => α (-t) * chart ψ g (lmul p (-t))
  have hk : IsCompact ((fun t : Lie E a => -t) '' tsupport α) := hα.2.1.isCompact.image continuous_neg
  have hgs : ∀ p, ∀ x, p ∈ invSet E a → x ∉ (fun t : Lie E a => -t) '' tsupport α → G p x = 0 := by
    intro p x _ hx
    have : α (-x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ⟨-x, h, neg_neg x⟩
    simp [G, this]
  have hf : LocallyIntegrable (fun _ : Lie E a => (1 : ℂ)) ν := locallyIntegrable_const 1
  have H := contDiffOn_convolution_right_with_param_comp (μ := ν) (n := ⊤) (ContinuousLinearMap.mul ℝ ℂ)
    (contDiffOn_const (c := (0 : Lie E a))) isOpen_invSet hk hgs hf (contDiffOn_smoothing_integrand hα hψ g)
  refine H.congr fun x hx => ?_
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  rw [chart_val, smoothing, chart_mul, convolution_def]
  simp [G]

end GlobalTheory.AutGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctionsStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a, smoothing ν α ψ ∈ Sm E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_Sm | exact GlobalTheory.AutGrowth.smoothing_mem_Sm | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_Sm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasing
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  have hA : ∀ i k, ‖A i k‖ ≤ ‖toL A‖ := fun i k =>
    (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  have hB : ∀ i k, ‖B i k‖ ≤ ‖toL B‖ := fun i k =>
    (norm_le_pi_norm (toL B i) k).trans (norm_le_pi_norm (toL B) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖A i k * B k j‖ ≤ ∑ _k : Fin a, ‖toL A‖ * ‖toL B‖ :=
        Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
          (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (norm_nonneg _))
    _ = a * (‖toL A‖ * ‖toL B‖) := by simp

theorem continuousOn_toL_inv : ContinuousOn (fun x : Lie E a => toL (Matrix.of x)⁻¹) (invSet E a) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hd : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
  exact continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hd.unit)

end SlopeTestRemainingChoices

theorem smoothing_mem_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α →
    ∀ f ∈ growth E a, smoothing ν α f ∈ growth E a := by
  intro E _ _ _ a ν _ α hα f hf g
  obtain ⟨C, N, hC⟩ := hf g
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  have hK : IsCompact (tsupport α) := hα.2.1
  obtain ⟨M, M0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ tsupport α, ‖x‖ ≤ M ∧ ‖toL (Matrix.of x)⁻¹‖ ≤ M := by
    obtain ⟨M1, h1⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    obtain ⟨M2, h2⟩ := hK.exists_bound_of_continuousOn (continuousOn_toL_inv.mono hα.2.2)
    refine ⟨max 0 (max M1 M2), le_max_left _ _, fun x hx => ⟨?_, ?_⟩⟩
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  set c : ℝ := 1 + a * M with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) * M := by positivity
    linarith
  refine ⟨(∫ x, ‖α x‖ ∂ν) * C * c ^ N, N, fun y => ?_⟩
  have hb : ∀ x, ‖α x * chart f (g * infGL E a y) x‖ ≤ ‖α x‖ * (C * c ^ N * height y ^ N) := by
    intro x
    by_cases hx : x ∈ tsupport α
    · obtain ⟨u, hu⟩ : IsUnit (Matrix.of x) := hα.2.2 hx
      have hxu : x = toL u.val := by rw [hu]; rfl
      subst hxu
      obtain ⟨m1, m2⟩ := hM _ hx
      have m2' : ‖toL (u⁻¹).val‖ ≤ M := by rw [Matrix.coe_units_inv]; exact m2
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [chart_val, mul_assoc, ← map_mul]
      refine (hC (y * u)).trans ?_
      have hh : height (y * u) ≤ c * height y := by
        have e2 : ((y * u)⁻¹ : GL (Fin a) (Cinf E)).val = (u⁻¹).val * (y⁻¹).val := by
          rw [_root_.mul_inv_rev]; rfl
        have p1 := norm_toL_mul_le y.val u.val
        have p2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
        have n1 := norm_nonneg (toL y.val)
        have n2 := norm_nonneg (toL (y⁻¹).val)
        have q1 : (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * M * ‖toL y.val‖ := by
          calc (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * (‖toL y.val‖ * M) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m1 n1) (Nat.cast_nonneg a)
            _ = a * M * ‖toL y.val‖ := by ring
        have q2 : (a : ℝ) * (‖toL (u⁻¹).val‖ * ‖toL (y⁻¹).val‖) ≤ a * M * ‖toL (y⁻¹).val‖ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m2' (Nat.cast_nonneg a)) n2
        have aM : 0 ≤ (a : ℝ) * M := by positivity
        unfold height
        rw [show toL (y * u).val = toL (y.val * u.val) from rfl, e2, hc]
        nlinarith
      calc C * height (y * u) ^ N ≤ C * (c * height y) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * u)]) hh N) C0
        _ = C * c ^ N * height y ^ N := by rw [mul_pow, mul_assoc]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  change ‖∫ x, α x * chart f (g * infGL E a y) x ∂ν‖ ≤ _
  have hi : Integrable (fun x => ‖α x‖) ν :=
    hα.1.continuous.norm.integrable_of_hasCompactSupport hα.2.1.norm
  refine (norm_integral_le_of_norm_le (hi.mul_const _) (.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const]
  ring

end GlobalTheory.AutGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasingStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ f ∈ growth E a, smoothing ν α f ∈ growth E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_growth | exact GlobalTheory.AutGrowth.smoothing_mem_growth | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]


open Classical in
def pre (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : L := if h : ∃ x, ι x = z then h.choose else 0

theorem pre_spec (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (h : ∃ x, ι x = z) : ι (pre ι z) = z := by
  unfold pre
  rw [dite_eq_left h]
  exact h.choose_spec

def tJ (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {m n : Type} (J : Matrix m n E) : Matrix m n L :=
  fun i j => pre ι (ι 1 * inclR (F := F) (AF F) (J i j))

def gram (σL : L →+* L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) L :=
  (P : Matrix (Fin n) (Fin n) L)ᵀ * tJ ι J * (P : Matrix (Fin n) (Fin n) L).map σL

def xm (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n d : ℕ} (PV : GL (Fin n) L) (PW : GL (Fin d) L) :
    Matrix (Fin d) (Fin n) L →+ Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun x := ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ).map ι
  map_zero' := by ext i j; simp
  map_add' x y := by ext i j; simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem xm_apply (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n d : ℕ} (PV : GL (Fin n) L) (PW : GL (Fin d) L) (x : Matrix (Fin d) (Fin n) L) :
    xm ι PV PW x = ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ).map ι := rfl

end GlobalTheory.InertLocFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedStr
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS.Modif

theorem geometricallyConnected_str : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (U : Y.Opens) (D : ℕ)
    (M : Modif p U D), SmoothOfRelativeDimension D p → GeometricallyConnected p → Dense (U : Set Y) →
    GeometricallyConnected M.str := by
  intro F _ Y p U D M hs hc hd
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : Nonempty Y := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Sp F))
    obtain ⟨y, -⟩ := p.surjective x
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := hd.nonempty
  have : Surjective (U.ι ≫ p) := ⟨fun x => ⟨⟨u, hu⟩, Subsingleton.elim _ _⟩⟩
  have hU : GeometricallyIrreducible (U.ι ≫ p) := inferInstance
  have : IsIso (M.σ ∣_ U) := M.iso
  have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ p) := by
    show (M.opn.ι ≫ M.σ) ≫ p = _
    rw [← morphismRestrict_ι, Category.assoc]
  have hO : GeometricallyIrreducible (M.opn.ι ≫ M.str) := by
    have sq : IsPullback (M.σ ∣_ U) (M.opn.ι ≫ M.str) (U.ι ≫ p) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [e, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback sq hU
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hy : UniversallyOpen y := inferInstance
  have hf : UniversallyOpen fst := MorphismProperty.of_isPullback h.flip hy
  have hdense : Dense ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := M.dense.preimage fst.isOpenMap
  have hsq : IsPullback (fst ∣_ M.opn) ((fst ⁻¹ᵁ M.opn).ι ≫ snd) (M.opn.ι ≫ M.str) y :=
    (isPullback_morphismRestrict fst M.opn).paste_vert h
  have : IrreducibleSpace (fst ⁻¹ᵁ M.opn) :=
    hO.geometrically_irreducibleSpace y _ _ hsq
  have hirr : IsIrreducible ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := by
    have := (IrreducibleSpace.isIrreducible_univ (fst ⁻¹ᵁ M.opn)).image _
      (fst ⁻¹ᵁ M.opn).ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have : IrreducibleSpace Z := by
    have hc := hirr.closure
    rw [hdense.closure_eq] at hc
    exact irreducibleSpace_def Z |>.mpr hc
  exact (connectedSpace_iff_univ).mpr (IrreducibleSpace.isIrreducible_univ Z).isConnected

end GlobalTheory.CompHS.Modif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

theorem cHess_apply_eq_ddbar {n : ℕ} {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hg : ContDiffAt ℝ 2 g x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.cHess n g x j k =
      ddbar g x (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
  have e : ReciprocityTheory.L2DbarEstimates.wdb n k g = fun y => dbar g y (EuclideanSpace.single k 1) := by
    funext y
    simp only [ReciprocityTheory.L2DbarEstimates.wdb, dbar_apply, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
    ring
  rw [ddbar_eq_del_dbar hg, del_apply, ReciprocityTheory.L2DbarEstimates.cHess, Matrix.of_apply, e]
  simp only [ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
  ring

end GlobalTheory.CurveDens

namespace GlobalTheory.CurveDens

end GlobalTheory.CurveDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormEqDot
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Matrix

noncomputable section

open scoped MatrixOrder ComplexOrder

namespace GlobalTheory.HermFamFrame

def formRight {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) : V →+ ℂ :=
  AddMonoidHom.mk' (nm.form σ x) (nm.add_right σ x)

theorem form_sum_right {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) {ι : Type} (s : Finset ι) (a : ι → K) (w : ι → V) :
    nm.form σ x (∑ j ∈ s, a j • w j) = ∑ j ∈ s, σ (a j) * nm.form σ x (w j) := by
  have := map_sum (formRight nm σ x) (fun j => a j • w j) s
  simp only [formRight, AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun j _ => nm.smul_right σ (a j) x (w j)

theorem form_sum_left {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (y : V) {ι : Type} (s : Finset ι) (a : ι → K) (w : ι → V) :
    nm.form σ (∑ i ∈ s, a i • w i) y = ∑ i ∈ s, starRingEnd ℂ (σ (a i)) * nm.form σ (w i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← nm.conj_symm, form_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, nm.conj_symm]

end GlobalTheory.HermFamFrame

end
end
