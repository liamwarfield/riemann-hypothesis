module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntHaar

open MeasureTheory

variable {k : Type} [Field k]

def glLinearEquiv {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₗ[k] (Fin t → k) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k))
    (Matrix.toLin' ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem coe_glLinearEquiv_symm {t : ℕ} (w : GL (Fin t) k) :
    ((glLinearEquiv w).symm : (Fin t → k) → (Fin t → k)) =
      ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec := by
  funext v
  rfl

theorem det_glLinearEquiv {t : ℕ} (w : GL (Fin t) k) :
    LinearEquiv.det (glLinearEquiv w) = Matrix.GeneralLinearGroup.det w := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k)) = _
  rw [LinearMap.det_toLin']
  rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem map_inv_mulVec (t : ℕ) [m : MeasurableSpace (Fin t → k)] [hb : BorelSpace (Fin t → k)]
    (μ : Measure (Fin t → k)) [μ.IsAddHaarMeasure] (w : GL (Fin t) k) :
    μ.map ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ := by
  borelize k
  have hp : @BorelSpace (Fin t → k) _ MeasurableSpace.pi := Pi.borelSpace
  have e : m = MeasurableSpace.pi := hb.measurable_eq.trans hp.measurable_eq.symm
  subst e
  rw [← coe_glLinearEquiv_symm, ← det_glLinearEquiv]
  exact GlobalTheory.ChangeVarPi.map_symm_eq_smul k (Fin t) μ (glLinearEquiv w)

theorem smInt_comp_inv_mulVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] {Z : Type} [AddCommGroup Z] [Module ℂ Z] (w : GL (Fin t) k) (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (fun v => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ φ := by
  intro k _ _ _ _ t _ _ μ _ Z _ _ w φ hl _
  have hc : Continuous ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec :=
    continuous_const.matrix_mulVec continuous_id
  have hval : ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) =
      (((distribHaarChar k (Matrix.GeneralLinearGroup.det w) : NNReal) : ℝ) : ℂ) := by
    rw [detChar_apply, val_absPow, Complex.cpow_one]
    rfl
  rw [hval]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  have hlev : μ ((fun x => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec x)) ⁻¹' {v}) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ (φ ⁻¹' {v}) := by
    rw [← Measure.smul_apply, ← map_inv_mulVec t μ w]
    exact (Measure.map_apply hc.measurable (hl.isOpen_fiber v).measurableSet).symm
  rw [hlev, ENNReal.toReal_smul, smul_smul, NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul]

end GlobalTheory.CompanionTheory.Rodier.SmIntHaar

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_integral_linear_change : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] {Z : Type} [AddCommGroup Z] [Module ℂ Z] (w : GL (Fin t) k) (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (fun v => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ φ := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec | exact GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec | (intros; apply GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunction
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.NodeFlat

theorem flatFn_nodeFn : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  intro E _ _ _ r s e₁ e₂ h₁ h₂
  have ap : ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
      (c : GL (Fin (r + s)) (Af E)), c ∈ GlobalTheory.CompanionTheory.LimV.KO E (r + s) →
      nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 :=
    fun u m k c hc => GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ u m k c hc
  have hleft : ∀ (v : BlockIx (r + s) r → Ad E) (x : GA E (r + s)),
      nodeFn e₁ e₂ (unip v * x) = nodeFn e₁ e₂ x := by
    intro v x
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [← mul_assoc, ← mul_assoc, ← PositivityTheory.Rg.Rs.InducedTensorMap.D.unip_add', ap _ _ _ _ hc, ap _ _ _ _ hc]
  have hright : ∀ (x : GA E (r + s)) (k' : Kinf E (r + s)), ∀ c' ∈ GlobalTheory.CompanionTheory.LimV.KO E (r + s),
      nodeFn e₁ e₂ (x * cf (r + s) k' c') = nodeFn e₁ e₂ x := by
    intro x k' c' hc'
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [mul_assoc _ (cf (r + s) k c), PositivityTheory.Rg.Rs.InducedTensorMap.cf_mul,
      ap _ _ _ _ ((GlobalTheory.CompanionTheory.LimV.KO E (r + s)).mul_mem hc hc'), ap _ _ _ _ hc]
  have key : ∀ m : GA E r × GA E s,
      ContDiffAt ℝ ∞ (chart (nodeFn e₁ e₂) (lev (Ad E) r s m)) (oneL E (r + s)) := by
    intro m
    obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
    have c₁ : ContDiffAt ℝ ∞ (fun y => e₁ (m.1 * infGL E r (b₁ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₁.sm m.1 (val_mem_invSet (b₁ (oneL E (r + s))))).comp (oneL E (r + s)) hb₁
      simpa only [Function.comp_def, chart_val] using this
    have c₂ : ContDiffAt ℝ ∞ (fun y => e₂ (m.2 * infGL E s (b₂ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₂.sm m.2 (val_mem_invSet (b₂ (oneL E (r + s))))).comp (oneL E (r + s)) hb₂
      simpa only [Function.comp_def, chart_val] using this
    refine ContDiffAt.congr_of_eventuallyEq (c₁.mul c₂) ?_
    filter_upwards [hloc] with y hy
    have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
      show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
      rw [← hy]
      rfl
    conv_lhs => rw [hyw, chart_val]
    obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
    rw [hv, ap _ _ _ _ ((GlobalTheory.CompanionTheory.LimV.KO E (r + s)).one_mem)]
  refine ⟨fun x => ?_, hright, ?_⟩
  · obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [ap _ _ _ _ hc]
    exact mul_ne_zero (h₁.ne _) (h₂.ne _)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, hg, rfl⟩ := exists_iw x
  have e1 : chart (nodeFn e₁ e₂) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (nodeFn e₁ e₂) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact hleft u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => nodeFn e₁ e₂ (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      nodeFn e₁ e₂ := by
    funext z
    show nodeFn e₁ e₂ (z * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k)) = nodeFn e₁ e₂ z
    rw [mul_assoc, ← infGL_comm]
    exact hright z k g hg
  rw [e2]
  exact key m

end GlobalTheory.CompanionTheory.LimV.NodeFlat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunctionStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_node_function : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn | exact GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotal
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ThTot
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.ThTot.OneRow

variable {D : D7}

theorem evalPoly_temperate {m n : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (z τ))) := by
  have coord : ∀ k : D.what₂.Tau × Fin m × Fin n × Bool, Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) := by
    rintro ⟨τ, i, j, b⟩
    let L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))
    cases b
    · exact L.hasTemperateGrowth
    · exact (Complex.conjCLE.toContinuousLinearMap.comp L).hasTemperateGrowth
  induction p using MvPolynomial.induction_on with
  | C a => simpa [evalPoly] using Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) + fun z => evalPoly q (fun τ => Matrix.of (z τ)) := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X k) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) * fun z =>
          if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1 := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.mul (coord k)

theorem exists_schwartz_poly_gauss (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ))
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) :
    ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z,
      f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine ⟨SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ (fun z : D.what₂.Tau → Fin V.rank → Fin n → ℂ =>
    evalPoly p (fun τ => Matrix.of (z τ))) f, fun z => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evalPoly_temperate p)]
  simp [hf]

theorem fockA_le_schwartzA (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    fockA θ V n l s ≤ schwartzA θ V.rank n := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  obtain ⟨f, hf⟩ := exists_schwartz_poly_gauss n V l hl s hs p
  refine Submodule.subset_span ⟨f, g, hg, ?_⟩
  funext x
  rw [hf]
  rfl

theorem gram_rank_one_one : (V1 D).gram = 1 := by
  refine Matrix.ext fun (i j : Fin 1) => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  show ∑ k : Fin 1, star ((Pi.basisFun D.host.E (Fin 1)) 0 k) * Formalism.BasicNotions.Examples₂.sgn false * (Pi.basisFun D.host.E (Fin 1)) 0 k =
    (1 : Matrix (Fin 1) (Fin 1) D.host.E) 0 0
  simp [Formalism.BasicNotions.Examples₂.sgn]

theorem gram_at_place_rank_one (τ : D.what₂.Tau) : gramAt D (V1 D) τ = 1 := by
  unfold gramAt
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cartan_involution_rank_one (τ : D.what₂.Tau) : IsCartanInv (gramAt D (V1 D) τ) 1 := by
  rw [gram_at_place_rank_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one]
  exact Matrix.PosDef.one

theorem gram_rank_one_eq_one : gA (V1 D) = (1 : Mx D (V1 D).rank (V1 D).rank) := by
  unfold gA rat
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

set_option synthInstance.maxHeartbeats 400000 in
theorem incA_algebraMap (c : D.host.F) :
    incA D (algebraMap D.host.F D.host.E c) = (algebraMap D.host.F (AF D.host.F) c) • (1 : AE D) := by
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c) =
    (algebraMap D.host.F (AF D.host.F) c) • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem pr_eq {p : ℕ} (b₀ : HermE D 1) (c : D.host.F) (hc : algebraMap D.host.F D.host.E c = b₀.1 0 0)
    (x y : Mx D 1 p) :
    pr b₀ x y = (algebraMap D.host.F (AF D.host.F) c) • (inner (V1 D) x y : Mx D p p) := by
  have h1 : b₀.1.map (incA D) = (algebraMap D.host.F (AF D.host.F) c) • (1 : Mx D 1 1) := by
    refine Matrix.ext fun (i j : Fin 1) => ?_
    fin_cases i; fin_cases j
    simp [← hc, incA_algebraMap]
  have h2 : (inner (V1 D) x y : Mx D p p) = HMul.hMul (adj x) y := by
    unfold GlobalTheory.StdUnn.inner
    rw [gram_rank_one_eq_one]
    exact congrArg (fun t : Mx D 1 p => (HMul.hMul (adj x) t : Mx D p p)) (Matrix.one_mul y)
  rw [h2]
  unfold pr
  rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

theorem trA_smul (a : AF D.host.F) (z : AE D) : trA (a • z) = a * trA z := by
  simp [trA, map_smul]

theorem halfTr_smul (a : AF D.host.F) (z : AE D) : halfTr (a • z) = a * halfTr z := by
  simp only [halfTr, trA_smul]; ring

theorem exists_base (b₀ : HermE D 1) (h : b₀.1.det ≠ 0) :
    ∃ c : D.host.F, c ≠ 0 ∧ algebraMap D.host.F D.host.E c = b₀.1 0 0 := by
  have h0 : b₀.1 0 0 ≠ 0 := by simpa [Matrix.det_fin_one] using h
  have hfix : star (b₀.1 0 0) = b₀.1 0 0 := congrFun (congrFun b₀.2 0) 0
  have hF : b₀.1 0 0 ∈ D.host.F :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E _).1 hfix
  exact ⟨⟨_, hF⟩, fun e => h0 (by simpa using congrArg (fun u : D.host.F => (u : D.host.E)) e), rfl⟩

theorem exists_par (ψ₀ : AddChar (AF D.host.F) ℂ) (h₀ : IsStdChar D ψ₀ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (a : D.host.F) (ha : a ≠ 0) :
    IsCharAF D.host.F (shift ψ₀ a) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ₀ a) θ l ∧ ∀ τ, l τ ≠ 0 := by
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have haE : algebraMap D.host.F D.host.E a ≠ 0 := (map_ne_zero _).2 ha
  have hst : star (algebraMap D.host.F D.host.E a) = algebraMap D.host.F D.host.E a :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2
  have hsk : IsSkew (-D.host.xi0 / algebraMap D.host.F D.host.E a) := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) haE, ?_⟩
    rw [star_div₀, star_neg, hst, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, neg_div]
  obtain ⟨lam, hlam, hc, l, hp, habs⟩ := shift_char_realPar D ψ₀ h₀ θ hθ _ hsk
  have : lam = a := by
    apply (algebraMap D.host.F D.host.E).injective
    rw [hlam]
    field_simp
  subst this
  refine ⟨hc, l, hp, fun τ h => ?_⟩
  have := habs τ
  rw [h, abs_zero] at this
  have h1 : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 hxi
  have h2 : tauE D τ (-D.host.xi0 / algebraMap D.host.F D.host.E lam) ≠ 0 := (map_ne_zero _).2 hsk.1
  exact (div_ne_zero (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)) this.symm

theorem oneTotal : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  intro hC hM hF D p μ 𝓕 hμ ψ hψ b₀ hdet χ hχ hr θ hθ
  obtain ⟨c, hc0, hc⟩ := exists_base b₀ hdet
  obtain ⟨ψ₀, h₀, lam, hlam0, hlam⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hne : lam * c ≠ 0 := mul_ne_zero hlam0 hc0
  obtain ⟨hψ₁, l, hpar, hl⟩ := exists_par ψ₀ h₀ θ hθ (lam * c) hne
  have hs : ∀ t, shift ψ₀ (lam * c) t = ψ (algebraMap D.host.F (AF D.host.F) c * t) := by
    intro t
    rw [hlam]
    simp [shift, AddChar.mulShift_apply, map_mul, mul_assoc]
  obtain ⟨ω, hω⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D p (V1 D) ψ₀ h₀ (lam * c) hne χ hχ hr θ hθ μ 𝓕 hμ
  intro u huc hub hu
  refine hF D p θ hθ l hl μ 𝓕 hμ u huc hub fun φ hφ => ?_
  have hφS := fockA_le_schwartzA θ (V1 D) p l hl _ (fun τ => cartan_involution_rank_one τ) hφ
  let Φ : schwartzA θ (V1 D).rank p := ⟨φ, hφS⟩
  have e : ∀ g h : G D p, ω (g * h) Φ = ω g (ω h Φ) := fun g h => by rw [map_mul]; rfl
  have hT : IsTh ψ χ θ b₀ μ (fun h => (ω h Φ).1) :=
    { mem := fun h => (ω h Φ).2
      cont := hC D p (V1 D) _ hψ₁ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
      maj := hM D p _ hψ₁ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hpar hl Φ hφ
      levi := by
        intro g a hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e]
        exact hω.levi g a hg _ y
      unip := by
        intro g b hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e, hω.unip g b hg _ y, hs, pr_eq b₀ c hc, Matrix.mul_smul, Matrix.trace_smul, halfTr_smul]
      weyl := by
        intro g hg h x
        show (ω (g * h) Φ).1 x = _
        rw [e, hω.weyl g hg _ x]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show _ * shift ψ₀ (lam * c) _ = _ * ψ _
        rw [hs, pr_eq b₀ c hc x y, Matrix.trace_smul, trA_smul] }
  have h1 : ∫ y, u y * conj ((ω 1 Φ).1 y) ∂μ = 0 := hu _ hT
  have h2 : (ω 1 Φ).1 = φ := by rw [map_one]; rfl
  rw [h2] at h1
  exact h1

end GlobalTheory.CompanionTheory.ThTot.OneRow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotalStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_theta_total : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal | exact GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairRestriction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairRestriction
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV

namespace GlobalTheory.CompanionTheory.EGlue.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_le_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ ≤ prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem prodSpan_le_pairSpace (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) ≤ pairSpace U₁ U₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem slice_mem (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) (m₁ : GA E a) :
    (fun y => F (m₁, y)) ∈ U₂.map (Sm E b).subtype := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, by funext y; simp⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.EGlue.Restrict

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairRestrict_holds : PairRestrict := by
  intro E _ _ _ a b U₁ U₂ U₂' F hF hs
  have hS₂ : ∀ m₁, (fun y => F (m₁, y)) ∈ U₂'.map (Sm E b).subtype := by
    intro m₁
    obtain ⟨φ, -, hφ⟩ := Restrict.slice_mem U₁ U₂ F hF m₁
    exact ⟨φ, hs m₁ φ hφ, hφ⟩
  have h := GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices (U₁.map (Sm E a).subtype) ⊤
    (U₂.map (Sm E b).subtype) (U₂'.map (Sm E b).subtype) F
    (Restrict.pairSpace_le_prodSpan U₁ U₂ hF) (fun _ => Submodule.mem_top) hS₂
  refine Restrict.prodSpan_le_pairSpace U₁ U₂' ?_
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact ⟨p, hp.1, q, hq.2, rfl⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairRestrictionStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_restriction : GlobalTheory.CompanionTheory.EGlue.PairRestrict := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds | exact GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedNode
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaH
namespace Bl.FirstLemmaH

theorem goal1 :
  ∀ {A : Type} (W : Submodule.{0, 0} Complex (A → Complex)),
  FiniteDimensional.{0, 0} Complex (Subtype.{1} fun (x : A → Complex) ↦ Membership.mem.{0, 0} W x) →
    Exists.{1} fun (S : Finset.{0} A) ↦
      ∀ (w : A → Complex),
        Membership.mem.{0, 0} W w → (∀ (a : A), Membership.mem.{0, 0} S a → Eq.{1} (w a) 0) → Eq.{1} w 0 := by
  intro A W hW
  classical
  let f : A → Module.Dual Complex W := fun a =>
    (LinearMap.proj (R := Complex) (φ := fun _ : A => Complex) a).comp W.subtype
  have hfg : (Submodule.span Complex (Set.range f)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hsub, heq⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hmem : ∀ φ ∈ s', ∃ a, f a = φ := fun φ h => hsub h
  choose g hg using hmem
  refine ⟨s'.attach.image (fun φ => g φ.1 φ.2), ?_⟩
  intro w hw h0
  have hker : Submodule.span Complex (s' : Set (Module.Dual Complex W)) ≤
      LinearMap.ker (Module.Dual.eval Complex W ⟨w, hw⟩) := by
    rw [Submodule.span_le]
    intro φ hφ
    have e := hg φ hφ
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
    rw [← e]
    exact h0 _ (Finset.mem_image.2 ⟨⟨φ, hφ⟩, Finset.mem_attach _ _, rfl⟩)
  funext a
  have ha : f a ∈ Submodule.span Complex (s' : Set (Module.Dual Complex W)) :=
    heq ▸ Submodule.subset_span ⟨a, rfl⟩
  have h1 := hker ha
  rw [LinearMap.mem_ker, Module.Dual.eval_apply] at h1
  exact h1

end Bl.FirstLemmaH
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedFirstBlockRestriction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedFirstBlockRestriction
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceL

theorem slice_typeF {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)) :
    IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W →
    ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)),
      IsOpen (K₁ : Set (GL (Fin r) (Af E))) ∧ FiniteDimensional ℂ W₁ ∧
      ∀ f ∈ typeF K W, ∀ y : GA E s,
        (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₁ W₁ := by
  intro hK hW
  have hcf : cf (r + s) k t = finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) := by
    rw [cf, infGL_comm]
  refine ⟨Slice1.levelOne s K t,
    W.map (LinearMap.funLeft ℂ ℂ fun κ : Kinf E r => Slice1.levK E r s κ * k),
    Slice1.isOpen_levelOne hK t, inferInstance, ?_⟩
  intro f hf y
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have h := Slice1.lev_finGL_right g u y t (Unitary.toUnits k)
    have h' := hf.1 _ (Slice1.mem_levelOne.1 hu)
      (lev (Ad E) r s (g, y) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    rw [← h] at h'
    simpa only [hcf, mul_assoc] using h'
  · refine ⟨_, hf.2 (lev (Ad E) r s (g, y) * finGL E (r + s) t), ?_⟩
    funext κ
    have h := Slice1.lev_infGL_right g (Unitary.toUnits κ) y t (Unitary.toUnits k)
    have e : lev (Cinf E) r s (Unitary.toUnits κ, 1) * Unitary.toUnits k =
        Unitary.toUnits (Slice1.levK E r s κ * k) := by
      rw [map_mul, Slice1.toUnits_levK]
    rw [e] at h
    simp only [LinearMap.funLeft_apply, hcf]
    rw [← h]
    simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceL

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedFirstBlockRestrictionStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typed_first_block_restriction : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K₁ : Set (GL (Fin r) (Af E))) ∧ FiniteDimensional ℂ W₁ ∧ ∀ f ∈ typeF K W, ∀ y : GA E s, (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₁ W₁ := by
  first | exact @GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF | exact GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF | (intros; apply GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDeterminingSet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDeterminingSet
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem exists_finset_separating_points {A : Type} (W : Submodule ℂ (A → ℂ)) :
    FiniteDimensional ℂ W → ∃ S : Finset A, ∀ w ∈ W, (∀ a ∈ S, w a = 0) → w = 0 :=
  _root_.Bl.FirstLemmaH.goal1 W

end GlobalTheory.CompanionTheory.LimV
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDeterminingSetStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_determining_set : ∀ {A : Type} (W : Submodule ℂ (A → ℂ)), FiniteDimensional ℂ W → ∃ S : Finset A, ∀ w ∈ W, (∀ a ∈ S, w a = 0) → w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points | exact GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points | (intros; apply GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedNode
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.FdNode

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s : ℕ}

theorem memInd2_of_mem_indSpan {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  unfold indSpan at h
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => (tens2 U₁ U₂).zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => (tens2 U₁ U₂).add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 _ + y.1 _
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => (tens2 U₁ U₂).smul_mem c (hx.2 k g)⟩
    change c • x.1 _ = c • x.1 _
    rw [hx.1]

def sliceMap (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) :
    Sm E (r + s) →ₗ[ℂ] (GA E r × GA E s → ℂ) where
  toFun φ m := φ.1 (lev (Ad E) r s m * cf (r + s) k t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tensor_le_prodSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    tens2 U₁ U₂ ≤ prodSpan (U₁.map (Sm E r).subtype) (U₂.map (Sm E s).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem fd_inf (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (h : FiniteDimensional ℂ (typed U K W)) :
    FiniteDimensional ℂ ↥(U.map (Sm E N).subtype ⊓ typeF K W) := by
  have hle : U.map (Sm E N).subtype ⊓ typeF K W ≤ (typed U K W).map (Sm E N).subtype := by
    rintro f ⟨⟨φ, hφ, rfl⟩, hf⟩
    exact ⟨φ, ⟨hφ, hf⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end SlopeTestRemainingChoices

theorem finiteDimensional_typed_indSpan : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), (∀ (K : Subgroup (GL (Fin r) (Af E))) (W : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K : Set (GL (Fin r) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₁ K W)) → (∀ (K : Subgroup (GL (Fin s) (Af E))) (W : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K : Set (GL (Fin s) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₂ K W)) → ∀ (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (indSpan U₁ U₂) K W) := by
  intro E _ _ _ r s U₁ U₂ h₁ h₂ K W hK hW
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s K hK
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finite_determining_set W hW
  choose K₁ W₁ oK₁ fW₁ sl₁ using
    fun i : Kinf E (r + s) × GL (Fin (r + s)) (Af E) => GlobalTheory.T.typed_first_block_restriction i.1 i.2 K W hK hW
  choose K₂ W₂ oK₂ fW₂ sl₂ using
    fun i : Kinf E (r + s) × GL (Fin (r + s)) (Af E) => GlobalTheory.T.typed_second_block_restriction i.1 i.2 K W hK hW
  let P : ↥S × ↥T → Submodule ℂ (GA E r × GA E s → ℂ) := fun i =>
    prodSpan (U₁.map (Sm E r).subtype ⊓ typeF (K₁ (i.1.1, i.2.1)) (W₁ (i.1.1, i.2.1)))
      (U₂.map (Sm E s).subtype ⊓ typeF (K₂ (i.1.1, i.2.1)) (W₂ (i.1.1, i.2.1)))
  haveI : ∀ i, FiniteDimensional ℂ (P i) := fun i =>
    GlobalTheory.T.finiteDimensional_prodSpan _ _ (fd_inf _ _ _ (h₁ _ _ (oK₁ _) (fW₁ _))) (fd_inf _ _ _ (h₂ _ _ (oK₂ _) (fW₂ _)))
  have hmem : ∀ (i : ↥S × ↥T) (φ : typed (indSpan U₁ U₂) K W), sliceMap i.1.1 i.2.1 φ.1 ∈ P i := by
    intro i φ
    have hmi := memInd2_of_mem_indSpan φ.2.1
    exact GlobalTheory.T.mem_prodSpan_inf _ _ _ _ _ (tensor_le_prodSpan U₁ U₂ (hmi.2 i.1.1 i.2.1))
      (fun y => sl₁ (i.1.1, i.2.1) _ φ.2.2 y) (fun x => sl₂ (i.1.1, i.2.1) _ φ.2.2 x)
  let Φ : typed (indSpan U₁ U₂) K W →ₗ[ℂ] ∀ i, P i := LinearMap.pi fun i =>
    ((sliceMap i.1.1 i.2.1).comp (Submodule.subtype _)).codRestrict (P i) (hmem i)
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun φ hφ => ?_)
  have hz : ∀ a ∈ S, ∀ t ∈ T, ∀ m, φ.1.1 (lev (Ad E) r s m * cf (r + s) a t) = 0 := by
    intro a ha t ht m
    have e := congrArg Subtype.val (congrFun hφ (⟨a, ha⟩, ⟨t, ht⟩))
    exact congrFun e m
  have hmi := memInd2_of_mem_indSpan φ.2.1
  have hty : φ.1.1 ∈ typeF K W := φ.2.2
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g
  have e : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l =
      unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) * finGL E (r + s) l := by
    simp only [mul_assoc]
  rw [e, hty.1 l hl, hmi.1]
  have hw := hS _ (hty.2 (lev (Ad E) r s m * finGL E (r + s) t)) (fun a ha => by
    have h0 := hz a ha t ht m
    rw [cf, infGL_comm, ← mul_assoc] at h0
    exact h0)
  exact congrFun hw k

end GlobalTheory.CompanionTheory.LimV.FdNode

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedNodeStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_node : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), (∀ (K : Subgroup (GL (Fin r) (Af E))) (W : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K : Set (GL (Fin r) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₁ K W)) → (∀ (K : Subgroup (GL (Fin s) (Af E))) (W : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K : Set (GL (Fin s) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₂ K W)) → ∀ (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (indSpan U₁ U₂) K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan | exact GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan | (intros; apply GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan <;> assumption)
end
end
