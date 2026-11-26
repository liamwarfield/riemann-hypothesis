module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorAnnihilated
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffRightConvolutionAlongOneParameterProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffRightConvolutionAlongOneParameterProduct
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.ConvSmooth

section Param

variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

theorem hasFDerivAt_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W} (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C) (ball_mem_nhds t₀ one_pos)
    (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)

theorem contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W} (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩

end Param

section Group

open GlobalTheory.AdelicU GlobalTheory.Orb NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {u : P → GAd σ J} {ν μ : Measure (GAd σ J)} {φ : GAd σ J → ℂ} {K : Set (GAd σ J)}


omit [NumberField E] [FiniteDimensional ℝ P] in
theorem infFin_mul_smoothFam (hu : IsSmoothRealFam u) {a : GInf σ J → ℂ} {b : GFin σ J → ℂ}
    {Φ : (∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) → ℂ} (e : ∀ x, a x = Φ (infCoord σ J x))
    (z : GAd σ J) (t : P) :
    infFin σ J a b (z * u t) = Φ (fun w τ i j => ∑ k, infCoord σ J (projInf σ J z) w τ i k *
      archMat σ J τ (projArch σ J w (u t)) k j) * b (projFin σ J z) := by
  simp only [infFin, map_mul, hu.1, mul_one, e, infCoord_mul]

theorem integrable_conj_mul_of_mem (hφ : Integrable φ ν) {h : GAd σ J → ℂ}
    (hh : h ∈ CcAd σ J) (g : GAd σ J) (x : GAd σ J) :
    Integrable (fun y => conj (h (y⁻¹ * g * x)) * φ y) ν := by
  obtain ⟨h1, h2⟩ := continuous_of_mem_ccAd hh
  obtain ⟨M, hM⟩ := h1.bounded_above_of_compact_support h2
  refine Integrable.mono' (hφ.norm.const_mul M) ?_ (.of_forall fun y => ?_)
  · have hc : Continuous fun y : GAd σ J => conj (h (y⁻¹ * g * x)) :=
      Complex.continuous_conj.comp (h1.comp ((continuous_inv.mul continuous_const).mul continuous_const))
    exact hc.aestronglyMeasurable.mul hφ.1
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

theorem contDiff_integral_of_compact (hu : IsSmoothRealFam u) (hKc : IsCompact K) (hK : ∀ᵐ y ∂ν, y ∈ K)
    (hφ : Integrable φ ν) {h : GAd σ J → ℂ} (hh : h ∈ CcAd σ J) (g : GAd σ J) :
    ContDiff ℝ ∞ fun t => ∫ y, conj (h (y⁻¹ * g * u t)) * φ y ∂ν := by
  induction hh using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨-, Φ, hΦ, e⟩, b, hb, rfl⟩ := hf
    have hcc : Continuous fun y : GAd σ J => infCoord σ J (projInf σ J (y⁻¹ * g)) :=
      (continuous_infCoord σ J).comp ((continuous_projInf σ J).comp (continuous_inv.mul continuous_const))
    obtain ⟨M, hM⟩ := hb.1.continuous.bounded_above_of_compact_support hb.2
    have hφ' : Integrable (fun y => conj (b (projFin σ J (y⁻¹ * g))) * φ y) ν := by
      refine Integrable.mono' (hφ.norm.const_mul M) ?_ (.of_forall fun y => ?_)
      · exact (Complex.continuous_conj.comp (hb.1.continuous.comp ((continuous_projFin σ J).comp
          (continuous_inv.mul continuous_const)))).aestronglyMeasurable.mul hφ.1
      · rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    have hΘ : ContDiff ℝ ∞ fun p : P × (∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) =>
        conj (Φ (fun w τ i j => ∑ k, p.2 w τ i k * archMat σ J τ (projArch σ J w (u p.1)) k j)) :=
      Complex.conjCLE.contDiff.comp (hΦ.comp (contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i =>
        contDiff_pi.2 fun j => ContDiff.sum fun k _ =>
          (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_snd w) τ) i) k).mul
            ((hu.2 w τ k j).comp contDiff_fst)))
    have key := GlobalTheory.ConvSmooth.contDiff_integral_smul_param hcc.aestronglyMeasurable (hKc.image hcc)
      (hK.mono fun y hy => mem_image_of_mem _ hy) hφ' hΘ
    convert key using 1
    funext t
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [infFin_mul_smoothFam hu e, map_mul]
    ring
  | zero => simp only [Pi.zero_apply, map_zero, zero_mul, integral_zero]; exact contDiff_const
  | add f f' hf hf' h h' =>
    have e : (fun t => ∫ y, conj ((f + f') (y⁻¹ * g * u t)) * φ y ∂ν) =
        fun t => (∫ y, conj (f (y⁻¹ * g * u t)) * φ y ∂ν) + ∫ y, conj (f' (y⁻¹ * g * u t)) * φ y ∂ν :=
      funext fun t => by
        simp only [Pi.add_apply, map_add (f := _), add_mul]
        exact integral_add (integrable_conj_mul_of_mem hφ hf g _) (integrable_conj_mul_of_mem hφ hf' g _)
    rw [e]
    exact h.add h'
  | smul a f _ h =>
    have e : (fun t => ∫ y, conj ((a • f) (y⁻¹ * g * u t)) * φ y ∂ν) =
        fun t => conj a * ∫ y, conj (f (y⁻¹ * g * u t)) * φ y ∂ν :=
      funext fun t => by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        ring
    rw [e]
    exact contDiff_const.mul h

theorem contDiff_integral_conj_mul (hu : IsSmoothRealFam u) (hcu : Continuous u) (hφ : LocallyIntegrable φ μ)
    {h : GAd σ J → ℂ} (hh : h ∈ CcAd σ J) (g : GAd σ J) :
    ContDiff ℝ ∞ fun t => ∫ y, conj (h (y⁻¹ * g * u t)) * φ y ∂μ := by
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  obtain ⟨-, hs⟩ := continuous_of_mem_ccAd hh
  set K := (fun p : P × GAd σ J => g * u p.1 * p.2⁻¹) '' (closedBall t₀ 1 ×ˢ tsupport h) with hKdef
  have hKc : IsCompact K := ((isCompact_closedBall t₀ 1).prod hs.isCompact).image (by fun_prop)
  have key := contDiff_integral_of_compact (ν := μ.restrict K) hu hKc (ae_restrict_mem hKc.measurableSet)
    (hφ.integrableOn_isCompact hKc) hh g
  refine key.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
  have : y⁻¹ * g * u t ∉ tsupport h := fun hm =>
    hy ⟨(t, y⁻¹ * g * u t), ⟨ball_subset_closedBall ht, hm⟩, by simp [mul_assoc]⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end Group

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta NumberField
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem continuous_ofFn_prod {G Q : Type} [Monoid G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace Q]
    {k : ℕ} {v : Fin k → Q → G} (hv : ∀ i, Continuous (v i)) :
    Continuous fun t => (List.ofFn fun i => v i t).prod := by
  induction k with
  | zero => simpa using continuous_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hv 0).mul (ih fun i => hv i.succ)

theorem contDiff_convR_lift_oneP : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g : GA D V, ContDiff ℝ ∞ fun t : Fin k → ℝ => GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  intro D V μ _ _ θ hθ f hf F k τs Xs hX g
  have hu := GlobalTheory.Orb.isSmoothRealFam_prod fun i =>
    (GlobalTheory.Orb.isSmoothRealFam_oneP hθ (hX i)).1.comp (contDiff_apply ℝ (fun _ => ℝ) i)
  have hcu := continuous_ofFn_prod (v := fun i (t : Fin k → ℝ) => oneP θ V (τs i) (Xs i) (t i)) fun i =>
    (GlobalTheory.Orb.isSmoothRealFam_oneP hθ (hX i)).2.1.comp (continuous_apply i)
  have hφ : LocallyIntegrable (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) μ :=
    locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have key := contDiff_integral_conj_mul hu hcu hφ (GlobalTheory.Orb.starFn_mem_ccAd hf) g
  convert key using 1
  funext t
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp [GlobalTheory.AutomorphicL2Unitary.starFn, mul_assoc]

end Record

end GlobalTheory.ConvSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffRightConvolutionAlongOneParameterProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_rightConvolution_along_one_parameter_products : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g : GA D V, ContDiff ℝ ∞ fun t : Fin k → ℝ => GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  first | exact @GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP | exact GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP | (intros; apply GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtremalVectorValuesLoweringAndTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtremalVectorValuesLoweringAndTorus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExtFock

section Perm

variable {n : ℕ} (π : Fin n → Fin n)

theorem submatrix_eq_mul (P : Matrix (Fin n) (Fin n) ℂ) :
    P.submatrix id π = P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply]

variable {π}

theorem perm_mul_self (hπ : ∀ a, π (π a) = a) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
  simp [mul_ite, Finset.sum_ite_eq', hπ]

theorem perm_single_perm (hπ : ∀ a, π (π a) = a) (c d : Fin n) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * Matrix.single c d 1 * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π =
      Matrix.single (π c) (π d) 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, Matrix.single_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, hπ]
  have key : ∀ x y, x = π y ↔ π x = y := fun x y => ⟨fun h => by rw [h, hπ], fun h => by rw [← h, hπ]⟩
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [key d b]
  by_cases h1 : π c = a
  · subst h1; simp
  · have h2 : ¬ a = π c := fun h => h1 h.symm
    simp [h1, h2]

theorem perm_diag_perm (hπ : ∀ a, π (π a) = a) (t : Fin n → ℂ) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * Matrix.diagonal t * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π =
      Matrix.diagonal (fun a => t (π a)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, Matrix.diagonal_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, hπ]
  split_ifs with h
  · rw [h]
  · rfl

theorem conj_submatrix (hπ : ∀ a, π (π a) = a) (P X : Matrix (Fin n) (Fin n) ℂ) :
    P.submatrix id π * X * (P.submatrix id π)⁻¹ =
      P * ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * X * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π) * P⁻¹ := by
  rw [submatrix_eq_mul π P, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (perm_mul_self hπ)]
  simp only [Matrix.mul_assoc]

end Perm

theorem killPair_rev {n p : ℕ} (hpn : p ≤ n) {c d : Fin n} (h : d < c) :
    GlobalTheory.HolRead.KillPair (fun a : Fin n => decide ((a : ℕ) < p)) (GlobalTheory.AdSpan.revPos p c) (GlobalTheory.AdSpan.revPos p d) := by
  have hdc : (d : ℕ) < c := h
  unfold GlobalTheory.HolRead.KillPair GlobalTheory.AdSpan.revPos
  by_cases hc : (c : ℕ) < p <;> by_cases hd : (d : ℕ) < p
  · left
    simp only [dif_pos (And.intro hc hpn), dif_pos (And.intro hd hpn), Fin.lt_def]
    refine ⟨by simp; omega, by simp; omega, by omega⟩
  · omega
  · right; right
    simp only [dif_neg (fun h' : (c : ℕ) < p ∧ p ≤ n => hc h'.1), dif_pos (And.intro hd hpn), Fin.lt_def]
    refine ⟨by simp; omega, by omega⟩
  · right; left
    simp only [dif_neg (fun h' : (c : ℕ) < p ∧ p ≤ n => hc h'.1), dif_neg (fun h' : (d : ℕ) < p ∧ p ≤ n => hd h'.1), Fin.lt_def]
    refine ⟨by simp; omega, by simp; omega, hdc⟩

end GlobalTheory.ExtFock

namespace GlobalTheory.ExtFock


open GlobalTheory.HolRead.ExtKill in
set_option maxHeartbeats 4000000 in
theorem ext_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) (p : ℕ), (∀ τ, ((Wc D i).sig (tauE D τ)).1 = p) → p ≤ (Wc D i).rank → IsExtVec (R.MW i (sg0 D A)) (fun ρ => u ρ) → ∀ T ∈ R.Wall i (sg0 D A), LowKilled R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) (T fun ρ => u ρ) ∧ ∀ (ρ : D.what₂.Tau) (s : Fin (Wc D i).rank → ℝ), ∃ l : ℂ, R.ωP i t (1, torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) = l • R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w) ∧ ∀ g, T (fun ρ => u ρ) (g * torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) = l * T (fun ρ => u ρ) g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hP i t u w p hp hpn hext T hT
  have hTm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  have hεd : ∀ ρ, (R.MW i (sg0 D A)).ε ρ = fun a : Fin (Wc D i).rank => decide ((a : ℕ) < p) := by
    intro ρ; funext a; rw [hM.order i ρ a, hp ρ]
  have hε : ∀ ρ (a : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε ρ a = if (a : ℕ) < p then true else !true := by
    intro ρ a; rw [hεd ρ]; by_cases h : (a : ℕ) < p <;> simp [h]
  let V := Wc D i
  let M := R.MW i (sg0 D A)
  let v : M.Vec := fun ρ => u ρ
  have KW (ρ : D.what₂.Tau) :
      (∀ a b, GlobalTheory.HolRead.KillPair (M.ε ρ) a b →
        RderC R.θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (T v) = 0) ∧
      ∀ (s : Fin V.rank → ℝ) (g : GA D V),
        T v (g * atTau R.θ V ρ ((M.fr ρ)⁻¹ *
          Matrix.diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) * M.fr ρ)) =
        Complex.exp (((∑ a, extWt M ρ a * s a : ℝ) : ℂ) * Complex.I) * T v g := by
    have hFrame := M.fr_unit ρ
    have hGram := M.fr_gram ρ
    obtain ⟨-, hlow, hwt⟩ := hext ρ
    have hlow' : (v ρ : M.H ρ) ∈ Formalism.MainNotions.S.lowKSub (M.ε ρ) (M.lam ρ) (M.σ ρ) := hlow
    refine ⟨fun a b hab => ?_, fun s g => ?_⟩
    · have hs := GlobalTheory.HolRead.MultDer.smoothVec_of_mem M ρ (v ρ).2
      have hd (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V ρ) :
          ∃ z : M.sm ρ, (z : M.H ρ) = dRep (M.rep ρ) X (v ρ : M.H ρ) ∧
            Rder R.θ V ρ X (T v) = T (Function.update v ρ z) := by
        have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V ρ
        have hU := GlobalTheory.SmoothAutCheck.gramAt_unit V ρ
        have hRep := (GlobalTheory.HolDict.ModelRep.model_rep D V _ M ρ).2.1
        obtain ⟨hOrbit, -, hDeriv⟩ :=
          GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint _ _ _ _ hH hU hRep _ hs
        refine ⟨⟨_, Submodule.subset_span (hDeriv X hX).1⟩, rfl, ?_⟩
        funext x
        obtain ⟨ℓ, hℓ, hℓT⟩ := hTm.cont ρ v x
        have hDerivAt :=
          GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit _ _ _ _ hH hU hRep _ hs ℓ hℓ X hX
        rw [← hℓT]
        have e : (fun t : ℝ => T v (x * oneP R.θ V ρ X t)) =
            fun t : ℝ => ℓ (M.rep ρ (NormedSpace.exp (t • X)) (v ρ : M.H ρ)) := by
          funext t
          have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t
          let z : M.sm ρ := ⟨_, Submodule.subset_span (hOrbit _ hg)⟩
          have hEquiv := congrFun (hTm.equiv ρ _ hg v z rfl) x
          exact ((hℓT z).trans hEquiv).symm
        show deriv (fun t : ℝ => T v (x * oneP R.θ V ρ X t)) 0 = _
        rw [e]
        exact hDerivAt.deriv
      have hs' := smoothVec_conj (σ := M.σ ρ) hFrame hGram hs
      set Z := (M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ with hZ
      obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V ρ Z
      have hXY := GlobalTheory.SmoothAutCheck.parts_sum V ρ Z
      unfold RderC
      generalize (1 / 2 : ℂ) • (Z + conjAt V ρ Z) = X at hX hXY ⊢
      generalize (1 / (2 * Complex.I)) • (Z - conjAt V ρ Z) = Y at hY hXY ⊢
      obtain ⟨z, hz, ez⟩ := hd X hX
      obtain ⟨z', hz', ez'⟩ := hd Y hY
      have hX' := lie_conj hFrame hGram hX
      have hY' := lie_conj hFrame hGram hY
      have hE : M.fr ρ * X * (M.fr ρ)⁻¹ + Complex.I • (M.fr ρ * Y * (M.fr ρ)⁻¹) =
          Matrix.single a b 1 := by
        rw [← conj_cancel hFrame (Matrix.single a b 1), ← hZ, ← hXY]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      have key : dRep (M.σ ρ) (M.fr ρ * X * (M.fr ρ)⁻¹) (v ρ : M.H ρ) +
          Complex.I • dRep (M.σ ρ) (M.fr ρ * Y * (M.fr ρ)⁻¹) (v ρ : M.H ρ) = 0 := by
        rcases hab with h | h | h
        · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _
            (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inl h) _ hX' _ hY' hE
        · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _
            (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inr h) _ hX' _ hY' hE
        · exact GlobalTheory.T.lowestKType_killed_by_negative_noncompact_roots _ _ _ _ _ p true
            (hε ρ) (M.enum ρ).1 (M.ds ρ) _ hlow' hs' a b h.1 h.2 _ hX' _ hY' hE
      have h0 : z + Complex.I • z' = 0 := by
        apply Subtype.ext
        show (z : M.H ρ) + Complex.I • (z' : M.H ρ) = 0
        rw [hz, hz', ← key, ← dRep_conj hFrame, ← dRep_conj hFrame]
        rfl
      have hSmul : T (Function.update v ρ (Complex.I • z')) =
          Complex.I • T (Function.update v ρ z') := by
        simpa only [RingHom.id_apply] using T.map_update_smul v ρ Complex.I z'
      rw [ez, ez', ← hSmul, ← T.map_update_add v ρ z (Complex.I • z'), h0, T.map_update_zero]
    · have hK := Formalism.IndefR.FWT.diag_mem (ε := M.ε ρ) s
      have hg := GlobalTheory.HolDict.ModelRep.conj_mem_inv hFrame hGram (kset_uj hK)
      have h := hTm.equiv ρ _ hg v
        (Complex.exp (((∑ a, extWt M ρ a * s a : ℝ) : ℂ) * Complex.I) • v ρ) (by
          unfold DSModel.rep
          rw [conj_cancel hFrame, hwt s hK]
          rfl)
      rw [T.map_update_smul, Function.update_eq_self] at h
      exact (congrFun h g).symm
  have hπ : ∀ a : Fin (Wc D i).rank, revPos p (revPos p a) = a := revPos_revPos p
  have hinv : ∀ ρ, ((onb (R.MW i (sg0 D A)) ρ))⁻¹ = (R.MW i (sg0 D A)).fr ρ := fun ρ =>
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))
  refine ⟨⟨(hTm.aut _).smooth, fun ρ c d hdc => ?_⟩, fun ρ s => ?_⟩
  · have e : revB p (onb (R.MW i (sg0 D A))) ρ * Matrix.single c d 1 * (revB p (onb (R.MW i (sg0 D A))) ρ)⁻¹ =
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ * Matrix.single (revPos p c) (revPos p d) 1 * (R.MW i (sg0 D A)).fr ρ := by
      show (onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p) * _ * ((onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p))⁻¹ = _
      rw [conj_submatrix hπ, perm_single_perm hπ, hinv]
      rfl
    rw [e]
    apply (KW ρ).1
    rw [hεd ρ]
    exact killPair_rev hpn hdc
  · set l : ℂ := Complex.exp (((∑ a, extWt (R.MW i (sg0 D A)) ρ a * s (revPos p a) : ℝ) : ℂ) * Complex.I) with hl
    have e : revB p (onb (R.MW i (sg0 D A))) ρ * Matrix.diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) *
        (revB p (onb (R.MW i (sg0 D A))) ρ)⁻¹ =
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((s (revPos p a) : ℂ) * Complex.I)) *
          (R.MW i (sg0 D A)).fr ρ := by
      show (onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p) * _ * ((onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p))⁻¹ = _
      rw [conj_submatrix hπ, perm_diag_perm hπ, hinv]
      rfl
    have htor : torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s =
        atTau R.θ (Wc D i) ρ (((R.MW i (sg0 D A)).fr ρ)⁻¹ *
          Matrix.diagonal (fun a => Complex.exp ((s (revPos p a) : ℂ) * Complex.I)) * (R.MW i (sg0 D A)).fr ρ) := by
      unfold torAt; rw [e]
    refine ⟨l, ?_, fun g => ?_⟩
    · have hK := Formalism.IndefR.FWT.diag_mem (ε := (R.MW i (sg0 D A)).ε ρ) (fun a => s (revPos p a))
      obtain ⟨-, -, hwt⟩ := hext ρ
      have h2 := (hP.ioP i t).2.1 ρ _ hK u (l • u ρ) (by
        show l • (((u ρ : (R.MW i (sg0 D A)).sm ρ)) : (R.MW i (sg0 D A)).H ρ) = _
        rw [hwt _ hK]) w
      rw [htor, h2, MultilinearMap.map_update_smul, Function.update_eq_self, map_smul, LinearMap.smul_apply]
      unfold RealDat.ptP
      exact map_smul _ _ _
    · rw [htor]
      exact (KW ρ).2 _ g

end GlobalTheory.ExtFock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtremalVectorValuesLoweringAndTorusStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremalVector_values_lowering_and_torus : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) (p : ℕ), (∀ τ, ((Wc D i).sig (tauE D τ)).1 = p) → p ≤ (Wc D i).rank → IsExtVec (R.MW i (sg0 D A)) (fun ρ => u ρ) → ∀ T ∈ R.Wall i (sg0 D A), LowKilled R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) (T fun ρ => u ρ) ∧ ∀ (ρ : D.what₂.Tau) (s : Fin (Wc D i).rank → ℝ), ∃ l : ℂ, R.ωP i t (1, torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) = l • R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w) ∧ ∀ g, T (fun ρ => u ρ) (g * torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) = l * T (fun ρ => u ρ) g := by
  first | exact @GlobalTheory.ExtFock.ext_values | exact GlobalTheory.ExtFock.ext_values | (intros; apply GlobalTheory.ExtFock.ext_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleLinearHomFramedPointEigenbases
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleLinearHomFramedPointEigenbases
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckePointLawRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem existsUnique_dual_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {T : Type} [CommRing T]
    (s : Sp (DualNumber T) ⟶ Y) (x₀ : Sp T ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom T T T).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber T) ⟶ X,
      spMap (TrivSqZeroExt.fstHom T T T).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber T) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom T T T).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber T, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  exact GlobalTheory.existsUnique_lift_of_etale_of_surjective f π hπ hnil x₀ s h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

variable {T : Type} [CommRing T]

abbrev epsBase (T : Type) [CommRing T] : Sp (DualNumber T) ⟶ Sp T := spMap (algebraMap T (DualNumber T))

abbrev epsZero (T : Type) [CommRing T] : Sp T ⟶ Sp (DualNumber T) := spMap (TrivSqZeroExt.fstHom T T T).toRingHom

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epsZero_base : epsZero T ≫ epsBase T = 𝟙 _ := by
  rw [spMap_spMap]
  exact (congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id _)

theorem eps_base (a : T) : spMap (epsMul a) ≫ epsBase T = epsBase T := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsZero_eps (a : T) : epsZero T ≫ spMap (epsMul a) = epsZero T := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  simp [epsMul]

theorem eps_comm (a b : T) : spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsMul a) := by
  rw [spMap_spMap, spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, mul_left_comm]

theorem eps_cancel {a b : T} (h : a * b = 1) : spMap (epsMul a) ≫ spMap (epsMul b) = 𝟙 _ := by
  have : (epsMul a).comp (epsMul b) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsMul, ← _root_.mul_assoc, h]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  exact Spec.map_id _

abbrev zeroAt (x : Sp T ⟶ Xo.X) : (Over.mk x : Over Xo.X) ⟶ tEps x := sec' x (epsZero T) epsZero_base

abbrev scaleAt (x : Sp T ⟶ Xo.X) (a : T) : tEps x ⟶ tEps x := res x (spMap (epsMul a)) (eps_base a)

theorem zeroAt_scaleAt (x : Sp T ⟶ Xo.X) (a : T) : zeroAt x ≫ scaleAt x a = zeroAt x :=
  Over.OverMorphism.ext (epsZero_eps a)

theorem scaleAt_comm (x : Sp T ⟶ Xo.X) (a b : T) : scaleAt x a ≫ scaleAt x b = scaleAt x b ≫ scaleAt x a :=
  Over.OverMorphism.ext (eps_comm a b)

theorem isTanAt_iff {x : Sp T ⟶ Xo.X} (a : tEps x ⟶ Xo.univ.t.G) : IsTanAt x a.left ↔ zeroAt x ≫ a = 1 :=
  ⟨fun h => Over.OverMorphism.ext h.2, fun h => ⟨Over.w a, congrArg (·.left) h⟩⟩

theorem isEigAt_iff {c : Coeff l} [Algebra c.F T] {x : Sp T ⟶ Xo.X} (τ : E →+* ℂ) (a : tEps x ⟶ Xo.univ.t.G) :
    IsEigAt c τ a.left ↔ ∀ r : 𝓞 E, a ≫ Xo.univ.t.act.act r = scaleAt x (algebraMap c.F T (embK c τ r)) ≫ a :=
  forall_congr' fun _ => ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩

theorem isCombAt_iff {x : Sp T ⟶ Xo.X} {m : ℕ} (a : Fin m → (tEps x ⟶ Xo.univ.t.G)) (cf : Fin m → T)
    (b : tEps x ⟶ Xo.univ.t.G) :
    IsCombAt x (fun i => (a i).left) cf b.left ↔ (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod = b := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain rfl : u = fun i => scaleAt x (cf i) ≫ a i := funext fun i => Over.OverMorphism.ext (hu i)
    exact Over.OverMorphism.ext h
  · intro h
    exact ⟨_, fun _ => rfl, congrArg (·.left) h⟩

variable {x x' : Sp T ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'}

def tanMap (h : IsLinHom Ψ) : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun a => Over.homMk (push Ψ (epsBase T) a) (push_hom h.1 _ a)) fun a b =>
    Over.OverMorphism.ext (h.2.1 _ _ a b _ _ rfl rfl).symm

theorem tanMap_left (h : IsLinHom Ψ) (a : tEps x ⟶ Xo.univ.t.G) : (tanMap h a).left = push Ψ (epsBase T) a := rfl

theorem tanMap_scale (h : IsLinHom Ψ) (s : T) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (scaleAt x s ≫ a) = scaleAt x' s ≫ tanMap h a :=
  Over.OverMorphism.ext (push_res Ψ _ _ a)

theorem tanMap_act (h : IsLinHom Ψ) (r : 𝓞 E) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (a ≫ Xo.univ.t.act.act r) = tanMap h a ≫ Xo.univ.t.act.act r := by
  refine Over.OverMorphism.ext ?_
  have e : toFib x (epsBase T) (a ≫ Xo.univ.t.act.act r) =
      toFib x (epsBase T) a ≫ (Over.mk x ◁ Xo.univ.t.act.act r).left := by
    rw [toFib, toFib, ← Over.comp_left, lift_whiskerLeft]
  rw [Over.comp_left, tanMap_left, tanMap_left, push, push, e, Category.assoc, reassoc_of% (h.2.2 r),
    ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  simp only [Category.assoc]

theorem sends_one (h : IsLinHom Ψ) : Sends Ψ 1 1 := by
  obtain ⟨f, hf, -⟩ := exists_pointHom h
  simpa using hf 1

theorem tanMap_zero (h : IsLinHom Ψ) {a : tEps x ⟶ Xo.univ.t.G} (ha : zeroAt x ≫ a = 1) :
    zeroAt x' ≫ tanMap h a = 1 :=
  Over.OverMorphism.ext ((sends_sec'_iff h.1 (epsZero T) epsZero_base a 1).1 (by rw [ha]; exact sends_one h))

theorem existsUnique_tanMap (h : IsLinHom Ψ) [Etale Ψ] {w : tEps x' ⟶ Xo.univ.t.G} (hw : zeroAt x' ≫ w = 1) :
    ∃! a : tEps x ⟶ Xo.univ.t.G, zeroAt x ≫ a = 1 ∧ tanMap h a = w := by
  have e₀ : ∀ (y : Sp T ⟶ Xo.X) (a : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ a = 1 ↔
      epsZero T ≫ toFib y (epsBase T) a = (lift (𝟙 (Over.mk y)) (1 : Over.mk y ⟶ Xo.univ.t.G)).left := fun y a => by
    rw [← lift_sec' y _ epsZero_base]
    refine ⟨fun e => by rw [← e], fun e => Over.OverMorphism.ext ?_⟩
    rw [← lift_l_snd (𝟙 (Over.mk y)) (_ ≫ a), e, lift_l_snd]
  have e₁ : ∀ a : tEps x ⟶ Xo.univ.t.G, tanMap h a = w ↔ toFib x (epsBase T) a ≫ Ψ = toFib x' (epsBase T) w :=
    fun a => by
      refine ⟨fun e => gx_ext ?_ ?_, fun e => Over.OverMorphism.ext ?_⟩
      · rw [Category.assoc, h.1, toFib_fst, toFib_fst]
      · rw [toFib_snd, ← e, tanMap_left, push, Category.assoc]
      · rw [tanMap_left, push, reassoc_of% e, toFib_snd]
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift Ψ (toFib x' (epsBase T) w)
    (lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ Xo.univ.t.G)).left ((sends_one h).trans ((e₀ x' w).1 hw).symm)
  have hv : v ≫ (fst (Over.mk x) Xo.univ.t.G).left = epsBase T := by rw [← h.1, reassoc_of% h₂, toFib_fst]
  let a : tEps x ⟶ Xo.univ.t.G := Over.homMk (v ≫ (snd (Over.mk x) Xo.univ.t.G).left) (by
    rw [Category.assoc, snd_hom, reassoc_of% hv]; rfl)
  have ha : toFib x (epsBase T) a = v := gx_ext (by rw [toFib_fst, hv]) (by rw [toFib_snd]; rfl)
  refine ⟨a, ⟨(e₀ x a).2 (by rw [ha, h₁]), (e₁ a).2 (by rw [ha, h₂])⟩, fun b hb => Over.OverMorphism.ext ?_⟩
  rw [← toFib_snd x _ b, hu _ ⟨(e₀ x b).1 hb.1, (e₁ b).1 hb.2⟩]
  rfl

theorem exists_basis_image {c : Coeff l} [Algebra c.F T] (h : IsLinHom Ψ) [Etale Ψ] {p : ℕ} {q : T}
    (hq : q * p = 1) (τ : E →+* ℂ) {m : ℕ} (u : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left))
    (tan : ∀ i, IsTanAt x (u i)) (eig : ∀ i, IsEigAt c τ (u i))
    (basis : ∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin m → T, IsCombAt x u a w) :
    ∃ u' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left), (∀ i, IsLieImg p Ψ (u i) (u' i)) ∧
      (∀ i, IsEigAt c τ (u' i)) ∧ ∀ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin m → T, IsCombAt x' u' a w := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → (tEps x ⟶ Xo.univ.t.G), u = fun i => (a i).left :=
    ⟨fun i => Over.homMk (u i) (tan i).1, rfl⟩
  have c₁ : ∀ y : Sp T ⟶ Xo.X, scaleAt y q ≫ scaleAt y p = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel hq)
  have c₂ : ∀ y : Sp T ⟶ Xo.X, scaleAt y p ≫ scaleAt y q = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel ((mul_comm _ _).trans hq))
  let L : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' q ≫ tanMap h b) fun b b' => by rw [map_mul, MonObj.comp_mul]
  have hL : ∀ b, L b = scaleAt x' q ≫ tanMap h b := fun _ => rfl
  have zs : ∀ (y : Sp T ⟶ Xo.X) (s : T) (b : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ b = 1 →
      zeroAt y ≫ scaleAt y s ≫ b = 1 := fun y s b hb => by rw [← Category.assoc, zeroAt_scaleAt, hb]
  have Lz : ∀ b, zeroAt x ≫ b = 1 → zeroAt x' ≫ L b = 1 := fun b hb => zs _ _ _ (tanMap_zero h hb)
  have Ls : ∀ s b, L (scaleAt x s ≫ b) = scaleAt x' s ≫ L b := fun s b => by
    rw [hL, hL, tanMap_scale, ← Category.assoc, scaleAt_comm, Category.assoc]
  have La : ∀ r b, L (b ≫ Xo.univ.t.act.act r) = L b ≫ Xo.univ.t.act.act r := fun r b => by
    rw [hL, hL, tanMap_act, Category.assoc]
  have Li : ∀ b b', zeroAt x ≫ b = 1 → zeroAt x ≫ b' = 1 → L b = L b' → b = b' := fun b b' hb hb' e => by
    have e' := congrArg (scaleAt x' p ≫ ·) e
    simp only [hL, reassoc_of% (c₂ x')] at e'
    exact (existsUnique_tanMap h (tanMap_zero h hb')).unique ⟨hb, e'⟩ ⟨hb', rfl⟩
  have ta : ∀ i, zeroAt x ≫ a i = 1 := fun i => (isTanAt_iff _).1 (tan i)
  refine ⟨fun i => (L (a i)).left, fun i => ⟨tan i, (isTanAt_iff _).2 (Lz _ (ta i)), a i, rfl, ?_⟩,
    fun i => (isEigAt_iff τ _).2 fun r => ?_, fun w hw hw' => ?_⟩
  · exact congrArg (·.left) (show scaleAt x' p ≫ L (a i) = tanMap h (a i) by rw [hL, reassoc_of% (c₂ x')])
  · rw [← La, (isEigAt_iff τ _).1 (eig i), Ls]
  · obtain ⟨w, rfl⟩ : ∃ b : tEps x' ⟶ Xo.univ.t.G, w = b.left := ⟨Over.homMk w hw.1, rfl⟩
    obtain ⟨v, ⟨hv, e⟩, -⟩ := existsUnique_tanMap h (zs x' p w ((isTanAt_iff _).1 hw))
    obtain rfl : L v = w := by rw [hL, e, reassoc_of% (c₁ x')]
    have ev : IsEigAt c τ v.left := (isEigAt_iff τ _).2 fun r => Li _ _
      (by have := Xo.univ.t.act.hom r; rw [← Category.assoc, hv, MonObj.one_comp]) (zs _ _ _ hv)
      (by rw [La, Ls, (isEigAt_iff τ _).1 hw'])
    refine (existsUnique_congr fun cf => ?_).1 (basis _ ((isTanAt_iff _).2 hv) ev)
    have e : L (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod =
        (List.ofFn fun i => scaleAt x' (cf i) ≫ L (a i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Ls _ _)
    rw [isCombAt_iff, isCombAt_iff, ← e]
    refine ⟨congrArg L, Li _ _ (LieEtale.comp_listProd _ _ fun b hb => ?_) hv⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact zs _ _ _ (ta i)

end GlobalTheory.HeckePointLawRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem GlobalTheory.HeckePointLawRing.exists_frame_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T]
    (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (p : ℕ), p ≠ 0 → IsLinHom Ψ → Etale Ψ →
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left),
      (∀ τ j, IsLieImg p Ψ (y.u τ j) (u τ j)) ∧ (∀ τ j, IsEigAt c τ (u τ j)) ∧
      ∀ τ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt x' (u τ) a w := by
  intro E _ _ _ H Dw l Xo c T _ _ y x' Ψ p hp h het
  have hF : ((p : c.F)) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hq : algebraMap c.F T ((p : c.F)⁻¹) * (p : T) = 1 := by
    rw [← map_natCast (algebraMap c.F T) p, ← map_mul, inv_mul_cancel₀ hF, map_one]
  choose u h₁ h₂ h₃ using fun τ => GlobalTheory.HeckePointLawRing.exists_basis_image (c := c) h hq τ
    (y.u τ) (y.tan τ) (y.eig τ) (y.basis τ)
  exact ⟨u, h₁, h₂, h₃⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleLinearHomFramedPointEigenbasesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_linear_hom_framed_point_eigenbases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (p : ℕ), p ≠ 0 → IsLinHom Ψ → Etale Ψ → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left), (∀ τ j, IsLieImg p Ψ (y.u τ j) (u τ j)) ∧ (∀ τ j, IsEigAt c τ (u τ j)) ∧ ∀ τ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt x' (u τ) a w := by
  first | exact @GlobalTheory.HeckePointLawRing.exists_frame_image | exact GlobalTheory.HeckePointLawRing.exists_frame_image | (intros; apply GlobalTheory.HeckePointLawRing.exists_frame_image <;> assumption)
end
end
