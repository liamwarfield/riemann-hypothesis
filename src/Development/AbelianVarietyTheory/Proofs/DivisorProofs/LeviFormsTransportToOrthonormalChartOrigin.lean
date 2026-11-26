module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOrigin
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviWeightChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nmat_hasDerivAt (X : Data E r) {f : ℂ → V (nd X)} {f' : V (nd X)} {t : ℂ}
    (hf : HasDerivAt f f' t) (τ : X.Ψ) (a c : Fin r) :
    HasDerivAt (fun s => nmat X (f s) τ a c) (nmat X f' τ a c - if a = c then 1 else 0) t := by
  unfold nmat
  by_cases h : c < a
  · simp only [h, dif_pos, h.ne', if_false, sub_zero]
    exact
      ((PiLp.proj 2 (fun _ : Fin (nd X) => ℂ) ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).hasFDerivAt).comp_hasDerivAt t hf
  · simp only [h, dif_neg, not_false_eq_true, sub_self]
    exact hasDerivAt_const _ _

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a c : Fin r) :
    nmat X 0 τ a c = if a = c then 1 else 0 := by
  have := congrFun (congrFun (IW.nmat_zero X τ) a) c
  simpa [mat, Matrix.one_apply] using this

theorem levi_transport_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  intro E _ _ _ r X x0 x1 b z ho hz hb hxb ξ
  have hz1 : (0 : V (nd X)) ∈ OmF X x1 := IW.zero_mem_OmF X x1 ho
  have hxb' : cpt X x0 z = rmul (cpt X x1 0) b := by rw [IW.cpt_zero]; exact hxb
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 hz1 b hb
  rw [← hxb'] at h0
  have hcd : Differentiable ℂ (cpt X x0) := IW.cpt_diff X x0
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hbz : bf z = b := h0.2.2
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  set v : V (nd X) := WithLp.toLp 2 ξ with hv
  have hγ : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hγU : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ U := by
    have h := (hγ.continuousAt)
    simp only [ContinuousAt, zero_smul, add_zero] at h
    exact h (hU.mem_nhds hzU)
  have hbfD : HasDerivAt (fun t : ℂ => bf (z + t • v)) (fderiv ℂ bf z v) 0 :=
    (hbf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hΦD : HasDerivAt (fun t : ℂ => Φ (z + t • v)) (fderiv ℂ Φ z v) 0 :=
    (hΦ.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hbfE : ∀ τ a c, HasDerivAt (fun t : ℂ => bf (z + t • v) τ a c) (fderiv ℂ bf z v τ a c) 0 :=
    fun τ a c => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hbfD τ) a) c
  refine ⟨fun k => (fderiv ℂ Φ z v).ofLp k, fun la => ?_, fderiv ℂ bf z v, ?_, ?_⟩
  · have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
      classical
      intro w hw
      unfold bchar
      refine DifferentiableAt.differentiableWithinAt ?_
      refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
        fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
        fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
      have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
        differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
      have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
        differentiableAt_zpow.2
          (Or.inl (GlobalTheory.LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
      exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
    have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
      (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
    have hne : bchar la (bf z) ≠ 0 := IW.bchar_ne_zero X (hsplit _ hz h0.1).2.1 _
    have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      rw [← GlobalTheory.LeviTransfer.metric_rmul normFactor_rightBorel_holds X la h1 h2, ← h3]
    have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
      rw [hΦz]
      exact (IW.phla_cpt_cdAt X x1 hz1 la).of_le HE.two_le_inf
    have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
      hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
    have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
      (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
    have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
    have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
    rw [hΦz] at hc
    unfold leviM
    rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
      HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
    exact congrArg Complex.re hc
  · intro τ a c hca
    have hev : (fun t : ℂ => bf (z + t • v) τ a c) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hγU] with t ht
      exact ((hsplit _ ht.1 ht.2).2.1 τ).2 a c hca
    exact (hbfE τ a c).unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev)
  · intro τ
    ext a c
    have hL : HasDerivAt (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c)
        (∑ k, x0 τ a k * (nmat X v τ k c - if k = c then 1 else 0)) 0 :=
      HasDerivAt.fun_sum fun k _ => (nmat_hasDerivAt X hγ τ k c).const_mul _
    have hR : HasDerivAt (fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c)
        (∑ k, ((∑ l, x1 τ a l * (nmat X (fderiv ℂ Φ z v) τ l k - if l = k then 1 else 0)) * bf (z + (0:ℂ) • v) τ k c
          + (∑ l, x1 τ a l * nmat X (Φ (z + (0:ℂ) • v)) τ l k) * fderiv ℂ bf z v τ k c)) 0 :=
      HasDerivAt.fun_sum fun k _ =>
        (HasDerivAt.fun_sum fun l _ => (nmat_hasDerivAt X hΦD τ l k).const_mul _).fun_mul (hbfE τ k c)
    have hev : (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c) =ᶠ[𝓝 0]
        fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c := by
      filter_upwards [hγU] with t ht
      have e0 : cpt X x0 (z + t • v) = rmul (cpt X x1 (Φ (z + t • v))) (bf (z + t • v)) :=
        (hsplit _ ht.1 ht.2).2.2
      have e := congrFun (congrFun (congrFun e0 τ) a) c
      simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at e
      exact e
    have heq := hL.unique (hR.congr_of_eventuallyEq hev)
    simp only [zero_smul, add_zero, hΦz, hbz, nmat_zero_apply] at heq
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, mat, Matrix.of_apply,
      WithLp.toLp_ofLp]
    rw [heq]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

end GlobalTheory.LeviWeightChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOriginStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviForms_transport_to_orthonormal_chart_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  first | exact @GlobalTheory.LeviWeightChart.levi_transport_origin | exact GlobalTheory.LeviWeightChart.levi_transport_origin | (intros; apply GlobalTheory.LeviWeightChart.levi_transport_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeStableIffPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeStableIffPrincipalCongruence
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapCong

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} {O : Subring L} {x : GL (Fin n) L}
    (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem pullLat_stable_iff_cong : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → u = 1 + algebraMap K.O B.A t * B.g → γ ∈ UL n w → ∀ g ∈ UL n w, ((∀ y ∈ pullLat w B ψ g, B.g * y ∈ pullLat w B ψ g) ↔ g⁻¹ * γ * g ∈ congSet w n k) := by
  intro E _ _ _ w hns K e hB k t ht hval B u x n γ ψ hψ hu hγ g hg
  obtain ⟨hsemi, hmul, -⟩ := hψ
  obtain ⟨hBc, hBint, hBval, -⟩ := hB
  have hO : ∀ z : w.adicCompletion E, z ∈ w.adicCompletionIntegers E ↔ Valued.v z ≤ 1 :=
    fun z => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w
  have heO : ∀ c : K.O, e (algebraMap K.O K.E c) ∈ w.adicCompletionIntegers E :=
    fun c => (hO _).2 ((hBint _).1 ⟨c, rfl⟩)
  have hcjO : ∀ z ∈ w.adicCompletionIntegers E, cj w z ∈ w.adicCompletionIntegers E := by
    intro z hz
    obtain ⟨o, ho⟩ := (hBint (e.symm z)).2 (by rw [e.apply_symm_apply]; exact (hO z).1 hz)
    obtain ⟨o', ho'⟩ := K.c_int o
    have h2 : cj w z = e (algebraMap K.O K.E o') := by
      rw [← ho', ho, hBc, e.apply_symm_apply]
    rw [h2]; exact heO o'
  obtain ⟨et, het⟩ : ∃ et, e (algebraMap K.O K.E t) = et := ⟨_, rfl⟩
  have het0 : et ≠ 0 := by
    rw [← het]; intro h0
    apply ht.1
    have h1 : algebraMap K.O K.E t = 0 := e.injective (h0.trans (map_zero e).symm)
    exact IsFractionRing.injective K.O K.E (h1.trans (map_zero _).symm)
  have hvet : Valued.v et = WithZero.exp (-(k : ℤ)) := by
    have h1 := hBval (algebraMap K.O K.E t)
    rw [hval, het] at h1
    have hv0 : Valued.v et ≠ 0 := (Valuation.ne_zero_iff _).2 het0
    unfold ordL at h1
    rw [dite_eq_right hv0] at h1
    rw [← WithZero.coe_unzero hv0, WithZero.exp]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  have hkey : ∀ y, ψ (B.g * y) = et⁻¹ • (γ.val *ᵥ ψ y - ψ y) := by
    intro y
    have h1 := hmul y
    rw [hu, add_mul, one_mul, mul_assoc, map_add (f := _), IsScalarTower.algebraMap_apply K.O K.E B.A, ← Algebra.smul_def,
      hsemi, het] at h1
    rw [← h1, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ het0, one_smul]
  have hmem : ∀ (h : GLw n w) y, y ∈ pullLat w B ψ h ↔
      ∀ i, ((h⁻¹ : GLw n w).val *ᵥ ψ y) i ∈ w.adicCompletionIntegers E := by
    intro h y
    constructor
    · intro hy i
      have h1 : ((h⁻¹ : GLw n w).val *ᵥ ψ ((1 : K.O) • y)) i ∈ w.adicCompletionIntegers E := hy 1 i
      rwa [one_smul] at h1
    · intro hy c i
      show ((h⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ _
      rw [← IsScalarTower.algebraMap_smul K.E c y, hsemi, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_mem (heO c) (hy i)
  have hgg : (g⁻¹ * γ * g : GLw n w).val * (g⁻¹ : GLw n w).val = (g⁻¹ : GLw n w).val * γ.val := by
    rw [← Units.val_mul, mul_inv_cancel_right, Units.val_mul]
  have hG : ∀ y, (g⁻¹ : GLw n w).val *ᵥ ψ (B.g * y) =
      et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ y)) := by
    intro y
    rw [hkey, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec (ψ y) ((g⁻¹ * γ * g : GLw n w).val), hgg]
  have hinvg : ∀ v : Fin n → w.adicCompletion E, (g⁻¹ : GLw n w).val *ᵥ (g.val *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hP : (∀ y ∈ pullLat w B ψ g, B.g * y ∈ pullLat w B ψ g) ↔
      ∀ v : Fin n → w.adicCompletion E, (∀ i, v i ∈ w.adicCompletionIntegers E) →
        ∀ i, (et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ v)) i ∈ w.adicCompletionIntegers E := by
    constructor
    · intro H v hv i
      have hy : ψ.symm (g.val *ᵥ v) ∈ pullLat w B ψ g := by
        rw [hmem]; intro j; rw [ψ.apply_symm_apply, hinvg]; exact hv j
      have h1 := (hmem g _).1 (H _ hy) i
      rwa [hG, ψ.apply_symm_apply, hinvg] at h1
    · intro H y hy
      rw [hmem] at hy ⊢
      intro i; rw [hG]; exact H _ hy i
  have hent : ∀ z, et⁻¹ * z ∈ w.adicCompletionIntegers E ↔ Valued.v z ≤ WithZero.exp (-(k : ℤ)) := by
    intro z
    rw [hO, map_mul, map_inv₀, hvet]
    exact inv_mul_le_one₀ (WithZero.exp_pos)
  have hPQ : (∀ v : Fin n → w.adicCompletion E, (∀ i, v i ∈ w.adicCompletionIntegers E) →
        ∀ i, (et⁻¹ • (((g⁻¹ * γ * g : GLw n w).val - 1) *ᵥ v)) i ∈ w.adicCompletionIntegers E) ↔
      ∀ i j, Valued.v (((g⁻¹ * γ * g : GLw n w).val - 1) i j) ≤ WithZero.exp (-(k : ℤ)) := by
    constructor
    · intro H i j
      have h1 := H (Pi.single j 1) (fun l => by
        rw [Pi.single_apply]; split_ifs
        · exact one_mem _
        · exact zero_mem _) i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at h1
      change et⁻¹ * ((g⁻¹ * γ * g : GLw n w).val - 1) i j ∈ _ at h1
      rwa [hent] at h1
    · intro H v hv i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      rw [← mul_assoc]
      exact mul_mem ((hent _).2 (H i j)) (hv j)
  rw [hP, hPQ]
  constructor
  · intro H
    refine ⟨?_, fun i j => by simpa [Matrix.sub_apply] using H i j⟩
    have hγ' : g⁻¹ * γ * g ∈ UL n w := mul_mem (mul_mem (inv_mem hg) hγ) hg
    unfold UL at hγ'
    rw [if_neg hns] at hγ'
    have hU : cT (cj w) (g⁻¹ * γ * g : GLw n w).val * 1 * (g⁻¹ * γ * g : GLw n w).val = 1 := hγ'
    rw [Matrix.mul_one] at hU
    have hinv : ((g⁻¹ * γ * g)⁻¹ : GLw n w).val = cT (cj w) (g⁻¹ * γ * g : GLw n w).val :=
      Units.inv_eq_of_mul_eq_one_left hU
    have hint : ∀ i j, (g⁻¹ * γ * g : GLw n w).val i j ∈ w.adicCompletionIntegers E := by
      intro i j
      have h1 : (g⁻¹ * γ * g : GLw n w).val i j =
          ((g⁻¹ * γ * g : GLw n w).val - 1) i j + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
        rw [Matrix.sub_apply, sub_add_cancel]
      rw [h1]
      refine add_mem ((hO _).2 ((H i j).trans ((WithZero.exp_le_exp.2 (by omega)).trans_eq WithZero.exp_zero))) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine mem_GLint_of_entries (fun i j => hint i j) (fun i j => ?_)
    rw [hinv]
    exact hcjO _ (hint j i)
  · intro H i j
    simpa [Matrix.sub_apply] using H.2 i j

end GlobalTheory.KapCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeStableIffPrincipalCongruenceStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_stable_iff_principalCongruence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → u = 1 + algebraMap K.O B.A t * B.g → γ ∈ UL n w → ∀ g ∈ UL n w, ((∀ y ∈ pullLat w B ψ g, B.g * y ∈ pullLat w B ψ g) ↔ g⁻¹ * γ * g ∈ congSet w n k) := by
  first | exact @GlobalTheory.KapCong.pullLat_stable_iff_cong | exact GlobalTheory.KapCong.pullLat_stable_iff_cong | (intros; apply GlobalTheory.KapCong.pullLat_stable_iff_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbIntAdSpanEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralZeroOfDerivativeAlongConjCurve
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

open GlobalTheory.AutomorphicL2Unitary Set

namespace GlobalTheory.Orb

theorem orbInt_comp_conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (dh : Measure H)
    [dh.IsHaarMeasure] [dh.IsMulRightInvariant] (γ : H) (dt : Measure (cent γ)) [dt.IsHaarMeasure]
    [dt.IsMulRightInvariant] (g : H) (f : H → ℂ) :
    orbInt dh γ dt (f ∘ conjEquiv g) = orbInt dh γ dt f := by
  let r : Quot (cent γ) ≃ᵐ Quot (cent γ) :=
    { toFun := rmul _ g⁻¹
      invFun := rmul _ g
      left_inv := fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]
      right_inv := fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one]
      measurable_toFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable
      measurable_invFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable }
  have hr : MeasurePreserving r (quotMeas _ dt dh) (quotMeas _ dt dh) :=
    measurePreserving_rmul_quotMeas (isClosed_cent γ) g⁻¹
  have h3 : descend (cent γ) (conjFn γ (f ∘ conjEquiv g)) = descend (cent γ) (conjFn γ f) ∘ r := funext fun q => by
    conv_rhs => rw [← Quotient.out_eq q]
    refine Eq.trans ?_ ((leftInv_conjFn le_rfl f).descend_mk (q.out * g⁻¹)).symm
    exact congrArg f (show g * _ * g⁻¹ = _ by group)
  rw [orbInt, quotInt, h3]
  exact hr.integral_comp' _

theorem orbitalIntegral_zero_of_derivative_along_conj_curve {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H) (hs : IsProperOrbit (cent s) s) (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H) (hc : Continuous c) (f f' : H → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f') (hf'c : HasCompactSupport f') (hd : ∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) : HasOrbInt μ s dt f' 0 := by
  have hO := hs.hasOrbInt (dh := μ) (dt := dt) hf' hf'c
  refine ⟨hO.1, ?_⟩
  change orbInt μ s dt f' = 0
  set ν := quotMeas (cent s) dt μ
  have hcf : ∀ (φ : H → ℂ) (g : H), Continuous φ → Continuous (conjFn s (φ ∘ conjEquiv g)) := fun φ g hφ =>
    hφ.comp ((conjEquiv g).continuous.comp (by fun_prop : Continuous fun x : H => x⁻¹ * s * x))
  have hmeas : ∀ (φ : H → ℂ) (g : H), Continuous φ →
      AEStronglyMeasurable (descend (cent s) (conjFn s (φ ∘ conjEquiv g))) ν := fun φ g hφ =>
    (measurable_descend (leftInv_conjFn le_rfl _) (hcf φ g hφ).measurable).aestronglyMeasurable
  let F : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f ∘ conjEquiv (c v)⁻¹))
  let F' : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f' ∘ conjEquiv (c v)⁻¹))
  have hconst : ∀ v, ∫ q, F v q ∂ν = orbInt μ s dt f := fun v =>
    orbInt_comp_conjEquiv μ s dt (c v)⁻¹ f

  obtain ⟨M, hM⟩ := hf'.bounded_above_of_compact_support hf'c
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  set K : Set H := (fun p : ℝ × H => c p.1 * p.2 * (c p.1)⁻¹) '' (Icc (-1) 1 ×ˢ tsupport f')
  have hK : IsCompact K := (isCompact_Icc.prod hf'c).image (by fun_prop)
  obtain ⟨χ, hχ1, -, hχc, hχI⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let χC : H → ℂ := fun x => ((χ x : ℝ) : ℂ)
  have hχC : Continuous χC := by fun_prop
  have hχCc : HasCompactSupport χC := HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hχc Complex.ofReal_zero
  have hχO := hs.hasOrbInt (dh := μ) (dt := dt) hχC hχCc
  let bound : Quot (cent s) → ℝ := fun q => M * ‖descend (cent s) (conjFn s χC) q‖
  have hbound : Integrable bound ν := hχO.1.norm.const_mul M
  have hb : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, ‖F' v q‖ ≤ bound q := by
    intro q v hv
    change ‖f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹)‖ ≤ M * ‖χC (q.out⁻¹ * s * q.out)‖
    rw [inv_inv]
    set y := (c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v
    by_cases hy : y ∈ tsupport f'
    · have hx : q.out⁻¹ * s * q.out ∈ K := ⟨(v, y), ⟨hv, hy⟩, by simp only [y]; group⟩
      have : χC (q.out⁻¹ * s * q.out) = 1 := by simp [χC, hχ1 hx]
      rw [this, norm_one, mul_one]
      exact hM y
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  have hderiv : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun w => F w q) (F' v q) v := by
    intro q v _
    have e1 : (fun w => F w q) = fun w => f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * c w) := funext fun w => by
      change f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * (c w)⁻¹⁻¹) = _
      rw [inv_inv]
    have e2 : F' v q = f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v) := by
      change f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹) = _
      rw [inv_inv]
    rw [e1, e2]
    exact hd _ v
  have hF0 : Integrable (F 0) ν :=
    (hs.hasOrbInt (dh := μ) (dt := dt) (f := f ∘ conjEquiv (c 0)⁻¹) (hf.comp (conjEquiv _).continuous)
      (hfc.comp_homeomorph (conjEquiv (c 0)⁻¹).toHomeomorph)).1
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (s := Icc (-1 : ℝ) 1) (bound := bound) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun v => hmeas f _ hf) hF0 (hmeas f' _ hf')
    (ae_of_all _ hb) hbound (ae_of_all _ hderiv)
  have h0 : HasDerivAt (fun v => ∫ q, F v q ∂ν) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  have := h0.unique hmain.2
  rw [← orbInt_comp_conjEquiv μ s dt (c 0)⁻¹ f']
  exact this.symm

theorem hasOrbInt_zero_of_hasDerivAt_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsProperOrbit (cent s) s → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H), Continuous c → ∀ (f f' : H → ℂ), Continuous f → HasCompactSupport f → Continuous f' → HasCompactSupport f' → (∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) → HasOrbInt μ s dt f' 0 :=
  fun _ _ _ _ _ _ _ _ _ μ _ _ s hs dt _ _ c hc f f' hf hfc hf' hf'c hd =>
    orbitalIntegral_zero_of_derivative_along_conj_curve μ s hs dt c hc f f' hf hfc hf' hf'c hd

end GlobalTheory.Orb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGContinuousInv
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem expG_continuous_inv : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z →
    Continuous (fun t : ℝ => expG ε Z t) ∧
      ∀ t : ℝ, toM (expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  refine ⟨(Formalism.REAL.group_exponential_facts n ε Z hZ).2.2.1, fun t => ?_⟩
  have hmul : toM (expG ε Z t) * NormedSpace.exp (-((t : ℂ) • Z)) = 1 := by
    rw [Formalism.REAL.toM_expG ε Z t hZ]
    have h := Formalism.REAL.one_parameter_subgroup_holds n Z t (-t)
    have e : ((-t : ℝ) : ℂ) • Z = -((t : ℂ) • Z) := by push_cast; rw [neg_smul]
    rw [e, add_neg_cancel] at h
    simpa using h.symm
  exact Units.inv_eq_of_mul_eq_one_right hmul

end GlobalTheory
end

open MeasureTheory GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM expG inG)

namespace GlobalTheory.PsCo.Pc1

theorem orbInt_adSpan_eq_zero : GlobalTheory.PsCo.Pc1.StOrbAd := by
  intro n ε μ _ s hs dt _ _ φ hφ
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant n ε μ
  have hp := isProperOrbit_realUJ hs
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hφ
    have hZ' : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
    obtain ⟨hc, hinv⟩ := GlobalTheory.expG_continuous_inv n ε Z hZ'
    obtain ⟨hsh, hd⟩ := GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan n ε Z H P hZ hH
    have hb : bas ε H P ∈ ShapeM ε P.totalDegree := Submodule.subset_span ⟨H, P, hH, le_rfl, rfl⟩
    obtain ⟨-, -, h1, h2⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hb
    obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hsh
    refine hasOrbInt_zero_of_hasDerivAt_conj (UJ ε) μ s hp dt (fun t => expG ε Z t) hc _ _ h1 h2 h3 h4 fun g u => ?_
    have e : ∀ v : ℝ, toM ((expG ε Z v)⁻¹ * g * expG ε Z v) =
        NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z) := fun v => by
      rw [← hinv v, ← Formalism.REAL.toM_expG ε Z v hZ']
      rfl
    simp only [e]
    exact hd (toM g) u
  | zero =>
    have h := (hp.hasOrbInt (dh := μ) (dt := dt) (f := fun _ => (0 : ℂ)) continuous_const HasCompactSupport.zero).smul 0
    rw [zero_mul, zero_smul] at h
    exact h
  | add φ ψ _ _ h1 h2 =>
    have h := h1.add h2
    rw [add_zero] at h
    exact h
  | smul a φ _ h1 =>
    have h := h1.smul a
    rw [mul_zero] at h
    exact h

end GlobalTheory.PsCo.Pc1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDimLocalModelPrimePlacesAlongParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDimLocalModelPrimePlacesAlongParameters
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.LocModelTwo

variable {L : Type} [Field L] {cL : ℂ →+* L}

def primeOf (P : Place cL) (Q : Subring L) (hP : P.Contains Q) : Ideal Q :=
  Ideal.comap ((Q.subtype).codRestrict P.ring fun x => hP x x.2) (IsLocalRing.maximalIdeal P.ring)

instance (P : Place cL) (Q : Subring L) (hP : P.Contains Q) : (primeOf P Q hP).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_primeOf {P : Place cL} {Q : Subring L} {hP : P.Contains Q} {x : Q} :
    x ∈ primeOf P Q hP ↔ ¬ IsUnit (⟨x, hP x x.2⟩ : P.ring) := Iff.rfl

theorem isUnit_of_ord_eq_zero (P : Place cL) {y : P.ring} (hy : (y : L) ≠ 0) (h : P.ord y = 0) :
    IsUnit y := by
  have hi : (y : L)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hy)).1 (by rw [P.ord_inv, h]; rfl)
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ hy)⟩

theorem ord_zero (P : Place cL) : P.ord 0 = 0 := by simp [Place.ord]

theorem pos_ord_iff {P : Place cL} {Q : Subring L} (hP : P.Contains Q) {x : Q} (hx : (x : L) ≠ 0) :
    0 < P.ord x ↔ x ∈ primeOf P Q hP := by
  rw [mem_primeOf]
  constructor
  · intro h hu
    have := P.ord_eq_zero hu
    simp only at this
    omega
  · intro h
    have h0 : 0 ≤ P.ord x := (P.ord_nonneg_iff hx).2 (hP x x.2)
    refine lt_of_le_of_ne h0 fun e => h ?_
    exact isUnit_of_ord_eq_zero P (y := ⟨x, hP x x.2⟩) hx e.symm

theorem ring_le {P P' : Place cL} {Q : Subring L} (hP : P.IsPrimeOf Q) (hP' : P'.Contains Q)
    (h : primeOf P' Q hP' ≤ primeOf P Q hP.1) : P.ring ≤ P'.ring := by
  intro f hf
  obtain ⟨a, ha, b, hb, hb0, hob, e⟩ := hP.2 f hf
  have hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1 := by
    rw [mem_primeOf, not_not]
    exact isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob
  have hbP' : (⟨b, hb⟩ : Q) ∉ primeOf P' Q hP' := fun h' => hbP (h h')
  rw [mem_primeOf, not_not] at hbP'
  obtain ⟨v, hv⟩ := hbP'.exists_right_inv
  have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
  have : f = a * v := by
    calc f = f * (b * v) := by rw [hv', mul_one]
      _ = a * v := by rw [← mul_assoc, e]
  rw [this]
  exact mul_mem (hP' a ha) v.2

theorem ringKrullDim_eq_one {P : Place cL} {Q : Subring L} [IsLocalRing Q] (hP : P.IsPrimeOf Q)
    (h : IsLocalRing.maximalIdeal Q ≤ primeOf P Q hP.1) : ringKrullDim Q = 1 := by
  have hle : P.ring.toSubring ≤ Q := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, hob, e⟩ := hP.2 f hf
    have hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1 := by
      rw [mem_primeOf, not_not]
      exact isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob
    have hbQ : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact hbP (h ((IsLocalRing.mem_maximalIdeal _).2 hn))
    obtain ⟨v, hv⟩ := hbQ.exists_right_inv
    have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
    have : f = a * v := by
      calc f = f * (b * v) := by rw [hv', mul_one]
        _ = a * v := by rw [← mul_assoc, e]
    rw [this]
    exact Q.mul_mem ha v.2
  have hQ : Q = P.ring.toSubring := le_antisymm (fun x hx => hP.1 x hx) hle
  exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.subringCongr hQ)).trans
    (IsDiscreteValuationRing.ringKrullDim_eq_one P.ring)

theorem eq_span_of_mem_of_not_mem {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {t u : R} (hm : Ideal.span {t, u} = IsLocalRing.maximalIdeal R) (p : Ideal R) [p.IsPrime]
    (ht : t ∈ p) (hu : u ∉ p) : p = Ideal.span {t} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).2 ht)
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal R)
    (IsNoetherian.noetherian p) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
  intro y hy
  have hym : y ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hy
  rw [← hm, Ideal.mem_span_pair] at hym
  obtain ⟨c, d, e⟩ := hym
  have hdu : d * u ∈ p := by
    have : d * u = y - c * t := by rw [← e]; ring
    rw [this]
    exact p.sub_mem hy (p.mul_mem_left c ht)
  have hd : d ∈ p := ((Ideal.IsPrime.mem_or_mem ‹_› hdu).resolve_right hu)
  rw [← e]
  refine Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self t)) ?_
  have huM : u ∈ IsLocalRing.maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have := Submodule.smul_mem_smul huM hd
  rw [mul_comm]
  exact this

end GlobalTheory.FieldPair.LocModelTwo

namespace GlobalTheory.FieldPair.LocModelTwo

theorem ring_eq_and_ord_eq_zero : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  (∀ P P' : Place cL, P.IsPrimeOf Q → P'.IsPrimeOf Q → 0 < P.ord (t : L) → 0 < P'.ord (t : L) →
    P.ring = P'.ring) ∧
  (∀ P : Place cL, P.IsPrimeOf Q → P.ord (t : L) = 0 ∨ P.ord (u : L) = 0) := by
  intro L _ cL Q hQ t u hm hd
  letI := hQ.isLocalRing
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  have hA : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q,
      ¬ (t ∈ primeOf P Q hP.1 ∧ u ∈ primeOf P Q hP.1) := by
    rintro P hP ⟨ht, hu⟩
    have h1 := ringKrullDim_eq_one hP (by
      rw [← hm]
      exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨ht, Set.singleton_subset_iff.2 hu⟩))
    rw [hd] at h1
    exact absurd h1 (by decide)
  have hB : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q, 0 < P.ord (t : L) →
      primeOf P Q hP.1 = Ideal.span {t} := by
    intro P hP hpos
    have ht0 : (t : L) ≠ 0 := fun e => by rw [e, ord_zero] at hpos; exact lt_irrefl _ hpos
    have ht : t ∈ primeOf P Q hP.1 := (pos_ord_iff hP.1 ht0).1 hpos
    exact eq_span_of_mem_of_not_mem hm _ ht fun hu => hA P hP ⟨ht, hu⟩
  refine ⟨fun P P' hP hP' hPt hP't => ?_, fun P hP => ?_⟩
  · have e := (hB P hP hPt).trans (hB P' hP' hP't).symm
    exact le_antisymm (ring_le hP hP'.1 e.ge) (ring_le hP' hP.1 e.le)
  · by_contra h
    push_neg at h
    have hpos : ∀ x : Q, P.ord (x : L) ≠ 0 → x ∈ primeOf P Q hP.1 := by
      intro x hx
      have hx0 : (x : L) ≠ 0 := fun e => hx (by rw [e, ord_zero])
      exact (pos_ord_iff hP.1 hx0).1
        (lt_of_le_of_ne ((P.ord_nonneg_iff hx0).2 (hP.1 x x.2)) (Ne.symm hx))
    exact hA P hP ⟨hpos t h.1, hpos u h.2⟩

end GlobalTheory.FieldPair.LocModelTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDimLocalModelPrimePlacesAlongParametersStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoDimLocalModel_primePlaces_along_parameters : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  (∀ P P' : Place cL, P.IsPrimeOf Q → P'.IsPrimeOf Q → 0 < P.ord (t : L) → 0 < P'.ord (t : L) →
    P.ring = P'.ring) ∧
  (∀ P : Place cL, P.IsPrimeOf Q → P.ord (t : L) = 0 ∨ P.ord (u : L) = 0) := by
  first | exact @GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero | exact GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero | (intros; apply GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeModuleGeneratorKaehlerWedgeRegularPairCons
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeModuleGeneratorKaehlerWedgeRegularPairCons
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing KaehlerDifferential Module

theorem mem_maximalIdeal_of_mul_add_mul_mem_sq {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {t u : R} (h : Ideal.span {t, u} = maximalIdeal R)
    (hd : ringKrullDim R = 2) {a b : R} (hab : a * t + b * u ∈ maximalIdeal R ^ 2) :
    a ∈ maximalIdeal R := by
  by_contra ha
  have hau : IsUnit a := by simpa [mem_maximalIdeal, mem_nonunits_iff] using ha
  have hu : u ∈ maximalIdeal R := h ▸ Ideal.subset_span (by simp)
  have hle : maximalIdeal R ≤ Ideal.span {u} ⊔ maximalIdeal R ^ 2 := by
    conv_lhs => rw [← h]
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · obtain ⟨c, hc⟩ := hau.exists_left_inv
      have e : x = c * (a * x + b * u) + (-(c * b)) * u := by
        linear_combination (-x) * hc
      rw [e]
      exact add_mem (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hab))
        (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self u)))
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have h1 := spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq (Set.finite_singleton u)
    ((Ideal.span_singleton_le_iff_mem _).2 hu) hle
  rw [Set.ncard_singleton] at h1
  have h2 := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at h2
  have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
  have := h2.trans h3
  norm_num at this

theorem isFreeGen_dForm_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (t u : Q),
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
    ringKrullDim Q = 2 →
    ∃ (m : ℕ) (z : Fin m → Q),
      (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
      IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem)
        (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  intro L _ cL Q hQ t u hspan hdim
  letI := hQ.isLocalRing
  letI : Algebra ℂ Q := (cL.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  haveI : IsRegularLocalRing Q := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q ?_
    rw [hdim, ← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Q) (Set.toFinite ({t, u} : Set Q))
    have h2 : ({t, u} : Set Q).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    exact_mod_cast h1.trans h2
  haveI : Algebra.FormallySmooth ℂ Q := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ Q
  have hs : Function.Surjective (algebraMap Q (ResidueField Q)) := residue_surjective
  haveI : Algebra.EssFiniteType ℂ (ResidueField Q) := .comp ℂ Q _
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := ℂ) hs).mpr
    inferInstance
  have hker : RingHom.ker (algebraMap Q (ResidueField Q)) = maximalIdeal Q := ker_residue
  have htm : t ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have hum : u ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have ht0 : algebraMap Q (ResidueField Q) t = 0 := (residue_eq_zero_iff t).mpr htm
  have hu0 : algebraMap Q (ResidueField Q) u = 0 := (residue_eq_zero_iff u).mpr hum

  obtain ⟨s, hsb⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  haveI := hsb.isAlgebraic_field
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin ℂ (Set.range ((↑) : s → ResidueField Q))) (ResidueField Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨bκ, hbκ⟩ := exists_basis_kaehler_of_algebraicIndependent hsb.1
  haveI : Finite s := Module.Finite.finite_basis bκ
  let e : Fin (Nat.card s) ≃ s := (Finite.equivFin s).symm
  let b' := bκ.reindex e.symm
  have hb' : ∀ i, b' i = D ℂ (ResidueField Q) (e i) := fun i => by
    rw [Basis.reindex_apply, Equiv.symm_symm, hbκ]
  let z : Fin (Nat.card s) → Q := fun i => Function.surjInv hs (e i : ResidueField Q)
  have hz : ∀ i, algebraMap Q (ResidueField Q) (z i) = e i := fun i => Function.surjInv_eq hs _
  refine ⟨Nat.card s, z, fun P hP => ?_, ?_⟩
  · have e1 : algebraMap Q (ResidueField Q) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)
        = MvPolynomial.aeval (fun i => (e i : ResidueField Q)) P := by
      rw [show (fun i => (e i : ResidueField Q)) = algebraMap Q (ResidueField Q) ∘ z from
        funext fun i => (hz i).symm, MvPolynomial.aeval_algebraMap_apply]
      rfl
    refine (residue_ne_zero_iff_isUnit _).mp ?_
    change algebraMap Q (ResidueField Q) _ ≠ 0
    rw [e1]
    exact fun h0 => hP ((algebraicIndependent_iff.1 (hsb.1.comp e e.injective)) P h0)
  · let v : Fin (Nat.card s + 2) → Q := Fin.cons t (Fin.cons u z : Fin (Nat.card s + 1) → Q)
    let w : Fin (Nat.card s + 2) → (ResidueField Q) ⊗[Q] Ω[Q⁄ℂ] := TensorProduct.mk Q (ResidueField Q) Ω[Q⁄ℂ] 1 ∘ fun i => D ℂ Q (v i)
    have hw0 : w 0 = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q t := rfl
    have hw1 : w (Fin.succ 0) = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q u := rfl
    have hwz : ∀ i : Fin (Nat.card s), w i.succ.succ = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (z i) := fun i => rfl
    have hmb : ∀ x : Q, mapBaseChange ℂ Q (ResidueField Q) ((1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x) = D ℂ (ResidueField Q) (algebraMap Q (ResidueField Q) x) :=
      fun x => by rw [mapBaseChange_tmul, one_smul, map_D]
    have hpair : ∀ a b : Q, (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) =
        algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0) := fun a b => by
      rw [hw0, hw1]
      simp only [map_add (f := _), Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul]
      rw [← algebraMap_smul (ResidueField Q) t, ← algebraMap_smul (ResidueField Q) u, ht0, hu0]
      simp only [zero_smul, add_zero, algebraMap_smul]
    have hkc : ∀ x (hx : x ∈ RingHom.ker (algebraMap Q (ResidueField Q))),
        kerCotangentToTensor ℂ Q (ResidueField Q) ((RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨x, hx⟩) =
          (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x := fun x hx => kerCotangentToTensor_toCotangent _ _ _ _

    have hsp : Submodule.span (ResidueField Q) (Set.range w) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      let c := b'.repr (mapBaseChange ℂ Q (ResidueField Q) y)
      have hy0 : mapBaseChange ℂ Q (ResidueField Q) (y - ∑ i, c i • w i.succ.succ) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum, sub_eq_zero]
        conv_lhs => rw [← b'.sum_repr (mapBaseChange ℂ Q (ResidueField Q) y)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hwz, hmb, hz, hb']
      obtain ⟨c', hc'⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ Q (ResidueField Q) hs _).mp hy0
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c'
      have hx' := hx
      rw [hker, ← hspan, Ideal.mem_span_pair] at hx'
      obtain ⟨a, b, rfl⟩ := hx'
      rw [hkc, hpair] at hc'
      have hy : y = (algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0)) + ∑ i, c i • w i.succ.succ := by
        rw [hc', sub_add_cancel]
      rw [hy]
      refine add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.succ 0, rfl⟩)))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

    have hli : LinearIndependent (ResidueField Q) w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hg
      have hφ := congrArg (mapBaseChange ℂ Q (ResidueField Q)) hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul, map_zero] at hφ
      rw [hw0, hmb, ht0, Derivation.map_zero, smul_zero, zero_add] at hφ
      rw [hw1, hmb, hu0, Derivation.map_zero, smul_zero, zero_add] at hφ
      simp only [hwz, hmb, hz, ← hb'] at hφ
      have hrest : ∀ i : Fin (Nat.card s), g i.succ.succ = 0 :=
        Fintype.linearIndependent_iff.mp b'.linearIndependent (fun i => g i.succ.succ) hφ
      simp only [hrest, zero_smul, Finset.sum_const_zero, add_zero] at hg
      obtain ⟨a, ha⟩ := hs (g 0)
      obtain ⟨b, hb⟩ := hs (g (Fin.succ 0))
      have hg' : (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) = 0 := by
        rw [hpair, ha, hb]
        exact hg
      have hmem : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) := by
        rw [hker]
        exact add_mem (Ideal.mul_mem_left _ _ htm) (Ideal.mul_mem_left _ _ hum)
      have hsq : a * t + b * u ∈ maximalIdeal Q ^ 2 := by
        have h1 : (RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨_, hmem⟩ = 0 :=
          hinj (by rw [hkc, map_zero]; exact hg')
        have h2 : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) ^ 2 :=
          (Ideal.toCotangent_eq_zero _ _).mp h1
        rwa [hker] at h2
      have ham : a ∈ maximalIdeal Q := mem_maximalIdeal_of_mul_add_mul_mem_sq hspan hdim hsq
      have hbm : b ∈ maximalIdeal Q := by
        refine mem_maximalIdeal_of_mul_add_mul_mem_sq (t := u) (u := t) (a := b) (b := a)
          (by rw [Set.pair_comm]; exact hspan) hdim ?_
        rw [add_comm]; exact hsq
      have h0 : g 0 = 0 := by rw [← ha]; exact (residue_eq_zero_iff a).mpr ham
      have h1 : g (Fin.succ 0) = 0 := by rw [← hb]; exact (residue_eq_zero_iff b).mpr hbm
      intro i
      refine Fin.cases h0 (fun j => Fin.cases h1 (fun k => hrest k) j) i
    haveI : Module.FinitePresentation Q Ω[Q⁄ℂ] := Module.finitePresentation_of_finite Q _
    obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := Q) (fun i => D ℂ Q (v i)) hli hsp
      (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal Q).subtype
        Subtype.val_injective)
    exact isFreeGen_dForm v b hb

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeModuleGeneratorKaehlerWedgeRegularPairConsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeModuleGenerator_kaehlerWedge_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∃ (m : ℕ) (z : Fin m → Q),
    (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
    IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  first | exact @GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons | exact GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons | (intros; apply GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons <;> assumption)
end
end
