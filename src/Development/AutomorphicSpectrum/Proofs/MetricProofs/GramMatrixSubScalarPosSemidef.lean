module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.TripleDeriv
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionForm
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramMatrixSubScalarPosSemidef
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XGramGrad
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PositivityTheory.Xgp.gram_grad

theorem inv_entry {k : ℕ} (H : Matrix (Fin k) (Fin k) ℂ) (a : ℝ) (ha : 0 < a) (hH : H.PosDef)
    (h : (H - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef) (p q : Fin k) : ‖H⁻¹ p q‖ ≤ 1 / a := by
  set w : Fin k → ℂ := fun i => H⁻¹ i q with hw
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  have h1 : H *ᵥ w = Pi.single q 1 := by
    ext i
    have := congrFun (congrFun (Matrix.mul_nonsing_inv H hu) i) q
    rw [Matrix.mul_apply] at this
    simp only [mulVec, dotProduct, hw, this, Matrix.one_apply, Pi.single_apply]
  have h2 := h.re_dotProduct_nonneg w
  rw [sub_mulVec, h1, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_single] at h2
  have h3 : star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [h3, smul_eq_mul, ← Complex.ofReal_mul] at h2
  simp only [RCLike.re_to_complex, Complex.sub_re, Complex.ofReal_re, mul_one, Pi.star_apply] at h2
  have h4 : (star (w q)).re ≤ ‖w q‖ := by
    have := Complex.re_le_norm (star (w q))
    rwa [norm_star] at this
  have h5 : ∀ i, ‖w i‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2 := fun i =>
    Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h6 : a * ‖w q‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    have hq : 0 < ‖w q‖ := by
      by_contra h0
      have : ‖w q‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
      rw [this] at hc
      linarith
    nlinarith [h5 q, mul_le_mul_of_nonneg_left (h5 q) ha.le]
  have h7 : (a * ‖w p‖) ^ 2 ≤ 1 := by
    have e1 := mul_le_mul_of_nonneg_left (h5 p) ha.le
    have e2 : a * ‖w p‖ ^ 2 ≤ ‖w q‖ := by linarith
    have e3 := mul_le_mul_of_nonneg_left e2 ha.le
    nlinarith
  have h8 : a * ‖w p‖ ≤ 1 := by
    nlinarith [mul_nonneg ha.le (norm_nonneg (w p))]
  rw [le_div_iff₀ ha]
  show ‖w p‖ * a ≤ 1
  linarith

theorem mul_entry {l m n : ℕ} (A : Matrix (Fin l) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) (α β : ℝ)
    (hα : 0 ≤ α) (hA : ∀ p q, ‖A p q‖ ≤ α) (hB : ∀ p q, ‖B p q‖ ≤ β) (p : Fin l) (q : Fin n) :
    ‖(A * B) p q‖ ≤ m * (α * β) := by
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ j, ‖A p j * B j q‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, α * β := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul (hA p j) (hB j q) (norm_nonneg _) hα
    _ = _ := by simp

theorem triple_entry {n k : ℕ} (U W : Matrix (Fin n) (Fin k) ℂ) (G : Matrix (Fin n) (Fin n) ℂ) (α β γ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hU : ∀ p q, ‖U p q‖ ≤ α) (hG : ∀ p q, ‖G p q‖ ≤ β) (hW : ∀ p q, ‖W p q‖ ≤ γ)
    (p q : Fin k) : ‖(Uᴴ * G * W) p q‖ ≤ n * (n * (α * β) * γ) :=
  mul_entry _ _ _ _ (by positivity)
    (mul_entry _ _ _ _ hα (fun p q => by rw [conjTranspose_apply, norm_star]; exact hU q p) hG) hW p q

end PositivityTheory.Xgp.gram_grad

theorem PositivityTheory.Xgp.t_gram_grad : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a := by
  intro n k E _ _ G V x a M ha hM hG hV hev hpsd bG bV
  by_cases hd : DifferentiableAt ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x
  swap
  · rw [fderiv_zero_of_not_differentiableAt hd, norm_zero]
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  obtain ⟨hGx, hVx⟩ := hev.self_of_nhds
  have hpos : ((V x)ᴴ * G x * V x).PosDef :=
    hGx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff.mpr hVx)
  let G' : Matrix (Fin n) (Fin n) ℂ := fun p q => fderiv ℝ (fun y => G y p q) x v
  let V' : Matrix (Fin n) (Fin k) ℂ := fun p q => fderiv ℝ (fun y => V y p q) x v
  have h1 := PositivityTheory.Xgp.gram_grad.triple_deriv (fun s : ℝ => G (x + s • v)) (fun s : ℝ => V (x + s • v)) G' V' 0
    (fun p q => PositivityTheory.Xgp.gram_grad.line_deriv _ x (hG p q) v)
    (fun p q => PositivityTheory.Xgp.gram_grad.line_deriv _ x (hV p q) v)
  have h2 := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_log_det
    (fun s : ℝ => (V (x + s • v))ᴴ * G (x + s • v) * V (x + s • v)) _ 0 h1 (by simpa using hpos)
  have h3 := (PositivityTheory.Xgp.gram_grad.line_deriv _ x hd v).unique h2
  simp only [zero_smul, add_zero] at h3
  rw [h3]
  have hv := norm_nonneg v
  have bG' : ∀ p q, ‖G' p q‖ ≤ M * ‖v‖ := fun p q =>
    ((fderiv ℝ (fun y => G y p q) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (bG p q).2 hv)
  have bV' : ∀ p q, ‖V' p q‖ ≤ M * ‖v‖ := fun p q =>
    ((fderiv ℝ (fun y => V y p q) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (bV p q).2 hv)
  have b3 : ∀ p q, ‖(V'ᴴ * G x * V x + (V x)ᴴ * G' * V x + (V x)ᴴ * G x * V') p q‖ ≤
      3 * (n : ℝ) ^ 2 * M ^ 3 * ‖v‖ := by
    intro p q
    have t1 := PositivityTheory.Xgp.gram_grad.triple_entry V' (V x) (G x) _ _ _ (by positivity) hM bV'
      (fun p q => (bG p q).1) (fun p q => (bV p q).1) p q
    have t2 := PositivityTheory.Xgp.gram_grad.triple_entry (V x) (V x) G' _ _ _ hM (by positivity)
      (fun p q => (bV p q).1) bG' (fun p q => (bV p q).1) p q
    have t3 := PositivityTheory.Xgp.gram_grad.triple_entry (V x) V' (G x) _ _ _ hM hM
      (fun p q => (bV p q).1) (fun p q => (bG p q).1) bV' p q
    rw [Matrix.add_apply, Matrix.add_apply]
    refine norm_add₃_le.trans ?_
    nlinarith
  have b4 := PositivityTheory.Xgp.gram_grad.mul_entry _ _ _ _ (by positivity)
    (PositivityTheory.Xgp.gram_grad.inv_entry _ a ha hpos hpsd) b3
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => b4 i i).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMobiusTransform
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMobiusTransform
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gram_logDet_fderiv_norm_le : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a :=
  @PositivityTheory.Xgp.t_gram_grad

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMobiusTransformStatement
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_gram_subharmonic : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le | exact GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramMatrixSubScalarPosSemidef
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem gram_grad_scale_arith (D c P Q a : ℝ) (ha : 0 < a) (hP : 0 < P) (hQ : 0 < Q)
    (h : P / Q * D ≤ c * P ^ 3 / a) : D ≤ c * P ^ 2 * Q / a := by
  have h1 : D = Q / P * (P / Q * D) := by field_simp
  have h2 : 0 ≤ Q / P := (div_pos hQ hP).le
  calc D = Q / P * (P / Q * D) := h1
    _ ≤ Q / P * (c * P ^ 3 / a) := mul_le_mul_of_nonneg_left h h2
    _ = c * P ^ 2 * Q / a := by field_simp

theorem gram_grad_comp_smul (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x' : E) (a P t : ℝ)
    (ha : 0 < a) (hP : 0 < P)
    (h1 : ∀ p q, DifferentiableAt ℝ (fun y => G (t • y) p q) x')
    (h2 : ∀ p q, DifferentiableAt ℝ (fun y => V (t • y) p q) x')
    (h3 : ∀ᶠ y in nhds x', (G (t • y)).PosDef ∧ LinearIndependent ℂ (V (t • y))ᵀ)
    (h4 : ((V (t • x'))ᴴ * G (t • x') * V (t • x') -
      (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef)
    (h5 : ∀ p q, ‖G (t • x') p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G (t • y) p q) x'‖ ≤ P)
    (h6 : ∀ p q, ‖V (t • x') p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V (t • y) p q) x'‖ ≤ P) :
    ‖fderiv ℝ (fun y => Real.log ((V (t • y))ᴴ * G (t • y) * V (t • y)).det.re) x'‖ ≤
      3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 3 / a :=
  GlobalTheory.T.log_det_gram_subharmonic n k E (fun u => G (t • u)) (fun u => V (t • u)) x' a P ha hP.le h1 h2 h3 h4 h5 h6

theorem gram_grad_scaled : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a P Q : ℝ), 0 < a → 0 < P → P ≤ Q → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ Q) → (∀ p q, ‖V x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ Q) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 2 * Q / a := by
  intro n k E _ _ G V x a P Q ha hP hPQ hGd hVd hev hH hGb hVb
  have hQ : 0 < Q := lt_of_lt_of_le hP hPQ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = P / Q := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ div_pos hP hQ
  have htne : t ≠ 0 := ht0.ne'
  obtain ⟨x', hx'⟩ : ∃ x' : E, x' = t⁻¹ • x := ⟨_, rfl⟩
  have hcx : t • x' = x := by rw [hx', smul_smul, mul_inv_cancel₀ htne, one_smul]
  have hL : DifferentiableAt ℝ (fun u : E => t • u) x' := (differentiableAt_id).const_smul t
  have hdiff : ∀ f : E → ℂ, DifferentiableAt ℝ f x →
      DifferentiableAt ℝ (fun u => f (t • u)) x' := by
    intro f hf
    have hf' : DifferentiableAt ℝ f (t • x') := by rw [hcx]; exact hf
    exact hf'.comp x' hL
  have hfd : ∀ f : E → ℂ, fderiv ℝ (fun u => f (t • u)) x' = t • fderiv ℝ f x := by
    intro f
    rw [fderiv_comp_smul, hcx]
  have hfdR : ∀ f : E → ℝ, fderiv ℝ (fun u => f (t • u)) x' = t • fderiv ℝ f x := by
    intro f
    rw [fderiv_comp_smul, hcx]
  have hbound : ∀ f : E → ℂ, ‖fderiv ℝ f x‖ ≤ Q →
      ‖fderiv ℝ (fun u => f (t • u)) x'‖ ≤ P := by
    intro f hf
    rw [hfd, norm_smul, Real.norm_of_nonneg ht0.le, ht]
    calc P / Q * ‖fderiv ℝ f x‖ ≤ P / Q * Q := mul_le_mul_of_nonneg_left hf (div_pos hP hQ).le
      _ = P := by field_simp
  have htend : Tendsto (fun u : E => t • u) (nhds x') (nhds x) := by
    have := hL.continuousAt.tendsto
    rwa [hcx] at this
  have key := gram_grad_comp_smul n k E G V x' a P t ha hP
    (fun p q => hdiff (fun y => G y p q) (hGd p q))
    (fun p q => hdiff (fun y => V y p q) (hVd p q))
    (htend.eventually hev)
    (by rw [hcx]; exact hH)
    (fun p q => ⟨by rw [hcx]; exact (hGb p q).1, hbound (fun y => G y p q) (hGb p q).2⟩)
    (fun p q => ⟨by rw [hcx]; exact (hVb p q).1, hbound (fun y => V y p q) (hVb p q).2⟩)
  have hk := hfdR (fun y => Real.log ((V y)ᴴ * G y * V y).det.re)
  rw [hk, norm_smul, Real.norm_of_nonneg ht0.le, ht] at key
  exact gram_grad_scale_arith _ _ P Q a ha hP hQ key

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramMatrixSubScalarPosSemidefStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_sub_scalar_posSemidef : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a P Q : ℝ), 0 < a → 0 < P → P ≤ Q → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ Q) → (∀ p q, ‖V x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ Q) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 2 * Q / a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrthogonalFlagDegreeComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrthogonalFlagDegreeComparison
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.FlagPair

theorem iSup_part_degree_rank {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K}
    {Ψ : Type} [Fintype Ψ] {j k : ℕ} (A : FlagPair E Ψ j k) (h : A.IsOrthFull) :
    E.normDegree (⨆ a, A.part a) =
        ∑ τ, E.normDegree (A.W τ).top + ∑ τ, E.normDegree (A.S τ).top ∧
      E.rank (⨆ a, A.part a) = Module.finrank (𝓞 K) E.carrier := by
  unfold GlobalTheory.CompanionTheory.Ar.FlagPair.IsOrthFull at h
  obtain ⟨hort, hcard⟩ := h
  obtain ⟨hdeg, hrk⟩ := GlobalTheory.T.normalized_degree_orthogonal_sum K E (Ψ ⊕ Ψ) A.part hort
  refine ⟨?_, ?_⟩
  · rw [hdeg, Fintype.sum_sum_type]
    rfl
  · have hW : ∀ τ, E.rank (A.part (Sum.inl τ)) = j := fun τ => by
      show E.rank ((A.W τ).F (Fin.last j)) = j
      rw [(A.W τ).rank (Fin.last j), Fin.val_last]
    have hS : ∀ τ, E.rank (A.part (Sum.inr τ)) = k := fun τ => by
      show E.rank ((A.S τ).F (Fin.last k)) = k
      rw [(A.S τ).rank (Fin.last k), Fin.val_last]
    rw [hrk, Fintype.sum_sum_type, ← hcard]
    simp only [hW, hS, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring

theorem two_sum_neg_degree_W : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ j k), A.IsOrthFull →
    -E.normDegree ⊤ - ∑ τ, A.flatDeg τ ≤ 2 * ∑ τ, -E.normDegree (A.W τ).top ∧
      ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ ⨆ a, A.part a) →
        2 * ∑ τ, -E.normDegree (A.W τ).top ≤
          -E.normDegree ⊤ - ∑ τ, A.flatDeg τ +
            Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  intro K _ _ E Ψ _ j k A h
  obtain ⟨hdeg, hrk⟩ := iSup_part_degree_rank A h
  obtain ⟨hle, hge⟩ := GlobalTheory.T.normalized_degree_full_rank_sublattice K E (⨆ a, A.part a) hrk
  have hflat : ∑ τ, A.flatDeg τ =
      ∑ τ, E.normDegree (A.W τ).top - ∑ τ, E.normDegree (A.S τ).top := by
    simp only [GlobalTheory.CompanionTheory.Ar.FlagPair.flatDeg, Finset.sum_sub_distrib]
  rw [hdeg] at hle
  refine ⟨?_, ?_⟩
  · rw [hflat, Finset.sum_neg_distrib]
    linarith
  · intro d hd hsub
    have hb := hge d hd hsub
    rw [hdeg] at hb
    rw [hflat, Finset.sum_neg_distrib]
    linarith

end GlobalTheory.CompanionTheory.Ar.FlagPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrthogonalFlagDegreeComparisonStatement
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_flag_degree_comparison : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ j k), A.IsOrthFull → -E.normDegree ⊤ - ∑ τ, A.flatDeg τ ≤ 2 * ∑ τ, -E.normDegree (A.W τ).top ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ ⨆ a, A.part a) → 2 * ∑ τ, -E.normDegree (A.W τ).top ≤ -E.normDegree ⊤ - ∑ τ, A.flatDeg τ + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W | exact GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepRowsInverseNonzeroEntry
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepRowsInverseNonzeroEntry
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.UnitComb

theorem coe_minorIJ {L : Type} [Field L] (V : ValuationSubring L) {N : ℕ}
    (h : Matrix (Fin N) (Fin N) V) (I J : Finset (Fin N)) :
    ((minorIJ h I J : V) : L) = minorIJ (h.map V.subtype) I J := by
  unfold minorIJ
  split_ifs with e
  · exact RingHom.map_det V.subtype _
  · rfl

theorem minorIJ_one_diag {R : Type} [CommRing R] {N : ℕ} (J : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) R) J J = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.submatrix_one _ (J.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem exists_isUnit_of_sum {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} (s : Finset ι)
    (f : ι → R) (h : IsUnit (∑ a ∈ s, f a)) : ∃ a ∈ s, IsUnit (f a) := by
  by_contra hc
  push_neg at hc
  have : ∑ a ∈ s, f a ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun a ha => (IsLocalRing.mem_maximalIdeal _).2 (hc a ha)
  exact (IsLocalRing.mem_maximalIdeal _).1 this h

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
    omega

theorem unit_comb : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  intro L _ V N j i H κ _ u u' hj hB hH hdet hinv hu' hu horth
  let Hv : Matrix (Fin N) (Fin N) V := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hHv : Hv.map V.subtype = H := by ext a b; rfl
  let uv : κ → Finset (Fin N) → V := fun m I => ⟨u m I, hu m I⟩
  let uv' : Finset (Fin N) → κ → V := fun I m => ⟨u' I m, hu' I m⟩
  have hdetc : ((Hv.det : V) : L) = H.det := by
    have := RingHom.map_det V.subtype Hv
    rw [RingHom.mapMatrix_apply, hHv] at this
    exact this
  have hunit : IsUnit Hv.det := by
    refine IsUnit.of_mul_eq_one (⟨(H.det)⁻¹, hinv⟩ : V) ?_
    apply Subtype.ext
    change ((Hv.det : V) : L) * (H.det)⁻¹ = 1
    rw [hdetc, mul_inv_cancel₀ hdet]
  have main := GlobalTheory.T.block_diagonal_minor_vanishing V N j i hj
  have hJ := stepCols_ne_empty (j := j) i hj
  have hBv : IsBlockDiag j Hv := fun a b hab => Subtype.ext (hB a b hab)
  have hstep : ∀ I, ¬ IsStepRows N j i I → minorIJ Hv I (stepCols N j i) = 0 := fun I hI =>
    (main.2.1 Hv I hBv hI).resolve_right hJ
  have hsum1 : IsUnit (∑ I', minorIJ Hv⁻¹ (stepCols N j i) I' * minorIJ Hv I' (stepCols N j i)) := by
    rw [← main.1, Matrix.nonsing_inv_mul _ hunit, minorIJ_one_diag]
    exact isUnit_one
  obtain ⟨I₀, -, hI₀⟩ := exists_isUnit_of_sum _ _ hsum1
  have hI₀' : IsUnit (minorIJ Hv I₀ (stepCols N j i)) := isUnit_of_mul_isUnit_right hI₀
  have hI₀s : IsStepRows N j i I₀ := by
    by_contra hc
    rw [hstep I₀ hc] at hI₀'
    exact not_isUnit_zero hI₀'
  have horthV : ∀ I', IsStepRows N j i I' → ∑ m, uv' I₀ m * uv m I' = if I₀ = I' then 1 else 0 := by
    intro I' hI'
    apply Subtype.ext
    have := horth I₀ I' hI₀s hI'
    split_ifs at this ⊢ with e
    · simpa [uv, uv'] using this
    · simpa [uv, uv'] using this
  let w : κ → V := fun m => ∑ I, uv m I * minorIJ Hv I (stepCols N j i)
  have hw : ∑ m, uv' I₀ m * w m = minorIJ Hv I₀ (stepCols N j i) := by
    have e1 : ∑ m, uv' I₀ m * w m =
        ∑ I, (∑ m, uv' I₀ m * uv m I) * minorIJ Hv I (stepCols N j i) := by
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [e1, Finset.sum_eq_single I₀]
    · rw [horthV I₀ hI₀s, if_pos rfl, one_mul]
    · intro b _ hb
      by_cases hs : IsStepRows N j i b
      · rw [horthV b hs, if_neg (Ne.symm hb), zero_mul]
      · rw [hstep b hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [← hw] at hI₀'
  obtain ⟨m, -, hm⟩ := exists_isUnit_of_sum _ _ hI₀'
  have hwm : IsUnit (w m) := isUnit_of_mul_isUnit_right hm
  have hcoe : ((w m : V) : L) = ∑ I, u m I * minorIJ H I (stepCols N j i) := by
    simp only [w, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coe_minorIJ, hHv]
    rfl
  refine ⟨m, ?_, ?_⟩
  · rw [← hcoe]
    intro h0
    exact hwm.ne_zero (Subtype.ext h0)
  · obtain ⟨c, hc⟩ := hwm.exists_right_inv
    have hc' : ((w m : V) : L) * (c : L) = 1 := congrArg Subtype.val hc
    rw [← hcoe, inv_eq_of_mul_eq_one_right hc']
    exact c.2

end GlobalTheory.CompanionTheory.Ar.PB.UnitComb
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepRowsInverseNonzeroEntryStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_rows_inverse_nonzero_entry : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.UnitComb.unit_comb | exact GlobalTheory.CompanionTheory.Ar.PB.UnitComb.unit_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.UnitComb.unit_comb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SingWeightRegFamilyTransport
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.Transport

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isOpen_compl_bdry (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hyt : A.chart j y ∈ (A.chart j).target := (A.chart j).map_source hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : AnalyticAt ℂ (s y ∘ (A.chart j).symm) (A.chart j y) :=
    hs.1 y j (A.chart j y) ⟨hyt, by
      show (A.chart j).symm (A.chart j y) ∈ L.U y
      rw [hsy]; exact L.mem_U y⟩
  have hcy : ContinuousAt (fun z => (s y ∘ (A.chart j).symm) (A.chart j z)) y :=
    ContinuousAt.comp (f := A.chart j) han.continuousAt ((A.chart j).continuousAt hj)
  have hne : (s y ∘ (A.chart j).symm) (A.chart j y) ≠ 0 := by
    show s y ((A.chart j).symm (A.chart j y)) ≠ 0
    rw [hsy]; exact hy
  have h1 : ∀ᶠ z in 𝓝 y, (s y ∘ (A.chart j).symm) (A.chart j z) ≠ 0 := hcy.eventually_ne hne
  filter_upwards [h1, (A.chart j).open_source.mem_nhds hj,
    (L.isOpen_U y).mem_nhds (L.mem_U y)] with z h1 h2 h3
  have h1' : s y z ≠ 0 := by
    have : s y ((A.chart j).symm (A.chart j z)) ≠ 0 := h1
    rwa [(A.chart j).left_inv h2] at this
  intro hz
  have hz' : s z z = 0 := hz
  have hg := hs.2 y z z ⟨h3, L.mem_U z⟩
  rw [hz'] at hg
  simp only [norm_zero, zero_mul] at hg
  have hpos : 0 < ‖s y z‖ * Real.exp (-L.φ y z) :=
    mul_pos (norm_pos_iff.2 h1') (Real.exp_pos _)
  exact hpos.ne' hg

theorem contDiffAt_two {A : FinHolAtlas e X} {U : Set X} {f : X → ℝ} (h : A.SmoothOn U f)
    (hU : IsOpen U) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hyU : (A.chart j).symm y ∈ U) : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y :=
  ((h j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hy, hyU⟩)).of_le
    ENat.LEInfty.out

theorem levi_eq_of_sub_re (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {W : Set X} (hW : IsOpen W) (hyW : (A.chart j).symm y ∈ W)
    {G : X → ℂ} (hG : A.HoloOn W G) {a b : X → ℝ} (hab : ∀ z ∈ W, a z - b z = (G z).re)
    (hb : ContDiffAt ℝ 2 (b ∘ (A.chart j).symm) y) (w : Fin e → ℂ) :
    levi (a ∘ (A.chart j).symm) y w = levi (b ∘ (A.chart j).symm) y w := by
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hyW⟩
  have hre : ContDiffAt ℝ 2 (fun z => ((G ∘ (A.chart j).symm) z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hGa.restrictScalars.contDiffAt
  have hev : (a ∘ (A.chart j).symm) =ᶠ[𝓝 y]
      fun z => (b ∘ (A.chart j).symm) z + 1 * ((G ∘ (A.chart j).symm) z).re := by
    have hmem : ∀ᶠ z in 𝓝 y, (A.chart j).symm z ∈ W :=
      ((A.chart j).continuousAt_symm hy).eventually_mem (hW.mem_nhds hyW)
    filter_upwards [hmem] with z hz
    have := hab _ hz
    simp only [Function.comp]
    linarith
  rw [levi_congr hev, levi_add_smul 1 hb hre, levi_re_analytic hGa]
  ring

theorem exists_re_base {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) {x u : X}
    (hu : u ∈ P.U x) : ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, P.φ x z - P.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G, hG, hW⟩ := hP.2 x u u ⟨hu, P.mem_U u⟩
  refine ⟨W ∩ P.U x ∩ P.U u, (oW.inter (P.isOpen_U x)).inter (P.isOpen_U u),
    ⟨⟨mW, hu⟩, P.mem_U u⟩, G, fun k => (hG k).mono fun y hy => ⟨hy.1, hy.2.1.1⟩, ?_⟩
  rintro z hz
  exact hW z hz

theorem exists_re_change {A : FinHolAtlas e X} {th th' : LocPot X} (hth : IsPotential A th)
    (hsame : SamePot A Set.univ th th') {x u : X} (hu : u ∈ th.U x) :
    ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, th.φ x z - th'.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G₁, h₁, e₁⟩ := exists_re_base hth hu
  obtain ⟨V, oV, mV, G₂, h₂, e₂⟩ := hsame u (Set.mem_univ _)
  refine ⟨W ∩ V, oW.inter oV, ⟨mW, mV⟩, fun z => G₁ z + G₂ z, fun k => ?_, ?_⟩
  · exact ((h₁ k).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rintro z ⟨a, b⟩
    have h1 := e₁ z a
    have h2 := e₂ z b
    simp only [Complex.add_re]
    linarith

theorem isPshOn_transport {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} {th th' : LocPot X}
    {ph : X → ℝ} (hs : IsSection A L s) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hsm : A.SmoothOn (bdry s)ᶜ ph)
    (hpsh : IsPshOn A (bdry s)ᶜ (th' + LocPot.ofFun ph)) :
    IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun ph) := by
  intro x j y hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1
  obtain ⟨W, oW, mW, G, hG, hW⟩ := exists_re_change hth hsame hyx
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨th'.mem_U _, Set.mem_univ _⟩, hyb⟩ w
  have hb : ContDiffAt ℝ 2 ((th' + LocPot.ofFun ph).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    (contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hsm (isOpen_compl_bdry A L s hs) j hyt hyb)
  rw [levi_eq_of_sub_re A j hyt oW mW hG (a := (th + LocPot.ofFun ph).φ x)
    (b := (th' + LocPot.ofFun ph).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := hW z hz
      show th.φ x z + ph z - (th'.φ _ z + ph z) = _
      linarith) hb w]
  exact h0

theorem isPsh_transport {A : FinHolAtlas e X} {Θ th th' : LocPot X} {f : X → ℝ} {c : ℝ}
    (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hf : A.Smooth f)
    (hpsh : IsPsh A (th' + LocPot.ofFun f + Θ.rsmul c)) :
    IsPsh A (th + LocPot.ofFun f + Θ.rsmul c) := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1.1
  have hyΘ : (A.chart j).symm y ∈ Θ.U x := hyU.2
  obtain ⟨W₁, o₁, m₁, G₁, h₁, e₁⟩ := exists_re_change hth hsame hyx
  obtain ⟨W₂, o₂, m₂, G₂, h₂, e₂⟩ := exists_re_base hΘ hyΘ
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨⟨th'.mem_U _, Set.mem_univ _⟩, Θ.mem_U _⟩⟩ w
  have hb : ContDiffAt ℝ 2
      ((th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hf isOpen_univ j hyt (Set.mem_univ _))).add
      (contDiffAt_const.mul (contDiffAt_two (hΘ.1 _) (Θ.isOpen_U _) j hyt (Θ.mem_U _)))
  have hG : A.HoloOn (W₁ ∩ W₂) fun z => G₁ z + (c : ℂ) * G₂ z := fun k =>
    ((h₁ k).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add
      ((analyticOnNhd_const (v := (c : ℂ))).mul ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩))
  rw [levi_eq_of_sub_re A j hyt (o₁.inter o₂) ⟨m₁, m₂⟩ hG
    (a := (th + LocPot.ofFun f + Θ.rsmul c).φ x)
    (b := (th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := e₁ z hz.1
      have h2 := e₂ z hz.2
      show th.φ x z + f z + c * Θ.φ x z -
        (th'.φ _ z + f z + c * Θ.φ _ z) = _
      simp only [Complex.add_re, Complex.re_ofReal_mul]
      rw [← h1, ← h2]
      ring) hb w]
  exact h0

theorem singWeight_regFamily_transport : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (th th' : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ),
    IsPotential A Θ → IsSection A L s → IsPotential A th → IsPotential A th' → SamePot A Set.univ th th' →
    (IsSingWeight A L s th' ph C₅ → IsSingWeight A L s th ph C₅) ∧
      (IsRegFamily A Θ L s th' ph phT C t₀ → IsRegFamily A Θ L s th ph phT C t₀) := by
  intro e X _ A Θ L s th th' ph phT C₅ C t₀ hΘ hs hth hth' hsame
  constructor
  · rintro ⟨_, hsm, hpsh, hb⟩
    exact ⟨hth, hsm, isPshOn_transport hs hth hth' hsame hsm hpsh, hb⟩
  · rintro ⟨h0, h1, hreg⟩
    refine ⟨h0, h1, fun t ht ht' => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hreg t ht ht'
    exact ⟨a1, a2, a3, a4, isPsh_transport hΘ hth hth' hsame a1 a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.Ar.PB.Transport
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagElementaryTwist
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRatFuncEmbeddingMoebius
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.Moebius

private theorem transcendental_of_mul_add_eq_mul {S K : Type*} [CommRing S] [IsDomain S] [Field K]
    [Algebra S K] {x t : K} {p q r : S} (hx : Transcendental S x)
    (hp : algebraMap S K p ≠ 0) (hr : algebraMap S K r ≠ 0)
    (h : t * (algebraMap S K p + x * algebraMap S K q) = x * algebraMap S K r) :
    Transcendental S t := by
  intro ht
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isAlgebraic_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact mul_ne_zero hx0 hr h.symm
  have hE : algebraMap S K r - t * algebraMap S K q ≠ 0 := by
    intro hE
    have h2 : t * algebraMap S K p = x * (algebraMap S K r - t * algebraMap S K q) := by
      linear_combination h
    rw [hE, mul_zero] at h2
    exact mul_ne_zero ht0 hp h2
  have hxe : x = t * algebraMap S K p * (algebraMap S K r - t * algebraMap S K q)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hE]
    linear_combination -h
  apply hx
  rw [hxe]
  exact (ht.mul (isAlgebraic_algebraMap p)).mul
    ((isAlgebraic_algebraMap r).sub (ht.mul (isAlgebraic_algebraMap q))).inv

theorem exists_ratFunc_embedding_moebius : ∀ (Φ S : Type) [Field Φ] [CommRing S] [IsDomain S] [Algebra Φ S] (p q r : S), p ≠ 0 → r ≠ 0 → ∃ θ : RatFunc Φ →+* FractionRing (Polynomial S), (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a))) ∧ algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0 ∧ θ RatFunc.X * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) := by
  intro Φ S _ _ _ _ p q r hp hr
  have hinj : Function.Injective (algebraMap (Polynomial S) (FractionRing (Polynomial S))) :=
    IsFractionRing.injective _ _
  have hs : ∀ s : S, algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C s) =
      algebraMap S (FractionRing (Polynomial S)) s := fun s => by
    rw [IsScalarTower.algebraMap_apply S (Polynomial S) (FractionRing (Polynomial S)),
      Polynomial.algebraMap_eq]
  have hpoly : Polynomial.C p + Polynomial.X * Polynomial.C q ≠ 0 := fun h =>
    hp (by simpa using congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) h)
  have hD : algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0 := by
    rw [← map_mul, ← map_add (f := _)]
    exact (map_ne_zero_iff _ hinj).2 hpoly
  obtain ⟨t, ht⟩ : ∃ t, t = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) /
      (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) := ⟨_, rfl⟩
  have htD : t * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) =
      algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) := by
    rw [ht]
    exact div_mul_cancel₀ _ hD
  have htr : Transcendental S t := by
    refine transcendental_of_mul_add_eq_mul (p := p) (q := q) (r := r)
      ((transcendental_algebraMap_iff hinj).2 (Polynomial.transcendental_X S)) ?_ ?_ ?_
    · rw [← hs]
      exact (map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hp)
    · rw [← hs]
      exact (map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hr)
    · simpa only [hs] using htD
  let φ : Polynomial Φ →+* FractionRing (Polynomial S) :=
    (Polynomial.aeval t).toRingHom.comp (Polynomial.mapRingHom (algebraMap Φ S))
  have hφinj : Function.Injective φ := by
    intro P Q hPQ
    apply Polynomial.map_injective _ (algebraMap Φ S).injective
    exact (transcendental_iff_injective.1 htr) hPQ
  have hφC : ∀ a : Φ, φ (Polynomial.C a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a)) := by
    intro a
    rw [hs]
    simp [φ]
  have hφX : φ Polynomial.X = t := by
    simp [φ]
  refine ⟨RatFunc.liftRingHom φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj),
    fun a => ?_, hD, ?_⟩
  · rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, RatFunc.liftRingHom_algebraMap, hφC]
  · rw [← RatFunc.algebraMap_X, RatFunc.liftRingHom_algebraMap, hφX, htD]

end GlobalTheory.CompanionTheory.Ar.Moebius
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagElementaryTwist
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData

theorem gen_data : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω) (A : Subring Ω) (val : A →+* ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (τ : Ψ) (ca cb : Fin N), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → (∀ τ, IsBlockDiag j (h τ)) → ∃ (L R : Type) (_ : Field L) (_ : CommRing R) (φ : Φ →+* L) (θ : RatFunc Φ →+* L) (U : Ψ → Matrix (Fin N) (Fin N) L) (s : L) (i : R →+* L) (ρ : R →+* ℂ) (cA : A →+* R) (B : Ψ → Matrix (Fin N) (Fin N) R) (sR : R), Function.Injective i ∧ (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = φ a) ∧ (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) ∧ U τ ca ca + s * U τ ca cb ≠ 0 ∧ θ RatFunc.X * (U τ ca ca + s * U τ ca cb) = s * U τ cb cb ∧ (∀ a : A, i (cA a) = φ (algebraMap Ω Φ a)) ∧ (∀ a, ρ (cA a) = val a) ∧ (∀ τ', IsBlockDiag j (B τ')) ∧ (∀ τ', (B τ').map i = ((T τ')⁻¹.map (φ.comp (algebraMap Ω Φ))) * ((g τ').map φ * U τ')) ∧ (∀ τ', (B τ').map ρ = h τ') ∧ i sR = s ∧ ρ sR = t := by
  intro Ω Φ _ _ _ Ψ N j g T A val h t τ ca cb hcb hsum hgb hgen hT hh
  let S₀ := MvPolynomial (UpIdx Ψ N j) Φ
  let P := Polynomial S₀
  let L := FractionRing P
  let Q := MvPolynomial (inertBlockIndex Ψ N j) A
  let R := Polynomial Q
  let aL : P →+* L := algebraMap P L
  let cP : S₀ →+* P := Polynomial.C
  let φ : Φ →+* L := aL.comp (cP.comp (C : Φ →+* S₀))
  let U : Ψ → Matrix (Fin N) (Fin N) L := fun τ' => (genUp Φ N j τ').map (aL.comp cP)
  let s : L := aL Polynomial.X
  let G' : Ψ → Matrix (Fin N) (Fin N) S₀ := fun τ' =>
    ((T τ')⁻¹.map (algebraMap Ω S₀)) * ((g τ').map (C : Φ →+* S₀) * genUp Φ N j τ')
  have indep := @GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp Ω Φ _ _ _ Ψ N j g T hgb hgen hT
  let iS : Q →+* S₀ := eval₂Hom ((algebraMap Ω S₀).comp A.subtype) fun q => G' q.1.1 q.1.2.1 q.1.2.2
  have iS_C : ∀ a : A, iS (C a) = algebraMap Ω S₀ a := fun a => eval₂Hom_C _ _ _
  have iS_X : ∀ q, iS (X q) = G' q.1.1 q.1.2.1 q.1.2.2 := fun q => eval₂Hom_X' _ _ _
  have eS : ∀ r, iS r = aeval (fun q : inertBlockIndex Ψ N j => G' q.1.1 q.1.2.1 q.1.2.2) (MvPolynomial.map A.subtype r) := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => rw [iS_C, map_C, aeval_C]; rfl
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X, iS_X]
  have hiS : Function.Injective iS := fun a b e => by
    refine MvPolynomial.map_injective A.subtype Subtype.val_injective
      ((algebraicIndependent_iff_injective_aeval.1 indep) ?_)
    rw [← eS, ← eS, e]
  let i : R →+* L := aL.comp (Polynomial.mapRingHom iS)
  have hi : Function.Injective i :=
    (IsFractionRing.injective P L).comp (Polynomial.map_injective iS hiS)
  let ρ₀ : Q →+* ℂ := eval₂Hom val fun q => h q.1.1 q.1.2.1 q.1.2.2
  let ρ : R →+* ℂ := Polynomial.eval₂RingHom ρ₀ t
  let cQ : Q →+* R := Polynomial.C
  let cA : A →+* R := cQ.comp (C : A →+* Q)
  let B : Ψ → Matrix (Fin N) (Fin N) R := fun τ' => (genericBlockMatrix A N j τ').map cQ
  have hGb : ∀ τ', IsBlockDiag j (G' τ') := fun τ' =>
    ((((hT τ').1.inv (hT τ').2.isUnit)).map _).mul (((hgb τ').map _).mul (genUp_blockDiag τ'))
  have hiG : ∀ τ', (genericBlockMatrix A N j τ').map iS = G' τ' := generic_block_matrix_map iS hGb fun q => by simp [iS]
  have hρ : ∀ τ', (genericBlockMatrix A N j τ').map ρ₀ = h τ' := generic_block_matrix_map ρ₀ hh fun q => by simp [ρ₀]
  have hdiag : ∀ τ' c, genUp Φ N j τ' c c ≠ 0 := fun τ' c => by
    rw [show genUp Φ N j τ' c c = X ⟨(τ', c, c), le_rfl, Iff.rfl⟩ from
      genUp_apply (⟨(τ', c, c), le_rfl, Iff.rfl⟩ : UpIdx Ψ N j)]
    exact X_ne_zero _
  have hinj : Function.Injective (aL.comp cP) :=
    (IsFractionRing.injective P L).comp Polynomial.C_injective
  have hle : ca ≤ cb := by
    rw [Fin.le_def]; omega
  obtain ⟨θ, hθ₁, hθ₂, hθ₃⟩ := GlobalTheory.CompanionTheory.Ar.Moebius.exists_ratFunc_embedding_moebius Φ S₀ (genUp Φ N j τ ca ca) (genUp Φ N j τ ca cb)
    (genUp Φ N j τ cb cb) (hdiag τ ca) (hdiag τ cb)
  refine ⟨L, R, inferInstance, inferInstance, φ, θ, U, s, i, ρ, cA, B, Polynomial.X, hi, hθ₁,
    fun τ' => ⟨(genUp_blockDiag τ').map _, fun a b hab => ?_, fun c => ?_⟩, hθ₂, hθ₃, fun a => ?_, fun a => ?_,
    fun τ' => (?_ : IsBlockDiag j _), fun τ' => ?_, fun τ' => ?_, ?_, ?_⟩
  · show (aL.comp cP) (genUp Φ N j τ' a b) = 0
    rw [genUp_upper τ' hab, map_zero]
  · show (aL.comp cP) (genUp Φ N j τ' c c) ≠ 0
    exact fun e => hdiag τ' c (hinj (by rw [e, map_zero]))
  · show aL (Polynomial.map iS (Polynomial.C (C a))) = aL (cP (C (algebraMap Ω Φ a)))
    rw [Polynomial.map_C]
    congr 2
    exact (eval₂Hom_C _ _ _).trans (MvPolynomial.algebraMap_apply ..)
  · show Polynomial.eval₂ ρ₀ t (Polynomial.C (C a)) = val a
    rw [Polynomial.eval₂_C]
    exact eval₂Hom_C _ _ _
  · exact (IsBlockDiag.map (fun a b hab => by
      simp [genericBlockMatrix, hab]) cQ)
  · have e1 : (B τ').map i = (G' τ').map (aL.comp cP) := by
      rw [← hiG]
      ext a b
      show aL (Polynomial.map iS (Polynomial.C _)) = aL (cP (iS _))
      rw [Polynomial.map_C]
    rw [e1]
    simp only [G', Matrix.map_mul]
    congr 1
  · rw [← hρ]
    ext a b
    show Polynomial.eval₂ ρ₀ t (Polynomial.C _) = _
    rw [Polynomial.eval₂_C]
    rfl
  · show aL (Polynomial.map iS Polynomial.X) = aL Polynomial.X
    rw [Polynomial.map_X]
  · show Polynomial.eval₂ ρ₀ t Polynomial.X = t
    rw [Polynomial.eval₂_X]

end GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagElementaryTwistStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_elementary_twist : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω) (A : Subring Ω) (val : A →+* ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (τ : Ψ) (ca cb : Fin N), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → (∀ τ, IsBlockDiag j (h τ)) → ∃ (L R : Type) (_ : Field L) (_ : CommRing R) (φ : Φ →+* L) (θ : RatFunc Φ →+* L) (U : Ψ → Matrix (Fin N) (Fin N) L) (s : L) (i : R →+* L) (ρ : R →+* ℂ) (cA : A →+* R) (B : Ψ → Matrix (Fin N) (Fin N) R) (sR : R), Function.Injective i ∧ (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = φ a) ∧ (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) ∧ U τ ca ca + s * U τ ca cb ≠ 0 ∧ θ RatFunc.X * (U τ ca ca + s * U τ ca cb) = s * U τ cb cb ∧ (∀ a : A, i (cA a) = φ (algebraMap Ω Φ a)) ∧ (∀ a, ρ (cA a) = val a) ∧ (∀ τ', IsBlockDiag j (B τ')) ∧ (∀ τ', (B τ').map i = ((T τ')⁻¹.map (φ.comp (algebraMap Ω Φ))) * ((g τ').map φ * U τ')) ∧ (∀ τ', (B τ').map ρ = h τ') ∧ i sR = s ∧ ρ sR = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData.gen_data | exact GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData.gen_data | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData.gen_data <;> assumption)
end
end
