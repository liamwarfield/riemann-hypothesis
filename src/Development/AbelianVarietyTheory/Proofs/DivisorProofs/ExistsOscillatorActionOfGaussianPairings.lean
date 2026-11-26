module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulNormGauLe
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder FourierTransform

namespace GlobalTheory.RealWeil

theorem pow_mul_norm_gau_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℕ) (v : V) :
    ‖v‖ ^ m * ‖gau v‖ ≤ m.factorial * Real.exp 1 := by
  rw [norm_gau]
  have hx0 : 0 ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖ := by
    have := Real.pow_div_factorial_le_exp _ hx0 m
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)] at this
    linarith [mul_comm (Real.exp ‖v‖) (m.factorial : ℝ)]
  have h2 : ‖v‖ + (-(π / 2) * ‖v‖ ^ 2) ≤ 1 := by
    nlinarith [Real.pi_gt_three, sq_nonneg ‖v‖, sq_nonneg (‖v‖ - 1 / 3)]
  calc ‖v‖ ^ m * Real.exp (-(π / 2) * ‖v‖ ^ 2)
      ≤ (m.factorial * Real.exp ‖v‖) * Real.exp (-(π / 2) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = m.factorial * Real.exp (‖v‖ + (-(π / 2) * ‖v‖ ^ 2)) := by rw [Real.exp_add]; ring
    _ ≤ m.factorial * Real.exp 1 := by gcongr

theorem gau_add {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v t : V) :
    gau (v + t) = gau v * gau t * cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) := by
  unfold gau
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h' : ((‖v + t‖ : ℝ) : ℂ) ^ 2 = ((‖v‖ ^ 2 + 2 * ⟪v, t⟫ + ‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← norm_add_sq_real v t]; push_cast; ring
  rw [h']
  push_cast
  ring

theorem contDiff_gau {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    ContDiff ℝ ∞ (gau : V → ℂ) := by
  have e : (gau : V → ℂ) = fun u => cexp (-(π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    simp only [gau]
    push_cast
    rfl
  rw [e]
  have hn : ContDiff ℝ ∞ (fun u : V => ‖u‖ ^ 2) := contDiff_norm_sq ℝ
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hn))

theorem exists_shift_form {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (J : V ≃ₗᵢ[ℝ] V) (v : V) :
    ∃ l : V →L[ℝ] ℂ, ‖l‖ ≤ 2 * π * ‖v‖ ∧
      ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (omJ J v t : ℂ) := by
  let l : V →L[ℝ] ℂ := (-(π : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ v)) -
      ((π : ℂ) * I) • (Complex.ofRealCLM.comp ((innerSL ℝ v).comp (J : V →L[ℝ] V)))
  have hl : ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ) := fun t => by
    simp [l]
  refine ⟨l, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_, fun t => by
    rw [hl t]; rfl⟩
  rw [hl t]
  calc ‖-(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ)‖
      ≤ ‖-(π : ℂ) * (⟪v, t⟫ : ℝ)‖ + ‖(π : ℂ) * I * (⟪v, J t⟫ : ℝ)‖ := norm_sub_le _ _
    _ = π * |⟪v, t⟫| + π * |⟪v, J t⟫| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    _ ≤ π * (‖v‖ * ‖t‖) + π * (‖v‖ * ‖t‖) := by
        gcongr
        · exact abs_real_inner_le_norm _ _
        · exact (abs_real_inner_le_norm v (J t)).trans (by rw [J.norm_map])
    _ = 2 * π * ‖v‖ * ‖t‖ := by ring

theorem decay_gau_smul {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun u => gau u • ρ u f) v‖ ≤ C := by
  set F : V → B := fun u => gau u • ρ u f with hF
  have hFs : ContDiff ℝ ∞ F := contDiff_gau.smul hf
  have hE : ContDiff ℝ ∞ (fun z : ℂ => cexp z) := Complex.contDiff_exp
  have hN : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ * ((k + i).factorial * Real.exp 1), fun v => ?_⟩
  obtain ⟨l, hl, hlt⟩ := exists_shift_form J v
  have hshift : (fun t => F (t + v)) = fun t => (gau v • ρ v) (cexp (l t) • F t) := by
    funext t
    simp only [hF, _root_.smul_apply, map_smul, smul_smul]
    rw [add_comm t v, h.2.1 v t f, smul_smul]
    congr 1
    have key : cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) = cexp (l t) * cexp (π * I * (omJ J v t : ℂ)) := by
      rw [hlt t, ← Complex.exp_add]; congr 1; ring
    rw [gau_add, key]
    ring
  have hG : ContDiff ℝ ∞ (fun t => cexp (l t)) := hE.comp l.contDiff
  have hρ1 : ‖ρ v‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [h.2.2.1, one_mul]
  have hL : ‖(gau v • ρ v).restrictScalars ℝ‖ ≤ ‖gau v‖ := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    calc ‖gau v • ρ v‖ ≤ ‖gau v‖ * ‖ρ v‖ := norm_smul_le _ _
      _ ≤ ‖gau v‖ * 1 := by gcongr
      _ = ‖gau v‖ := mul_one _
  have hexp : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun t => cexp (l t)) 0‖ ≤
      ‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i := by
    intro i
    have e1 : (fun t => cexp (l t)) = (fun z : ℂ => cexp z) ∘ (l : V → ℂ) := rfl
    rw [e1, l.iteratedFDeriv_comp_right hE 0 (by exact_mod_cast le_top), map_zero]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  have hD : ‖iteratedFDeriv ℝ n F v‖ ≤ ‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ := by
    have e0 : iteratedFDeriv ℝ n F v = iteratedFDeriv ℝ n (fun t => F (t + v)) 0 := by
      rw [iteratedFDeriv_comp_add_right, zero_add]
    have e2 : (fun t => (gau v • ρ v) (cexp (l t) • F t)) =
        ((gau v • ρ v).restrictScalars ℝ) ∘ (fun t => cexp (l t) • F t) := rfl
    rw [e0, hshift, e2]
    refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hG.smul hFs).contDiffAt hN).trans ?_
    refine mul_le_mul hL ?_ (norm_nonneg _) (norm_nonneg _)
    refine (norm_iteratedFDeriv_smul_le hG hFs 0 hN).trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp i) (by positivity))
      (norm_nonneg _)
  calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖
      ≤ ‖v‖ ^ k * (‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖ * (‖v‖ ^ (k + i) * ‖gau v‖) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, pow_add]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (pow_mul_norm_gau_le _ _) (by positivity)

theorem Sm.good : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ f : B,
    Sm ρ f → Good h f := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h f hf
  let ψ : SchwartzMap V B := ⟨fun u => gau u • ρ u f, contDiff_gau.smul hf, fun k n => decay_gau_smul h hf k n⟩
  have hψ : ((𝓕 ψ : SchwartzMap V B) : V → B) = 𝓕 (fun u => gau u • ρ u f) := SchwartzMap.fourier_coe ψ
  intro n
  have hint := (𝓕 ψ).integrable_pow_mul volume n
  refine (J.measurePreserving.integrable_comp_of_integrable hint).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, LinearIsometryEquiv.norm_map, proj_translate hJ h f w, h.2.2.1, hψ]

end GlobalTheory.RealWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.Osc

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}

set_option linter.unusedSectionVars false

theorem proj_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) : proj h (proj h f) = proj h f := by
  have := proj_heis_proj hJ h 0 f
  rwa [h.1, gau_zero, one_smul] at this

theorem good_of_sm (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) : Good h f :=
  Sm.good V B J ρ hJ h f hf

theorem heis_neg (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (w : V) (f : B) : ρ w (ρ (-w) f) = f := by
  have h0 : omJ J w (-w) = 0 := by
    have := omJ_skew hJ w w
    have e : omJ J w (-w) = -omJ J w w := by simp [omJ]
    linarith
  rw [h.2.1, h0, add_neg_cancel, h.1]
  simp

theorem cont_neg (h : IsHeis (omJ J) ρ) (f : B) : Continuous fun w => ρ (-w) f :=
  (h.2.2.2 f).comp continuous_neg

theorem integrable_pow_gau (n : ℕ) : Integrable fun w : V => ‖w‖ ^ n * ‖gau w‖ := by
  have h1 := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (π / 4 : ℂ))
    (by simpa using Real.pi_pos) 0 0).norm
  refine Integrable.mono' (h1.const_mul (n.factorial * Real.exp 1))
    ((continuous_norm.pow n).mul continuous_gau.norm).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have e : (-(π / 4 : ℂ) * (‖w‖ : ℂ) ^ 2 + 0 * ((⟪(0 : V), w⟫ : ℝ) : ℂ)) = ((-(π / 4) * ‖w‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_exp, ofReal_re, Real.norm_of_nonneg (by positivity), norm_gau]
  have h2 : ‖w‖ ^ n ≤ n.factorial * Real.exp ‖w‖ := by
    have := Real.pow_div_factorial_le_exp ‖w‖ (norm_nonneg w) n
    rwa [div_le_iff₀' (by positivity)] at this
  calc ‖w‖ ^ n * Real.exp (-(π / 2) * ‖w‖ ^ 2) ≤ n.factorial * Real.exp ‖w‖ * Real.exp (-(π / 2) * ‖w‖ ^ 2) := by
        gcongr
    _ ≤ _ := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        nlinarith [Real.pi_gt_three, sq_nonneg ‖w‖, sq_nonneg (‖w‖ - 1)]

theorem good_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x : B) : Good h (proj h x) := by
  intro n
  refine ((integrable_pow_gau (V := V) n).mul_const ‖proj h x‖).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [proj_heis_proj hJ, gau_neg, norm_smul, mul_assoc]

theorem sm_add {f f' : B} (hf : Sm ρ f) (hf' : Sm ρ f') : Sm ρ (f + f') := by
  simpa only [Sm, map_add (f := _)] using ContDiff.add hf hf'

theorem sm_smul (a : ℂ) {f : B} (hf : Sm ρ f) : Sm ρ (a • f) := by
  simpa only [Sm, map_smul] using ContDiff.const_smul a hf

theorem sm_heis (h : IsHeis (omJ J) ρ) (a : V) {f : B} (hf : Sm ρ f) : Sm ρ (ρ a f) := by
  unfold Sm
  simp only [h.2.1]
  refine ContDiff.smul (Complex.contDiff_exp.comp (contDiff_const.mul ?_)) (ContDiff.comp hf (contDiff_id.add contDiff_const))
  exact Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)

theorem sm_comp (g : V →L[ℝ] V) {f : B} (hf : Sm ρ f) : Sm (fun v => ρ (g v)) f :=
  ContDiff.comp hf g.contDiff

theorem good_integrable {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    Integrable fun w => ‖proj h (ρ (-w) f)‖ := by
  simpa using hf 0

theorem good_ext (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f f' : B} (hf : Good h f) (hf' : Good h f')
    (e : ∀ v, proj h (ρ v f) = proj h (ρ v f')) : f = f' := by
  rw [← hf.inversion hJ, ← hf'.inversion hJ]
  simp only [e]

def intw (ρ' : V → B →L[ℂ] B) (T : B →L[ℂ] B) (ρ : V → B →L[ℂ] B) (f : B) : B := ∫ w, ρ' w (T (ρ (-w) f))

variable {T : B →L[ℂ] B}

theorem norm_le_of_proj {h : IsHeis (omJ J) ρ} (hT : ∀ x, T (proj h x) = T x) (x : B) :
    ‖T x‖ ≤ ‖T‖ * ‖proj h x‖ := by
  rw [← hT]; exact T.le_opNorm _

theorem intw_integrable {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ') (hT : ∀ x, T (proj h x) = T x)
    {f : B} (hf : Good h f) : Integrable fun w => ρ' w (T (ρ (-w) f)) := by
  refine Integrable.mono' ((good_integrable hf).const_mul ‖T‖)
    (h'.continuous continuous_id (T.continuous.comp (cont_neg h f))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [h'.2.2.1]
  exact norm_le_of_proj hT _

theorem proj_heis_heis (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a b : V) {x : B} (hx : proj h x = x) :
    proj h (ρ a (ρ b x)) = (cexp (π * I * (omJ J a b : ℂ)) * gau (a + b)) • x := by
  rw [h.2.1, map_smul, ← hx, proj_heis_proj hJ, smul_smul]

theorem proj_heis_intw (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Good h f) (v : V) :
    proj h' (ρ' v (intw ρ' T ρ f)) = T (ρ v f) := by
  have e1 := ((proj h').comp (ρ' v)).integral_comp_comm (intw_integrable h' hT hf)
  have e2 := (T.comp ((proj h).comp (ρ v))).integral_comp_comm (intw_integrable h (proj_proj hJ h) hf)
  rw [hf.inversion hJ] at e2
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  rw [intw, ← e1, ← hT, ← e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [proj_heis_heis hJ h' _ _ (hT' _), proj_heis_heis hJ h _ _ (proj_proj hJ h _), map_smul, hT]

theorem good_intw (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Good h f) :
    Good h' (intw ρ' T ρ f) := by
  intro n
  simp only [proj_heis_intw hJ h' hT hT' hf]
  refine Integrable.mono' ((hf n).const_mul ‖T‖)
    ((continuous_norm.pow n).mul (T.continuous.comp (cont_neg h f)).norm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (by positivity), mul_left_comm]
  gcongr
  exact norm_le_of_proj hT _

theorem intw_heis (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Sm ρ f) (a : V) :
    intw ρ' T ρ (ρ a f) = ρ' a (intw ρ' T ρ f) := by
  have g1 := good_of_sm hJ h hf
  have g2 := good_of_sm hJ h (sm_heis h a hf)
  refine good_ext hJ (good_intw hJ h' hT hT' g2)
    (good_of_sm hJ h' (sm_heis h' a ((good_intw hJ h' hT hT' g1).sm hJ))) fun v => ?_
  rw [proj_heis_intw hJ h' hT hT' g2, h.2.1, h'.2.1, map_smul, map_smul, proj_heis_intw hJ h' hT hT' g1]

theorem intw_proj (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Sm ρ f)
    (a b : V →L[ℝ] V) (hab : ∀ v, a (b v) = v) (ha : ∀ x y, omJ J (a x) (a y) = omJ J x y) :
    intw ρ' T ρ (proj (h.twist a ha) f) = proj (h'.twist a ha) (intw ρ' T ρ f) := by
  have g1 := good_of_sm hJ h hf
  have s : ∀ {ρ : V → B →L[ℂ] B} (h : IsHeis (omJ J) ρ) (x : B), Good h (proj (h.twist a ha) x) := by
    intro ρ h x
    have := sm_comp b ((good_proj hJ (h.twist a ha) x).sm hJ)
    simp only [hab] at this
    exact good_of_sm hJ h this
  refine good_ext hJ (good_intw hJ h' hT hT' (s h f)) (s h' _) fun v => ?_
  rw [proj_heis_intw hJ h' hT hT' (s h f)]
  have e1 := (T.comp (ρ v)).integral_comp_comm ((h.twist a ha).integrable f)
  have e2 := ((proj h').comp (ρ' v)).integral_comp_comm ((h'.twist a ha).integrable (intw ρ' T ρ f))
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  rw [proj_apply (h.twist a ha), proj_apply (h'.twist a ha), ← e1, ← e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [h.2.1, h'.2.1, map_smul, proj_heis_intw hJ h' hT hT' g1]

theorem intw_add {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ') (hT : ∀ x, T (proj h x) = T x)
    {f f' : B} (hf : Good h f) (hf' : Good h f') : intw ρ' T ρ (f + f') = intw ρ' T ρ f + intw ρ' T ρ f' := by
  simp only [intw, map_add (f := _)]
  exact integral_add (intw_integrable h' hT hf) (intw_integrable h' hT hf')

theorem intw_smul (a : ℂ) (f : B) : intw ρ' T ρ (a • f) = a • intw ρ' T ρ f := by
  simp only [intw, map_smul, integral_smul]

theorem proj_comm (h : IsHeis (omJ J) ρ) (A : B →L[ℂ] B) (hA : ∀ v f, A (ρ v f) = ρ v (A f)) (x : B) :
    A (proj h x) = proj h (A x) := by
  rw [proj_apply, proj_apply, ← A.integral_comp_comm (h.integrable x)]
  simp only [map_smul, hA]

theorem intw_comm {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ') (hT : ∀ x, T (proj h x) = T x)
    {f : B} (hf : Good h f) (A : B →L[ℂ] B) (hA : ∀ v f, A (ρ v f) = ρ v (A f))
    (hA' : ∀ v f, A (ρ' v f) = ρ' v (A f)) (hAT : ∀ x, A (T x) = T (A x)) :
    intw ρ' T ρ (A f) = A (intw ρ' T ρ f) := by
  rw [intw, intw, ← A.integral_comp_comm (intw_integrable h' hT hf)]
  simp only [hA, hA', hAT]

theorem proj_twist_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (h' : IsHeis (omJ J) ρ') (a : V → V)
    (ha : ∀ u, ρ' u = ρ (a u)) (x : B) : proj h (proj h' (proj h x)) = lam a • proj h x := by
  rw [proj_apply h', ← (proj h).integral_comp_comm (h'.integrable _), lam, ← integral_smul_const]
  simp only [ha, map_smul, proj_heis_proj hJ, smul_smul]

theorem proj_twist_twist_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a b : V →L[ℝ] V)
    (ha : ∀ x y, omJ J (a x) (a y) = omJ J x y) (hb : ∀ x y, omJ J (b x) (b y) = omJ J x y) (x : B) :
    proj h (proj (h.twist a ha) (proj (h.twist b hb) (proj h x))) = mu J a b • proj h x := by
  rw [proj_apply (h.twist a ha), ← (proj h).integral_comp_comm ((h.twist a ha).integrable _), mu,
    ← integral_smul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e1 := ((proj h).comp (ρ (a u))).integral_comp_comm ((h.twist b hb).integrable (proj h x))
  simp only [ContinuousLinearMap.comp_apply] at e1
  simp only
  rw [map_smul, proj_apply (h.twist b hb), ← e1, ← integral_smul, ← integral_smul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [map_smul]
  rw [proj_heis_heis hJ h _ _ (proj_proj hJ h _), smul_smul, smul_smul]

section Norm

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Φ : B →L[ℂ] H}

theorem inner_heis (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (v : V) (x y : B) :
    inner ℂ (Φ (ρ v x)) (Φ (ρ v y)) = inner ℂ (Φ x) (Φ y) := by
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_smul, ← map_add (f := _), ← map_sub, hΦ]

theorem inner_heis' (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (v : V)
    (x y : B) : inner ℂ (Φ x) (Φ (ρ v y)) = inner ℂ (Φ (ρ (-v) x)) (Φ y) := by
  rw [← inner_heis hΦ v (ρ (-v) x), heis_neg hJ h]

theorem inner_integral (x : B) {F : V → B} (hF : Integrable F) :
    inner ℂ (Φ x) (Φ (∫ w, F w)) = ∫ w, inner ℂ (Φ x) (Φ (F w)) :=
  (((innerSL ℂ (Φ x)).comp Φ).integral_comp_comm hF).symm

theorem star_gau (u : V) : (starRingEnd ℂ) (gau u) = gau u := by
  rw [gau, ← Complex.exp_conj]
  simp [map_ofNat]

theorem inner_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖)
    (x y : B) : inner ℂ (Φ (proj h x)) (Φ y) = inner ℂ (Φ x) (Φ (proj h y)) := by
  rw [← inner_conj_symm, proj_apply, proj_apply, inner_integral _ (h.integrable _), inner_integral _ (h.integrable _),
    ← integral_conj, ← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_smul, inner_smul_right, map_mul, inner_conj_symm, star_gau, gau_neg, inner_heis' hJ h hΦ u]

theorem inner_intw (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hΦ : ∀ v f, ‖Φ (ρ' v f)‖ = ‖Φ f‖)
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Good h f) :
    inner ℂ (Φ (intw ρ' T ρ f)) (Φ (intw ρ' T ρ f)) = ∫ w, inner ℂ (Φ (T (ρ (-w) f))) (Φ (T (ρ (-w) f))) := by
  have := inner_integral (Φ := Φ) (intw ρ' T ρ f) (intw_integrable h' hT hf)
  refine this.trans (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_))
  simp only
  rw [inner_heis' hJ h' hΦ, ← hT' (ρ (-w) f), ← inner_proj hJ h' hΦ, proj_heis_intw hJ h' hT hT' hf, hT']

theorem norm_intw (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (hΦ' : ∀ v f, ‖Φ (ρ' v f)‖ = ‖Φ f‖)
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x)
    (hn : ∀ x, inner ℂ (Φ (T x)) (Φ (T x)) = inner ℂ (Φ (proj h x)) (Φ (proj h x))) {f : B} (hf : Good h f) :
    ‖Φ (intw ρ' T ρ f)‖ = ‖Φ f‖ := by
  have e1 := inner_intw hJ h' hΦ' hT hT' hf
  have e2 := inner_intw hJ h hΦ (proj_proj hJ h) (proj_proj hJ h) hf
  have e3 : intw ρ (proj h) ρ f = f := hf.inversion hJ
  simp only [hn] at e1
  rw [e3, ← e1] at e2
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), e2]

end Norm

theorem continuous_twist_proj (h : IsHeis (omJ J) ρ) :
    Continuous fun p : (V →L[ℝ] V) × B => ∫ u, gau u • ρ (p.1 u) p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  refine continuousAt_of_dominated (bound := fun u => ‖gau u‖ * (‖p₀.2‖ + 1)) ?_ ?_
    ((integrable_gau (V := V)).norm.mul_const _) ?_
  · exact Filter.Eventually.of_forall fun p =>
      (continuous_gau.smul ((h.2.2.2 p.2).comp p.1.continuous)).aestronglyMeasurable
  · have : ∀ᶠ p : (V →L[ℝ] V) × B in nhds p₀, ‖p.2‖ < ‖p₀.2‖ + 1 :=
      (continuous_snd.norm.continuousAt (x := p₀)).eventually_lt_const (lt_add_one _)
    filter_upwards [this] with p hp
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_smul, h.2.2.1]
    gcongr
  · refine Filter.Eventually.of_forall fun u => Continuous.continuousAt ?_
    exact (h.continuous (by fun_prop) continuous_snd).const_smul _

theorem continuous_twist_intw {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    Continuous fun a : V →L[ℝ] V => ∫ w, ρ (a w) (∫ u, gau u • ρ (a u) (proj h (ρ (-w) f))) := by
  have hc := continuous_twist_proj h
  refine continuous_of_dominated (bound := fun w => (∫ u : V, ‖gau u‖) * ‖proj h (ρ (-w) f)‖) ?_ ?_
    ((good_integrable hf).const_mul _) ?_
  · intro a
    exact (h.continuous a.continuous
      (hc.comp (continuous_const.prodMk ((proj h).continuous.comp (cont_neg h f))))).aestronglyMeasurable
  · intro a
    refine Filter.Eventually.of_forall fun w => ?_
    rw [h.2.2.1]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [norm_smul, h.2.2.1]
    rw [integral_mul_const]
  · refine Filter.Eventually.of_forall fun w => ?_
    exact h.continuous (by fun_prop) (hc.comp (continuous_id.prodMk continuous_const))

theorem proj_twist_of_isometry (h : IsHeis (omJ J) ρ) (a b : V →L[ℝ] V) (hab : ∀ v, a (b v) = v)
    (ha : ∀ x y, omJ J (a x) (a y) = omJ J x y) (hn : ∀ x, ‖a x‖ = ‖x‖) (x : B) :
    proj (h.twist a ha) x = proj h x := by
  let e : V ≃ₗᵢ[ℝ] V := LinearIsometryEquiv.ofSurjective ⟨a.toLinearMap, hn⟩ fun v => ⟨b v, hab v⟩
  have he : ∀ v, e v = a v := fun v => rfl
  rw [proj_apply, proj_apply, ← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun u => gau u • ρ u x)]
  simp only [he, gau, hn]

section Group

variable {G : Type} [Group G] {k : G →* (V →L[ℝ] V)} {c : G → ℂ}

theorem k_mul (k : G →* (V →L[ℝ] V)) (g g' : G) (v : V) : k (g * g') v = k g (k g' v) := by
  rw [map_mul]; rfl

theorem k_inv (k : G →* (V →L[ℝ] V)) (g : G) (v : V) : k g (k g⁻¹ v) = v := by
  rw [← k_mul, mul_inv_cancel, map_one]; rfl

abbrev pr (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (g : G) : B →L[ℂ] B :=
  proj (h.twist (k g) (hk g))

def vacOp (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (c : G → ℂ) (g : G) :
    B →L[ℂ] B := c g • (pr h hk g).comp (proj h)

def osc (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (c : G → ℂ) (g : G) (f : B) : B :=
  intw (fun v => ρ (k g v)) (vacOp h hk c g) ρ f

variable (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y)

theorem vacOp_apply (g : G) (x : B) : vacOp h hk c g x = c g • pr h hk g (proj h x) := rfl

theorem pr_one (x : B) : pr h hk 1 x = proj h x := by
  simp [proj_apply]

include hJ

theorem vacOp_proj (g : G) (x : B) : vacOp h hk c g (proj h x) = vacOp h hk c g x := by
  simp only [vacOp_apply, proj_proj hJ]

theorem proj_vacOp (g : G) (x : B) : pr h hk g (vacOp h hk c g x) = vacOp h hk c g x := by
  simp only [vacOp_apply, map_smul, proj_proj hJ]

theorem sm_osc (g : G) {f : B} (hf : Sm ρ f) : Sm ρ (osc h hk c g f) := by
  have := sm_comp (k g⁻¹) ((good_intw hJ (h.twist (k g) (hk g)) (vacOp_proj (c := c) hJ h hk g)
    (proj_vacOp hJ h hk g) (good_of_sm hJ h hf)).sm hJ)
  simp only [k_inv] at this
  exact this

theorem osc_heis (g : G) (v : V) {f : B} (hf : Sm ρ f) : osc h hk c g (ρ v f) = ρ (k g v) (osc h hk c g f) :=
  intw_heis hJ (h.twist (k g) (hk g)) (vacOp_proj hJ h hk g) (proj_vacOp hJ h hk g) hf v

theorem pr_osc (g : G) {f : B} (hf : Sm ρ f) : pr h hk g (osc h hk c g f) = c g • pr h hk g (proj h f) := by
  have := proj_heis_intw hJ (h.twist (k g) (hk g)) (vacOp_proj (c := c) hJ h hk g)
    (proj_vacOp hJ h hk g) (good_of_sm hJ h hf) 0
  simp only [map_zero, h.1] at this
  exact this

theorem osc_pr (g g' : G) {f : B} (hf : Sm ρ f) :
    osc h hk c g (pr h hk g' f) = pr h hk (g * g') (osc h hk c g f) := by
  refine (intw_proj hJ (h.twist (k g) (hk g)) (vacOp_proj (c := c) hJ h hk g)
    (proj_vacOp hJ h hk g) hf (k g') (k g'⁻¹) (k_inv k g') (hk g')).trans ?_
  simp only [proj_apply, k_mul, osc]

theorem osc_proj (g : G) {f : B} (hf : Sm ρ f) : osc h hk c g (proj h f) = c g • pr h hk g (proj h f) := by
  rw [← pr_osc hJ h hk g hf, ← pr_one h hk, osc_pr hJ h hk g 1 hf, mul_one]

theorem osc_one (hc : c 1 = 1) {f : B} (hf : Sm ρ f) : osc h hk c 1 f = f := by
  refine Eq.trans ?_ ((good_of_sm hJ h hf).inversion hJ)
  simp only [osc, intw, vacOp_apply, pr_one, proj_proj hJ, hc, one_smul, map_one, ContinuousLinearMap.one_apply]

theorem scalar_mul (hl : ∀ g, star (c g) * c g * lam (k g) = 1)
    (hm : ∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) (g g' : G) (x : B) :
    (c g * c g') • pr h hk (g * g') (pr h hk g (proj h x)) = c (g * g') • pr h hk (g * g') (proj h x) := by
  rw [← sub_eq_zero]
  set y := (c g * c g') • pr h hk (g * g') (pr h hk g (proj h x)) - c (g * g') • pr h hk (g * g') (proj h x) with hy
  have h1 : proj h y = 0 := by
    rw [hy, map_sub, map_smul, map_smul, proj_twist_twist_proj hJ h _ _ (hk _) (hk _),
      proj_twist_proj hJ h _ (k (g * g')) (fun _ => rfl), smul_smul, smul_smul, hm, sub_self]
  have h2 : pr h hk (g * g') y = y := by
    simp only [hy, map_sub, map_smul, proj_proj hJ]
  have h3 := proj_twist_proj hJ (h.twist (k (g * g')) (hk _)) h (k (g * g')⁻¹) (fun u => by simp only [k_inv]) y
  have h4 : lam (k (g * g')⁻¹) ≠ 0 := fun e => by
    have := hl (g * g')⁻¹
    rw [e, mul_zero] at this
    exact zero_ne_one this
  rw [h2, h1, map_zero] at h3
  exact (smul_eq_zero.1 h3.symm).resolve_left h4

theorem osc_mul (hl : ∀ g, star (c g) * c g * lam (k g) = 1)
    (hm : ∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) (g g' : G) {f : B}
    (hf : Sm ρ f) : osc h hk c (g * g') f = osc h hk c g (osc h hk c g' f) := by
  have s1 := sm_osc (c := c) hJ h hk g' hf
  refine good_ext hJ (h := h.twist (k (g * g')) (hk _))
    (good_of_sm hJ _ (sm_comp _ (sm_osc hJ h hk _ hf))) (good_of_sm hJ _ (sm_comp _ (sm_osc hJ h hk _ s1))) fun v => ?_
  have s2 := sm_heis h v hf
  have s3 : Sm ρ (proj h (ρ v f)) := (good_proj hJ h _).sm hJ
  show pr h hk (g * g') _ = pr h hk (g * g') _
  rw [← osc_heis hJ h hk _ v hf, pr_osc hJ h hk _ s2, k_mul, ← osc_heis hJ h hk _ _ s1, ← osc_heis hJ h hk _ v hf,
    ← osc_pr hJ h hk _ _ (sm_osc hJ h hk _ s2), pr_osc hJ h hk _ s2, osc, intw_smul, ← osc,
    osc_pr hJ h hk _ _ s3, osc_proj hJ h hk _ s2, map_smul, smul_smul, mul_comm (c g'), scalar_mul hJ h hk hl hm]

theorem norm_osc (hl : ∀ g, star (c g) * c g * lam (k g) = 1) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (g : G) {f : B}
    (hf : Sm ρ f) : ‖Φ (osc h hk c g f)‖ = ‖Φ f‖ := by
  refine norm_intw hJ (h.twist (k g) (hk g)) hΦ (fun v => hΦ _) (vacOp_proj hJ h hk g) (proj_vacOp hJ h hk g)
    (fun x => ?_) (good_of_sm hJ h hf)
  have e : inner ℂ (Φ (pr h hk g (proj h x))) (Φ (pr h hk g (proj h x))) =
      lam (k g) * inner ℂ (Φ (proj h x)) (Φ (proj h x)) := by
    rw [inner_proj hJ (h.twist (k g) (hk g)) (fun v => hΦ _), proj_proj hJ, inner_proj hJ h hΦ,
      proj_twist_proj hJ h _ (k g) (fun _ => rfl), map_smul, inner_smul_right, inner_proj hJ h hΦ, proj_proj hJ]
  rw [vacOp_apply, map_smul, inner_smul_left, inner_smul_right, e, ← mul_assoc, ← mul_assoc]
  exact (congrArg (· * _) (hl g)).trans (one_mul _)

end Group

theorem exists_isOsc : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h G _ k c hk hc hl hm
  refine ⟨osc h hk c, ⟨fun g f f' hf hf' => ?_, fun g a f _ => intw_smul a f, fun g f hf => sm_osc hJ h hk g hf,
    fun f hf => osc_one hJ h hk hc hf, fun g g' f hf => osc_mul hJ h hk hl hm g g' hf,
    fun g v f hf => osc_heis hJ h hk g v hf, fun g A hA f hf => ?_,
    fun H _ _ _ Φ hΦ g f hf => norm_osc hJ h hk hl Φ hΦ g hf⟩, fun Y _ γ hγ hcγ f hf => ?_,
    fun a g hg f hf hfa => ?_⟩
  · exact intw_add (h.twist (k g) (hk g)) (vacOp_proj hJ h hk g) (good_of_sm hJ h hf) (good_of_sm hJ h hf')
  · refine intw_comm (h.twist (k g) (hk g)) (vacOp_proj hJ h hk g) (good_of_sm hJ h hf) A hA (fun v => hA _)
      fun x => ?_
    rw [vacOp_apply, vacOp_apply, map_smul, proj_comm (h.twist (k g) (hk g)) A (fun v => hA _), proj_comm h A hA]
  · refine (hcγ.smul ((continuous_twist_intw (good_of_sm hJ h hf)).comp hγ)).congr fun y => ?_
    simp only [osc, intw, vacOp_apply, map_smul, integral_smul]
    rfl
  · have hfa' : pr h hk a f = f := hfa
    have s0 := sm_osc (c := c) hJ h hk a⁻¹ hf
    have e0 : proj h (osc h hk c a⁻¹ f) = osc h hk c a⁻¹ f := by
      rw [← pr_one h hk, ← inv_mul_cancel a, ← osc_pr hJ h hk _ _ hf, hfa']
    have e1 : osc h hk c g (osc h hk c a⁻¹ f) = c g • osc h hk c a⁻¹ f := by
      have := osc_proj (c := c) hJ h hk g s0
      rw [proj_twist_of_isometry h (k g) (k g⁻¹) (k_inv k g) (hk g) hg, e0, e0] at this
      exact this
    rw [osc_mul hJ h hk hl hm _ _ hf, osc_mul hJ h hk hl hm _ _ s0, e1, osc, intw_smul, ← osc,
      ← osc_mul hJ h hk hl hm _ _ hf, mul_inv_cancel, osc_one hJ h hk hc hf]

end GlobalTheory.RealWeil.Osc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairingsStatement
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by
  first | exact @GlobalTheory.RealWeil.Osc.exists_isOsc | exact GlobalTheory.RealWeil.Osc.exists_isOsc | (intros; apply GlobalTheory.RealWeil.Osc.exists_isOsc <;> assumption)
end
