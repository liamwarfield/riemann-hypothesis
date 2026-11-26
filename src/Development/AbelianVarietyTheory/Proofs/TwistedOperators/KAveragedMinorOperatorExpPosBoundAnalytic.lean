module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLeadMinorDecay
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsURepOnOfIsTau
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Dec.FormF
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.PsiBound

lemma det_exp_sq {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y) :
    (NormedSpace.exp Y).det * (NormedSpace.exp Y).det = 1 := by
  have hJ := Jm_mul_self ε
  have h1 : Jm ε * Y * Jm ε = -Y := by
    rw [Matrix.mul_assoc, h.2, Matrix.mul_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h2 : NormedSpace.exp (Jm ε * Y * Jm ε) = Jm ε * NormedSpace.exp Y * Jm ε :=
    Matrix.exp_units_conj (⟨Jm ε, Jm ε, hJ, hJ⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ) Y
  have h3 : (Jm ε).det * (Jm ε).det = 1 := by rw [← det_mul, hJ, det_one]
  have h4 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have h5 := congrArg Matrix.det h4
  rw [← h1, h2, det_mul, det_mul, det_mul, det_one] at h5
  linear_combination h5 - (NormedSpace.exp Y).det * (NormedSpace.exp Y).det * h3

lemma muInt_cast {n : ℕ} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (a : Fin n) :
    (muInt lam a : ℝ) = lam a + Formalism.QuantumDeterminants.rhoStd n a := by
  obtain ⟨m, hm⟩ := hlam.2 a
  have : lam a + Formalism.QuantumDeterminants.rhoStd n a = ((m + n - 1 - (a : ℕ) : ℤ) : ℝ) := by
    unfold Formalism.QuantumDeterminants.rhoStd; push_cast; linarith
  unfold muInt
  rw [this, Int.floor_intCast]

lemma norm_Phi_le {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {X km : Matrix (Fin n) (Fin n) ℂ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h)
    (hX : inP ε X) (hk : km ∈ Kset ε) :
    ‖Phi lam (km⁻¹ * NormedSpace.exp X * km)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := by
  obtain ⟨hpos, hle⟩ := GlobalTheory.MinorDecay.prod_leadMinor_decay n ε lam h X km hlam hgap hX hk
  obtain ⟨hY, -, hexp⟩ := GlobalTheory.MinorDecay.conj_facts hX hk
  have hsq := det_exp_sq hY
  rw [← hexp] at hsq
  have hs0 : 0 ≤ hs X := by unfold hs; positivity
  unfold decHS rkR
  rw [Real.sq_sqrt hs0]
  refine le_trans (le_of_eq ?_) hle
  set z := km⁻¹ * NormedSpace.exp X * km with hz
  have hn : ∀ l hl, ‖leadMinor z l hl‖ = (leadMinor z l hl).re := fun l hl => by
    rw [← Complex.abs_re_eq_norm.2 (hpos l hl).2, abs_of_pos (hpos l hl).1]
  unfold Phi
  rw [norm_prod]
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_castSucc]
    have hdet : leadMinor z ((Fin.last m).val + 1) (Fin.last m).isLt = z.det := rfl
    have hone : ‖z.det‖ = 1 := by
      have h1 := congrArg norm hsq
      rw [norm_mul, norm_one] at h1
      nlinarith [norm_nonneg z.det]
    rw [norm_zpow, hdet, hone, _root_.one_zpow, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_zpow, hn, ← Real.rpow_intCast]
    congr 1
    have hi : (Fin.castSucc i).val + 1 < m + 1 := by simp
    unfold sInt
    rw [dite_eq_left hi]
    push_cast
    rw [muInt_cast hlam, muInt_cast hlam]
    unfold Formalism.QuantumDeterminants.rhoStd
    simp only [Fin.val_castSucc]
    push_cast
    have : lam (Fin.castSucc i) = lam ⟨i.val, by omega⟩ := rfl
    rw [this]
    ring

lemma weighted_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (d : ℕ) (φ a b : α → ℂ)
    (M U V : ℝ) (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : ∀ x, ‖φ x‖ ≤ M)
    (i1 : Integrable (fun x => ‖a x‖ ^ 2) μ) (i2 : Integrable (fun x => ‖b x‖ ^ 2) μ)
    (ha : (d : ℝ) * ∫ x, ‖a x‖ ^ 2 ∂μ = V ^ 2) (hb : (d : ℝ) * ∫ x, ‖b x‖ ^ 2 ∂μ = U ^ 2) :
    ‖(d : ℂ) * ∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * U * V := by
  have key : ∀ t : ℝ, 0 < t →
      ‖(d : ℂ) * ∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * (t / 2) * V ^ 2 + M * (1 / (2 * t)) * U ^ 2 := by
    intro t ht
    have hbd := norm_integral_le_of_norm_le (μ := μ) (f := fun x => φ x * (a x * b x))
      (g := fun x => M * (t / 2) * ‖a x‖ ^ 2 + M * (1 / (2 * t)) * ‖b x‖ ^ 2)
      ((i1.const_mul _).add (i2.const_mul _)) (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, norm_mul]
        have hab : ‖a x‖ * ‖b x‖ ≤ t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2 := by
          have : t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2 - ‖a x‖ * ‖b x‖ =
              (t * ‖a x‖ - ‖b x‖) ^ 2 / (2 * t) := by
            field_simp; ring
          have h2 : 0 ≤ (t * ‖a x‖ - ‖b x‖) ^ 2 / (2 * t) := by positivity
          linarith
        calc _ ≤ M * (t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2) :=
              mul_le_mul (hφ x) hab (by positivity) hM
          _ = _ := by ring)
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul] at hbd
    rw [norm_mul, Complex.norm_natCast]
    refine (mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg d)).trans (le_of_eq ?_)
    rw [mul_add, mul_left_comm, ha, mul_left_comm (d : ℝ), hb]
  refine le_of_forall_pos_le_add fun e he => ?_
  obtain ⟨δ, hδ, hδe⟩ : ∃ δ : ℝ, 0 < δ ∧ M * (U + V) * δ ≤ e :=
    ⟨e / (M * (U + V) + 1), by positivity, by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith⟩
  refine (key ((U + δ) / (V + δ)) (by positivity)).trans ?_
  have h1 : (U + δ) / (V + δ) / 2 * V ^ 2 ≤ (U + δ) * V / 2 := by
    rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (U + δ) * V * δ := by positivity
    nlinarith
  have h2 : 1 / (2 * ((U + δ) / (V + δ))) * U ^ 2 ≤ (V + δ) * U / 2 := by
    have : 1 / (2 * ((U + δ) / (V + δ))) * U ^ 2 = (V + δ) * U ^ 2 / (2 * (U + δ)) := by
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (V + δ) * U * δ := by positivity
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hM
  have h4 : 0 ≤ M * (U + V) * δ := by positivity
  nlinarith

section Tau

variable {n : ℕ} {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

lemma isURepOn_of_isTau (h : IsTau ε abelian₂ τ w) : IsURepOn (Kset ε) τ := by
  obtain ⟨hW, hrep, hdiff, hadj, -⟩ := h
  refine ⟨⟨hrep.1, fun a ha b hb => hrep.2 a (K_KC ha) b (K_KC hb)⟩, fun g hg v => ?_, fun v => ?_⟩
  · have h1 := hadj g (K_KC hg) v (τ g v)
    have h2 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 gᴴ (K_KC (Kset_star ε hg)) g (K_KC hg), h2, hrep.1,
      ContinuousLinearMap.one_apply] at h1
    rw [@norm_eq_sqrt_re_inner ℂ, h1, ← @norm_eq_sqrt_re_inner ℂ]
  · let b := stdOrthonormalBasis ℂ W
    have e : (fun k => τ k v) = fun k => ∑ i, ⟪b i, τ k v⟫_ℂ • b i :=
      funext fun k => (b.sum_repr' _).symm
    rw [e]
    refine continuousOn_finsetSum _ fun i _ => ContinuousOn.smul ?_ continuousOn_const
    exact (hdiff (b i) v).continuousOn.mono fun k hk => K_KC hk

lemma schur_norm (h : IsTau ε abelian₂ τ w) (x : W) :
    (Module.finrank ℂ W : ℝ) * ∫ k : KG ε, ‖⟪x, τ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) = ‖x‖ ^ 2 := by
  have hU := isURepOn_of_isTau h
  obtain ⟨hW, -, -, -, hirr, hw, -⟩ := h
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  obtain ⟨c, -, hc⟩ := avgSchur n ε W τ w hW hU hirr (by rintro rfl; simp at hw)
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) :=
    (hU.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have hc' : ∀ y : W, ∫ k : KG ε, ⟪τ (toMK k) w, y⟫_ℂ * ⟪y, τ (toMK k) w⟫_ℂ ∂(muK ε) = c * ⟪y, y⟫_ℂ :=
    fun y => hc y (innerSL ℂ y)
  let b := stdOrthonormalBasis ℂ W
  have hd : (Module.finrank ℂ W : ℂ) * c = 1 := by
    have h2 : ∑ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) =
        (Module.finrank ℂ W : ℂ) * c := by
      simp only [hc', inner_self_eq_norm_sq_to_K, b.orthonormal.1]
      simp
    rw [← h2, ← MeasureTheory.integral_finsetSum _ fun i _ =>
      ((h1.inner continuous_const).mul (continuous_const.inner h1)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)]
    have h3 : ∀ k : KG ε, ‖τ (toMK k) w‖ = 1 := fun k => (hU.2.1 _ k.2 w).trans hw
    simp only [b.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K, h3]
    simp
  have e : ∀ k : KG ε, ⟪τ (toMK k) w, x⟫_ℂ * ⟪x, τ (toMK k) w⟫_ℂ =
      ((‖⟪x, τ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [← inner_conj_symm (τ (toMK k) w) x, Complex.conj_mul']; simp
  have h4 := hc' x
  simp only [e, integral_complex_ofReal] at h4
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, h4, Complex.ofReal_natCast, ← mul_assoc, hd, one_mul, Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x

lemma ps_entry (h : IsTau ε abelian₂ τ w) (lam : Fin n → ℝ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    (u y : W) :
    ⟪y, ps ε lam τ w x u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * x * toMK k) *
      (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  haveI := h.1
  haveI := FiniteDimensional.complete ℂ W
  have hk := toMK_cont ε
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) :=
    ((isURepOn_of_isTau h).2.2 w).comp_continuous hk fun k => k.2
  have h2 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k)) := by
    have e : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k => K_inv k.2
    simp only [e]
    unfold Phi
    refine continuous_finsetProd _ fun i _ => Continuous.zpow₀ ?_ _ fun k => Or.inl ?_
    · unfold leadMinor
      exact (((hk.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hk).matrix_submatrix
        _ _).matrix_det
    · exact ((hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC k.2).1)).submatrix
        (Fin.castLE_injective _)).det_pos.ne'
  have h3 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    h2.smul (((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp
      ((innerSL ℂ).continuous.comp h1)).clm_apply h1)
  have h4 := h3.integrable_of_hasCompactSupport (μ := muK ε) (HasCompactSupport.of_compactSpace _)
  unfold ps
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply h4,
    ← integral_inner (h4.apply_continuousLinearMap u)]
  congr 2
  funext k
  simp [inner_smul_right, mul_comm]

end Tau

end GlobalTheory.PsiBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAveragedMinorOperatorExpPosBoundAnalytic
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

private lemma posDef_inv_toMK_mul_mul_toMK {n : ℕ} {ε : Fin n → Bool} (k : KG ε)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : ((toMK k)⁻¹ * x * toMK k).PosDef := by
  have hK : toMK k ∈ Kset ε := (mem_KG ε _).1 k.2
  have hU : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hK.1
  have hinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  rw [hinv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro v₁ v₂ hv
  have := congrArg (fun v => (toMK k)ᴴ *ᵥ v) hv
  simpa [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU] using this

private lemma norm_inner_ps_exp_le_decHS_mul {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    {w : W} (hlam : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) {h : ℝ}
    (hgap : GapAtLeast ε lam h) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (u y : W) :
    ‖⟪y, ps ε lam τ w (NormedSpace.exp X) u⟫_ℂ‖ ≤
      decHS h (rkR ε) (Real.sqrt (hs X)) * ‖u‖ * ‖y‖ := by
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  have hint : ∀ v : W, Integrable (fun k : KG ε => ‖⟪v, τ (toMK k) w⟫_ℂ‖ ^ 2) (muK ε) := by
    intro v
    by_contra hn
    have hs := GlobalTheory.PsiBound.schur_norm hτ v
    rw [integral_undef hn, mul_zero] at hs
    have hv : v = 0 := by
      have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      exact norm_eq_zero.1 this
    subst hv
    simp at hn
  have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
  rw [GlobalTheory.PsiBound.ps_entry hτ lam hP u y]
  refine GlobalTheory.PsiBound.weighted_bound (muK ε) (Module.finrank ℂ W) _ _ _ _ _ _ hM (norm_nonneg u)
    (norm_nonneg y) (fun k => GlobalTheory.PsiBound.norm_Phi_le hlam hgap hX ((mem_KG ε _).1 k.2))
    (hint y) ?_ (GlobalTheory.PsiBound.schur_norm hτ y) ?_
  · simpa only [norm_inner_symm] using hint u
  · simpa only [norm_inner_symm] using GlobalTheory.PsiBound.schur_norm hτ u

theorem ps_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  intro n ε lam W _ _ τ w hlam hτ h hgap X hX
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  refine ⟨fun x => ?_, ?_, ?_⟩
  ·
    rw [GlobalTheory.PsiBound.ps_entry hτ lam hP x x]
    set F : KG ε → ℂ := fun k => Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) *
      (⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) with hFdef
    have hF : ∀ k, 0 ≤ F k := by
      intro k
      have hphi : 0 < Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) :=
        (phiPos n lam _ (posDef_inv_toMK_mul_mul_toMK k hP)).2.1
      have hsq : 0 ≤ ⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ := by
        rw [← inner_conj_symm x (τ (toMK k) w), mul_comm, Complex.mul_conj]
        exact Complex.zero_le_real.2 (Complex.normSq_nonneg _)
      exact mul_nonneg hphi.le hsq
    have hre : ∀ k, F k = ((F k).re : ℂ) := fun k =>
      Complex.ext rfl (by simpa using ((Complex.le_def.1 (hF k)).2).symm)
    have hI : ∫ k, F k ∂(muK ε) = ((∫ k, (F k).re ∂(muK ε) : ℝ) : ℂ) := by
      rw [integral_congr_ae (Eventually.of_forall hre)]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [hI]
    refine mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.2 (integral_nonneg fun k => ?_))
    exact (Complex.le_def.1 (hF k)).1
  ·
    have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun u => ?_
    set T := ps ε lam τ w (NormedSpace.exp X)
    rcases eq_or_ne (T u) 0 with h0 | h0
    · rw [h0, norm_zero]; positivity
    have hb := norm_inner_ps_exp_le_decHS_mul hlam hτ hgap hX u (T u)
    rw [inner_self_eq_norm_sq_to_K] at hb
    simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hb
    have hpos : 0 < ‖T u‖ := norm_pos_iff.2 h0
    nlinarith
  ·
    obtain ⟨hopen, hpos, hdiff, -⟩ := psBasic n ε lam W τ w hlam hτ
    haveI : FiniteDimensional ℂ W := hτ.1
    haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
    let e : (Fin n → Fin n → ℂ) ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv
    have hg : AnalyticAt ℂ (fun z : Fin n → Fin n → ℂ => ps ε lam τ w (Matrix.of z))
        (e.symm (NormedSpace.exp X)) :=
      GlobalTheory.SCV.analyticAt_of_differentiableOn hdiff
        (hopen.mem_nhds (show Matrix.of _ ∈ U1 ε from hpos _ hP))
    have he : AnalyticAt ℂ (⇑e.symm) (NormedSpace.exp X) :=
      e.symm.toContinuousLinearMap.analyticAt _
    exact hg.comp he

end GlobalTheory.SphJet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAveragedMinorOperatorExpPosBoundAnalyticStatement
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  first | exact @GlobalTheory.SphJet.ps_exp_pos_bound_analytic | exact GlobalTheory.SphJet.ps_exp_pos_bound_analytic | (intros; apply GlobalTheory.SphJet.ps_exp_pos_bound_analytic <;> assumption)
end
