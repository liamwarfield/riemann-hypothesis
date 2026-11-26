module

public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
public import GroundTheory.GlobalFields.LocalFieldAtPlace

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.OM.SchDiff

section general

variable {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiff_iter {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (iteratedFDeriv ℝ n F) :=
  hF.iteratedFDeriv_right (by norm_cast)

theorem fderiv_iter_comm {F : X → V} (hF : ContDiff ℝ ∞ F) (h : X) (n : ℕ) (a : X) :
    fderiv ℝ (iteratedFDeriv ℝ n F) a h = iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a := by
  induction n generalizing a with
  | zero =>
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((contDiff_iter hF 0).differentiable (by simp) a)]
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    ext m
    have hK := contDiff_iter hF n
    have hK' : ContDiff ℝ ∞ (fderiv ℝ (iteratedFDeriv ℝ n F)) := hK.fderiv_right (by norm_cast)
    have hd := hK'.differentiable (by simp) a
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((contDiff_iter hF (n + 1)).differentiable (by simp) a), iteratedFDeriv_succ_apply_left,
      ← funext ih]
    simp only [iteratedFDeriv_succ_apply_left]
    rw [fderiv_continuousMultilinear_apply_const_apply (hd.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
    have hs := (hK.contDiffAt (x := a)).isSymmSndFDerivAt (by simp)
    simp [hs.eq h (m 0)]

theorem taylor_iter {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) (a h : X) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ segment ℝ a (a + h), ‖iteratedFDeriv ℝ (n + 2) F b‖ ≤ M) :
    ‖iteratedFDeriv ℝ n F (a + h) - iteratedFDeriv ℝ n F a
      - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a‖ ≤ M * ‖h‖ * ‖h‖ := by
  have h1 : ∀ b ∈ segment ℝ a (a + h),
      ‖fderiv ℝ (iteratedFDeriv ℝ n F) b - fderiv ℝ (iteratedFDeriv ℝ n F) a‖ ≤ M * ‖h‖ := by
    intro b hb
    have h2 := (convex_segment a (a + h)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ (n + 1) F) (C := M)
      (fun x _ => (contDiff_iter hF (n + 1)).differentiable (by simp) x)
      (fun x hx => by rw [norm_fderiv_iteratedFDeriv]; exact hM x hx)
      (left_mem_segment _ _ _) hb
    have h3 : ‖b - a‖ ≤ ‖h‖ := by
      simpa using norm_sub_le_of_mem_segment hb
    rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact h2.trans (by gcongr)
  have h4 := (convex_segment a (a + h)).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ n F)
      (fun x _ => (contDiff_iter hF n).differentiable (by simp) x) h1
      (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  rw [add_sub_cancel_left, fderiv_iter_comm hF] at h4
  exact h4

end general

section family

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iter_slice {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) (p : P) (x : E) :
    iteratedFDeriv ℝ n (fun y => F (p, y)) x =
      (iteratedFDeriv ℝ n F (p, x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  have h1 : (fun y => F (p, y)) = (fun q => F ((p, 0) + q)) ∘ ContinuousLinearMap.inr ℝ P E := by
    funext y; simp
  have h2 : ContDiff ℝ ∞ (fun q => F ((p, 0) + q)) := hF.comp (contDiff_const.add contDiff_id)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ h2 _ (by norm_cast; simp),
    iteratedFDeriv_comp_add_left]
  simp

theorem seminorm_remainder {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (z : P)
    (hb : ∀ k n : ℕ, ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F (p, x)‖ ≤ C)
    (R D : P → SchwartzMap E ℂ) (hR : ∀ p, ⇑(R p) = fun x => F (p, x))
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0)) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (R (z + v) - R z - D v) ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hb k (n + 2)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC z (by simp) 0)
  refine ⟨C, fun v hv => SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_⟩
  have hG : ContDiff ℝ ∞ (fun b => fderiv ℝ F b ((v, 0) : P × E)) :=
    (hF.fderiv_right (m := ∞) (by norm_cast)).clm_apply contDiff_const
  have e1 : iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x =
      iteratedFDeriv ℝ n (R (z + v)) x - iteratedFDeriv ℝ n (R z) x - iteratedFDeriv ℝ n (D v) x := by
    have : ⇑(R (z + v) - R z - D v) = ⇑(R (z + v)) - ⇑(R z) - ⇑(D v) := by
      funext y; simp
    rw [this, iteratedFDeriv_sub_apply (f := ⇑(R (z + v)) - ⇑(R z)) (((R (z + v)).smooth n).sub ((R z).smooth n)).contDiffAt
      ((D v).smooth n).contDiffAt, iteratedFDeriv_sub_apply ((R (z + v)).smooth n).contDiffAt
      ((R z).smooth n).contDiffAt]
  have e2 : iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x =
      (iteratedFDeriv ℝ n F ((z, x) + (v, 0)) - iteratedFDeriv ℝ n F (z, x)
        - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b ((v, 0) : P × E)) (z, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
    rw [e1, hR, hR, hD, iter_slice hF, iter_slice hF, iter_slice hG]
    ext m
    simp
  rcases eq_or_lt_of_le (show 0 ≤ ‖x‖ ^ k by positivity) with h0 | h0
  · rw [← h0, zero_mul]; positivity
  have h3 := taylor_iter hF n (z, x) (v, 0) (M := C / ‖x‖ ^ k) (by positivity) (by
    rintro b ⟨s, t, hs, ht, hst, rfl⟩
    have : s • (z, x) + t • ((z, x) + (v, (0 : E))) = (z + t • v, x) := by
      obtain rfl : s = 1 - t := by linarith
      ext <;> simp <;> module
    rw [this, le_div_iff₀ h0, mul_comm]
    apply hC
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
    nlinarith [norm_nonneg v])
  have h4 : ‖((v, 0) : P × E)‖ = ‖v‖ := by simp [Prod.norm_def]
  rw [h4] at h3
  have h5 : ‖iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x‖ ≤ C / ‖x‖ ^ k * ‖v‖ * ‖v‖ := by
    rw [e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) h3
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_inr_le_one _ _ _
  calc _ ≤ ‖x‖ ^ k * (C / ‖x‖ ^ k * ‖v‖ * ‖v‖) := by gcongr
    _ = _ := by field_simp

theorem hasFDerivAt_family {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (z : P)
    (hb : ∀ k n : ℕ, ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F (p, x)‖ ≤ C)
    (R D : P → SchwartzMap E ℂ) (hR : ∀ p, ⇑(R p) = fun x => F (p, x))
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0))
    (T : SchwartzMap E ℂ →L[ℂ] ℂ) (L : P →L[ℝ] ℂ) (hL : ∀ v, L v = T (D v)) :
    HasFDerivAt (fun p => T (R p)) L z := by
  obtain ⟨S, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (by
      change Continuous fun f => ‖T f‖
      fun_prop)
  choose B hB using seminorm_remainder hF z hb R D hR hD
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun v : P => ‖v‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C * ∑ i ∈ S, |B i.1 i.2|) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : P) one_pos] with v hv
  rw [mem_closedBall_zero_iff] at hv
  have h1 := hC (R (z + v) - R z - D v)
  have h2 : (S.sup (schwartzSeminormFamily ℂ E ℂ)) (R (z + v) - R z - D v) ≤
      (∑ i ∈ S, |B i.1 i.2|) * ‖v‖ ^ 2 := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => (hB i.1 i.2 v hv).trans ?_
    gcongr
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i : ℕ × ℕ => |B i.1 i.2|)
      (fun _ _ => abs_nonneg _) hi)
  rw [hL, ← map_sub, ← map_sub, Real.norm_of_nonneg (by positivity), mul_assoc]
  refine le_trans h1 ?_
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  gcongr

theorem bound_mul_translate {A : P × E → ℂ} (hA : Function.HasTemperateGrowth A) (s : SchwartzMap E ℂ)
    (l : P →L[ℝ] E) (z : P) (k n : ℕ) :
    ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun q : P × E => A q * s (q.2 + l q.1)) (p, x)‖ ≤ C := by
  obtain ⟨N, C₀, hC₀, hN⟩ := hA.norm_iteratedFDeriv_le_uniform n
  set L : P × E →L[ℝ] E := ContinuousLinearMap.snd ℝ P E + l ∘L ContinuousLinearMap.fst ℝ P E with hL
  have hLq : ∀ q : P × E, L q = q.2 + l q.1 := fun q => rfl
  set c : ℝ := 1 + (‖z‖ + 1) + ‖l‖ * (‖z‖ + 1) with hc
  set S : ℝ := 2 ^ (k + N) * ((Finset.Iic (k + N, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) s with hS
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C₀ * c ^ (k + N) * ‖L‖ ^ (n - i) * S,
    fun p hp x => ?_⟩
  have hp' : ‖p‖ ≤ ‖z‖ + 1 := by
    have := norm_add_le z (p - z)
    rw [add_sub_cancel] at this
    linarith
  have hx : ‖x‖ ≤ ‖x + l p‖ + ‖l‖ * (‖z‖ + 1) := by
    have h1 := norm_sub_le (x + l p) (l p)
    rw [add_sub_cancel_right] at h1
    have h2 : ‖l p‖ ≤ ‖l‖ * (‖z‖ + 1) := (l.le_opNorm p).trans (by gcongr)
    linarith
  have hl0 : 0 ≤ ‖l‖ * (‖z‖ + 1) := by positivity
  have hq : 1 + ‖(p, x)‖ ≤ c * (1 + ‖x + l p‖) := by
    have h1 : ‖(p, x)‖ ≤ ‖p‖ + ‖x‖ := by
      rw [Prod.norm_def]
      exact max_le (by simp) (by simp)
    have h2 : 1 * ‖x + l p‖ ≤ c * ‖x + l p‖ := by
      gcongr
      have := norm_nonneg z
      linarith
    linarith
  have hx' : ‖x‖ ≤ c * (1 + ‖x + l p‖) := by
    have := norm_snd_le (p, x)
    linarith
  have hs : ContDiff ℝ ∞ (⇑s ∘ L) := (s.smooth ⊤).comp L.contDiff
  have h1 := norm_iteratedFDeriv_mul_le hA.1 hs (p, x) (n := n) (by norm_cast; simp)
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  have h2 : ‖iteratedFDeriv ℝ (n - i) (⇑s ∘ L) (p, x)‖ ≤
      ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ * ‖L‖ ^ (n - i) := by
    rw [L.iteratedFDeriv_comp_right (s.smooth ⊤) _ (by generalize n - i = j; exact_mod_cast le_top)]
    simpa [hLq] using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ (n - i) s (L (p, x))) (fun _ => L)
  have h3 : (1 + ‖x + l p‖) ^ (k + N) * ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + N, n)) le_rfl (Nat.sub_le _ _) s _
  have h4 := hN i hi' (p, x)
  have hc0 : 0 ≤ c := by positivity
  calc _ ≤ (c * (1 + ‖x + l p‖)) ^ k * ((n.choose i : ℝ) * (C₀ * (c * (1 + ‖x + l p‖)) ^ N) *
        (‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ * ‖L‖ ^ (n - i))) := by
        gcongr
        exact h4.trans (by gcongr)
    _ = (n.choose i : ℝ) * C₀ * c ^ (k + N) * ‖L‖ ^ (n - i) *
        ((1 + ‖x + l p‖) ^ (k + N) * ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖) := by
        simp only [mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr

end family

theorem temperate_exp : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => cexp (I * t)) = fun t : ℝ => I ^ n * cexp (I * t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have : HasDerivAt (fun t : ℝ => I ^ n * cexp (I * t)) (I ^ n * (cexp (I * t) * (I * 1))) t :=
        (((hasDerivAt_id (t : ℂ)).const_mul I).cexp.const_mul _).comp_ofReal
      rw [this.deriv]; ring
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n => ⟨0, 1, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

variable {κ : Type} [Fintype κ]

end GlobalTheory.CompanionTheory.OM.SchDiff

namespace GlobalTheory.CompanionTheory.OM

open SchDiff

end GlobalTheory.CompanionTheory.OM
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MembershipProofs.GoodCharIsLocallyConstant
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrLaw

theorem goodChar_isLocallyConstant {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) : IsLocallyConstant (ψ : R → ℂ) := by
  have hone : ∀ z : R, ((u⁻¹ : Rˣ) : R) * z ∈ O → ψ z = 1 := by
    intro z hz
    have hu : ∀ y ∈ O, ψ ((u : R) * y) = 1 :=
      (h.ann (u : R)).2 (by rw [Units.inv_mul]; exact O.one_mem)
    have := hu _ hz
    rwa [Units.mul_inv_cancel_left] at this
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | ((u⁻¹ : Rˣ) : R) * (y - x) ∈ O}, ?_, ?_, ?_⟩
  · exact h.isOpen.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  · simp only [Set.mem_ofPred_eq, sub_self, mul_zero]
    exact O.zero_mem
  · intro y hy
    have hy' : y = x + (y - x) := by abel
    rw [hy', AddChar.map_add_eq_mul, hone _ hy, mul_one]

theorem schr_law : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (w w' : W) (φ φ' : (κ → R) → ℂ), GoodChar ψ O u → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → d.rho ψ w (d.rho ψ w' φ) = ψ (⅟(2 : R) * B w w') • d.rho ψ (w + w') φ ∧ d.rho ψ 0 φ = φ ∧ (φ ∈ SB (κ → R) → d.rho ψ w φ ∈ SB (κ → R)) ∧ pair μ (d.rho ψ w φ) (d.rho ψ w φ') = pair μ φ φ' := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ w w' φ φ' hψ hμ
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  have hloc : IsLocallyConstant (ψ : R → ℂ) := goodChar_isLocallyConstant hψ
  have hdot : ∀ b : κ → R, Continuous fun x : κ → R => x ⬝ᵥ b := fun b =>
    continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add (f := _), Prod.fst_add, Prod.snd_add, d.form]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
    congr 2
    simp only [add_dotProduct, dotProduct_add]
    linear_combination (-((d.e w).1 ⬝ᵥ (d.e w').2)) * h2
  · funext x
    simp [Darboux.rho, schr]
  · intro hφ
    change IsLocallyConstant _ ∧ HasCompactSupport _ at hφ
    change IsLocallyConstant _ ∧ HasCompactSupport _
    refine ⟨?_, ?_⟩
    · exact (hloc.comp_continuous ((hdot _).add continuous_const)).mul
        (hφ.1.comp_continuous (continuous_id.add continuous_const))
    · exact (hφ.2.comp_homeomorph (Homeomorph.addRight (d.e w).1)).mul_left
  · let _ : MeasurableSpace (κ → R) := borel _
    have : BorelSpace (κ → R) := ⟨rfl⟩
    have : μ.IsAddHaarMeasure := hμ
    have hpt : ∀ x, (starRingEnd ℂ) (d.rho ψ w φ x) * d.rho ψ w φ' x =
        (starRingEnd ℂ) (φ ((d.e w).1 + x)) * φ' ((d.e w).1 + x) := by
      intro x
      simp only [Darboux.rho, schr, map_mul]
      have hn : (starRingEnd ℂ) (ψ (x ⬝ᵥ (d.e w).2 + ⅟(2 : R) * ((d.e w).1 ⬝ᵥ (d.e w).2))) *
          ψ (x ⬝ᵥ (d.e w).2 + ⅟(2 : R) * ((d.e w).1 ⬝ᵥ (d.e w).2)) = 1 := by
        rw [Complex.conj_mul', hψ.norm_one]
        simp
      rw [add_comm (d.e w).1 x]
      linear_combination ((starRingEnd ℂ) (φ (x + (d.e w).1)) * φ' (x + (d.e w).1)) * hn
    unfold pair
    simp_rw [hpt]
    exact integral_add_left_eq_self (fun x => (starRingEnd ℂ) (φ x) * φ' x) (d.e w).1

end GlobalTheory.CompanionTheory.SchrLaw
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MembershipProofs.DualNumberGraphFiltrationIsotropicOfSkew
open GlobalTheory.CompanionTheory.VacLoc ValuativeRel GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.VacLoc.GoodInh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem goodChar_of_hasConductor (χ : AddChar k Circle) (c : kˣ) (hχ : HasConductor χ c) :
    GoodChar (Circle.coeHom.compAddChar χ) 𝒪[k] c := by
  have hcoe : ∀ z, (Circle.coeHom.compAddChar χ) z = 1 ↔ χ z = 1 := fun z => by
    show ((χ z : Circle) : ℂ) = 1 ↔ _
    exact Circle.coe_eq_one
  refine ⟨fun x => ?_, IsNonarchimedeanLocalField.isCompact_closedBall k 1, Valuation.isOpen_integer,
    fun x => ?_, fun U hU => ?_, fun x => ?_⟩
  · show ‖((χ x : Circle) : ℂ)‖ = 1
    exact Circle.norm_coe _
  · have key : (∀ y ∈ 𝒪[k], (Circle.coeHom.compAddChar χ) (x * y) = 1) ↔
        ∀ y, ValuativeRel.valuation k y ≤ ValuativeRel.valuation k x → χ y = 1 := by
      simp only [hcoe]
      constructor
      · intro H y hy
        by_cases hx : x = 0
        · have h0 : ValuativeRel.valuation k y = 0 := by
            rw [hx, map_zero] at hy
            exact le_antisymm hy zero_le'
          rw [(Valuation.zero_iff _).1 h0, AddChar.map_zero_eq_one]
        · have hmem : x⁻¹ * y ∈ 𝒪[k] := by
            rw [Valuation.mem_integer_iff, map_mul]
            calc ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k y
                ≤ ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k x :=
                  mul_le_mul_of_nonneg_left hy zero_le'
              _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
          have h1 := H _ hmem
          rwa [mul_inv_cancel_left₀ hx] at h1
      · intro H y hy
        apply H
        rw [map_mul]
        calc ValuativeRel.valuation k x * ValuativeRel.valuation k y
            ≤ ValuativeRel.valuation k x * 1 :=
              mul_le_mul_of_nonneg_left ((Valuation.mem_integer_iff _ _).1 hy) zero_le'
          _ = ValuativeRel.valuation k x := mul_one _
    rw [key, hχ x, Valuation.mem_integer_iff, map_mul]
    constructor
    · intro hle
      calc ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k x
          ≤ ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k (c : k) :=
            mul_le_mul_of_nonneg_left hle zero_le'
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    · intro hle
      calc ValuativeRel.valuation k x
          = ValuativeRel.valuation k ((c : k) * (((c⁻¹ : kˣ) : k) * x)) := by
            rw [← mul_assoc, Units.mul_inv, one_mul]
        _ = ValuativeRel.valuation k (c : k) *
            ValuativeRel.valuation k (((c⁻¹ : kˣ) : k) * x) := map_mul _ _ _
        _ ≤ ValuativeRel.valuation k (c : k) * 1 := by
            rw [map_mul]
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ = ValuativeRel.valuation k (c : k) := mul_one _
  · obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).1 hU
    obtain ⟨δ, hδ0, hδ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
    obtain ⟨ϖ, hϖ⟩ := ValuativeRel.valuation_surjective (K := k) δ
    obtain ⟨z, hz⟩ := ValuativeRel.valuation_surjective (K := k)
      (γ : ValuativeRel.ValueGroupWithZero k)
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hz
      exact γ.ne_zero hz.symm
    have hϖ0 : ϖ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hϖ
      exact hδ0.ne hϖ
    refine ⟨Units.mk0 (z * ϖ) (mul_ne_zero hz0 hϖ0), fun y hy => hγ ?_⟩
    have hy' : ValuativeRel.valuation k y ≤ 1 := (Valuation.mem_integer_iff _ _).1 hy
    show ValuativeRel.valuation k (z * ϖ * y) < γ
    rw [map_mul, map_mul, hz, hϖ]
    calc (γ : ValuativeRel.ValueGroupWithZero k) * δ * ValuativeRel.valuation k y
        ≤ γ * δ * 1 := mul_le_mul_of_nonneg_left hy' zero_le'
      _ = γ * δ := mul_one _
      _ < γ * 1 := mul_lt_mul_of_pos_left hδ1 (zero_lt_iff.2 γ.ne_zero)
      _ = γ := mul_one _
  · by_cases hx : ValuativeRel.valuation k x ≤ 1
    · exact ⟨1, by simp, by simpa [Valuation.mem_integer_iff] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      refine ⟨(Units.mk0 x hx0)⁻¹, ?_, ?_⟩
      · rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, Units.val_mk0, Valuation.map_inv]
        exact (inv_le_one₀ ((Valuation.pos_iff _).2 hx0)).2 (le_of_lt (not_le.1 hx))
      · rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx0]
        exact one_mem _

theorem exists_goodChar :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      (∃ ψ : AddChar k ℂ, GoodChar ψ 𝒪[k] 1) ∧
      ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ x, ‖ψ x‖ = 1) → ψ ≠ 1 → ∃ u : kˣ, GoodChar ψ 𝒪[k] u := by
  intro k _ _ _ _
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  refine ⟨?_, fun ψ hψc hψn hψ1 => ?_⟩
  · obtain ⟨-, ⟨χ, -, -, hχ⟩, -⟩ := GlobalTheory.SplitWeil.conductor_exists k
    exact ⟨_, goodChar_of_hasConductor χ 1 hχ⟩
  · let χ : AddChar k Circle :=
      { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.2 (hψn x)⟩
        map_zero_eq_one' := Circle.ext (by simp)
        map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }
    have hχψ : Circle.coeHom.compAddChar χ = ψ := AddChar.ext _ _ fun x => rfl
    have hχc : Continuous χ := hψc.subtype_mk _
    have hχ1 : χ ≠ 1 := by
      intro h1
      apply hψ1
      rw [← hχψ, h1]
      exact AddChar.ext _ _ fun x => by simp
    obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
    exact ⟨c, hχψ ▸ goodChar_of_hasConductor χ c hc⟩

end GlobalTheory.CompanionTheory.VacLoc.GoodInh
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsEqMulApplyZero
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.WeilCoinv

theorem exists_dotProduct_ne_one {k : Type} [Field k] {κ : Type} [Fintype κ] {ψ : AddChar k ℂ} (hψ : ψ ≠ 1)
    {x : κ → k} (hx : x ≠ 0) : ∃ y : κ → k, ψ (x ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := hi
  refine ⟨Pi.single i (t / x i), ?_⟩
  have hxt : x i * (t / x i) = t := by field_simp
  rw [dotProduct_single, hxt]
  exact ht

theorem exists_eq_mul_apply_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ,
    (∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (0, y) φ) = l φ) → ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l φ = a * φ 0 := by
  intro k _ _ _ _ _ κ _ ψ hψc hψ l hl
  classical
  haveI : NonarchimedeanAddGroup k := GlobalTheory.WeilM.nonarch_field k
  haveI : NonarchimedeanAddGroup (κ → k) := GlobalTheory.WeilM.nonarch_pi k κ
  have hψlc : IsLocallyConstant ψ := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψc
  have hχ : ∀ y : κ → k, IsLocallyConstant (fun x : κ → k => ψ (x ⬝ᵥ y)) := fun y =>
    hψlc.comp_continuous (continuous_id.dotProduct continuous_const)
  have key : ∀ t : Finset (κ → k), ∀ φ ∈ SB (κ → k),
      (∀ x, φ x ≠ 0 → ∃ y ∈ t, ψ (x ⬝ᵥ y) ≠ 1) → l φ = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro φ _ h
      have hz : φ = 0 := funext fun x => by
        by_contra hx
        obtain ⟨y, hy, -⟩ := h x hx
        simp at hy
      rw [hz, map_zero]
    | @insert y t hyt ih =>
      intro φ hφ h
      obtain ⟨hφl, hφc⟩ := hφ
      obtain ⟨φ₁, hφ₁⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if ψ (x ⬝ᵥ y) = 1 then φ x else 0 := ⟨_, rfl⟩
      obtain ⟨g, hg⟩ : ∃ f : (κ → k) → ℂ,
          f = fun x => if ψ (x ⬝ᵥ y) = 1 then 0 else φ x / (ψ (x ⬝ᵥ y) - 1) := ⟨_, rfl⟩
      have hφ₁SB : φ₁ ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hφ₁]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then b else 0)
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hφ₁, h0]
      have hgSB : g ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hg]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then 0 else b / (a - 1))
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hg, h0]
      have hsch : schr ψ ((0 : κ → k), y) g = fun x => ψ (x ⬝ᵥ y) * g x := by
        funext x
        simp [GlobalTheory.WeilM.schr]
      have hdiff : φ = φ₁ + (schr ψ ((0 : κ → k), y) g - g) := by
        rw [hsch]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, hφ₁, hg]
        split_ifs with h1
        · simp
        · have hne : ψ (x ⬝ᵥ y) - 1 ≠ 0 := sub_ne_zero.mpr h1
          rw [zero_add, ← sub_one_mul]
          field_simp
      rw [hdiff, map_add (f := _), map_sub, hl y g hgSB, sub_self, add_zero]
      refine ih φ₁ hφ₁SB ?_
      intro x hx
      have hx1 : ψ (x ⬝ᵥ y) = 1 := by
        by_contra hne
        apply hx
        simp [hφ₁, hne]
      have hx2 : φ x ≠ 0 := by
        intro h0
        apply hx
        simp [hφ₁, h0]
      obtain ⟨y', hy', hy'ne⟩ := h x hx2
      rcases Finset.mem_insert.mp hy' with rfl | hy't
      · exact absurd hx1 hy'ne
      · exact ⟨y', hy't, hy'ne⟩
  have vanish : ∀ φ ∈ SB (κ → k), φ 0 = 0 → l φ = 0 := by
    intro φ hφ h0
    obtain ⟨hφl, hφc⟩ := hφ
    have hsupp : IsClosed (Function.support φ) := (hφl.isOpen_fiber 0).isClosed_compl
    have hK : IsCompact (Function.support φ) := by
      have hc := hφc.isCompact
      rwa [tsupport, hsupp.closure_eq] at hc
    have hcov : Function.support φ ⊆ ⋃ y : κ → k, {x | ψ (x ⬝ᵥ y) ≠ 1} := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx h0
      obtain ⟨y, hy⟩ := exists_dotProduct_ne_one hψ hx0
      exact Set.mem_iUnion.mpr ⟨y, hy⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : κ → k => {x | ψ (x ⬝ᵥ y) ≠ 1})
      (fun y => ((hχ y).isClosed_fiber 1).isOpen_compl) hcov
    refine key t φ ⟨hφl, hφc⟩ ?_
    intro x hx
    have hxt := ht hx
    simp only [Set.mem_iUnion] at hxt
    obtain ⟨y, hy, hxy⟩ := hxt
    exact ⟨y, hy, hxy⟩
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : κ → k)
  obtain ⟨O, hO⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  have hOc : IsCompact (O : Set (κ → k)) := hC.of_isClosed_subset O.isClosed hO
  have hO0 : (0 : κ → k) ∈ O := O.zero_mem
  obtain ⟨φ₀, hφ₀d⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if x ∈ O then 1 else 0 := ⟨_, rfl⟩
  have hφ₀ : φ₀ ∈ SB (κ → k) := by
    refine ⟨?_, HasCompactSupport.intro' hOc O.isClosed fun x hx => ?_⟩
    · rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ O
      · refine ⟨O, O.isOpen, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∈ O := hx'
        simp [hφ₀d, hx, hx'']
      · refine ⟨(O : Set (κ → k))ᶜ, O.isClosed.isOpen_compl, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∉ O := hx'
        simp [hφ₀d, hx, hx'']
    · have hx' : x ∉ O := hx
      simp [hφ₀d, hx']
  refine ⟨l φ₀, fun φ hφ => ?_⟩
  have h1 : φ - φ 0 • φ₀ ∈ SB (κ → k) := Submodule.sub_mem _ hφ (Submodule.smul_mem _ _ hφ₀)
  have h2 : (φ - φ 0 • φ₀) 0 = 0 := by simp [hφ₀d, hO0]
  have h3 := vanish _ h1 h2
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h3
  rw [h3, mul_comm]

end GlobalTheory.CompanionTheory.WeilCoinv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MembershipProofs.CharacterAugmentationSubspaceQuotientActionTop
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WittOrbit

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}

theorem int_mul {l m n : Type} [Fintype m] {X : Matrix l m E} {Y : Matrix m n E} (hX : ∀ i j, X i j ∈ A)
    (hY : ∀ i j, Y i j ∈ A) : ∀ i j, (X * Y) i j ∈ A := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem int_map {m n : Type} {X : Matrix m n E} (hs : ∀ z ∈ A, c z ∈ A) (hX : ∀ i j, X i j ∈ A) :
    ∀ i j, (X.map c) i j ∈ A := by
  intro i j
  rw [Matrix.map_apply]
  exact hs _ (hX i j)

theorem map_map_eq {m n : Type} (hc : ∀ z, c (c z) = z) (X : Matrix m n E) : (X.map c).map c = X := by
  ext i j; simp [hc]

theorem map_mul' {l m n : Type} [Fintype m] (X : Matrix l m E) (Y : Matrix m n E) :
    (X * Y).map c = X.map c * Y.map c :=
  Matrix.map_mul

end

end GlobalTheory.CompanionTheory.WittOrbit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ResCardAndUniformizer
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.IdxAd.Unif

theorem resCard_and_uniformizer : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Ideal.absNorm v.asIdeal ∧ ∃ ϖ : (v.adicCompletion F)ˣ, (∃ p : 𝒪[v.adicCompletion F], Irreducible p ∧ (p : v.adicCompletion F) = ϖ) ∧ ∀ t : (v.adicCompletion F)ˣ, ∃ (a : ℤ) (u : (v.adicCompletion F)ˣ), (u : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ t = u * ϖ ^ a ∧ a.natAbs = (WithZero.log (Valued.v (t : v.adicCompletion F))).natAbs := by
  intro F _ _ v
  have hS : (Valuation.integer (ValuativeRel.valuation (v.adicCompletion F))) =
      (v.adicCompletionIntegers F).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F := RingEquiv.subringCongr hS
  have hle : ∀ {x : v.adicCompletion F}, Valued.v x ≤ 1 → x ∈ 𝒪[v.adicCompletion F] := fun hx =>
    (GroundTheory.Global.mem_valuationInteger_iff v _).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).2 hx)
  refine ⟨?_, ?_⟩
  · have h := GroundTheory.Global.natCard_residueField_adicCompletionIntegers (K := F) v
    rw [← h]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  · obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
    have hval : Valued.v (q : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      GroundTheory.Global.valued_of_irreducible v hq
    have hq0 : (q : v.adicCompletion F) ≠ 0 := fun h => hq.ne_zero (Subtype.ext h)
    have hp : Irreducible (e.symm q) :=
      (MulEquiv.irreducible_iff e.symm).2 hq
    refine ⟨Units.mk0 _ hq0, ⟨_, hp, rfl⟩, fun t => ?_⟩
    have ht : Valued.v (t : v.adicCompletion F) ≠ 0 :=
      (Valued.v).ne_zero_iff.2 t.ne_zero
    set a : ℤ := - WithZero.log (Valued.v (t : v.adicCompletion F)) with ha
    have hu : Valued.v (((t * (Units.mk0 _ hq0) ^ (-a) : (v.adicCompletion F)ˣ)) :
        v.adicCompletion F) = 1 := by
      rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hval,
        ← WithZero.exp_zsmul, ← WithZero.exp_log ht, ← WithZero.exp_add, smul_eq_mul, ha]
      simp
    refine ⟨a, t * (Units.mk0 _ hq0) ^ (-a), hle hu.le, hle ?_, ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    · simp [mul_assoc]
    · rw [ha, Int.natAbs_neg]

end GlobalTheory.CompanionTheory.IdxAd.Unif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MembershipProofs.NormIteratedFDerivCexpCompLe
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff Nat

namespace GlobalTheory.CompanionTheory.OM

namespace GaussSch

theorem one_add_pow_mul_exp_le {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ Real.exp (N ^ 2 / (4 * c)) := by
  have h1 : (1 + r) ^ N ≤ Real.exp r ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
  calc (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ Real.exp r ^ N * Real.exp (-c * r ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (N * r + -c * r ^ 2) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (N ^ 2 / (4 * c)) := by
        apply Real.exp_le_exp.2
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]

theorem norm_iteratedFDeriv_cexp (i : ℕ) (y : ℂ) :
    ‖iteratedFDeriv ℝ i cexp y‖ = Real.exp y.re := by
  rw [← ((Complex.contDiff_exp : ContDiff ℂ (i : WithTop ℕ∞) cexp).contDiffAt (x := y)).restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp,
    Complex.norm_exp]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_cexp_comp_le {q : E → ℂ} (hq : q.HasTemperateGrowth) (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (q x).re := by
  obtain ⟨m, K, hK, hbd⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * (max K 1) ^ n, m * n, by positivity, fun x ↦ ?_⟩
  have h1x : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hD1 : 1 ≤ max K 1 * (1 + ‖x‖) ^ m :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ h1x)
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i q x‖ ≤ (max K 1 * (1 + ‖x‖) ^ m) ^ i := by
    intro i hi hin
    calc ‖iteratedFDeriv ℝ i q x‖ ≤ K * (1 + ‖x‖) ^ m := hbd i hin x
      _ ≤ max K 1 * (1 + ‖x‖) ^ m := by gcongr; exact le_max_left _ _
      _ = (max K 1 * (1 + ‖x‖) ^ m) ^ 1 := (pow_one _).symm
      _ ≤ (max K 1 * (1 + ‖x‖) ^ m) ^ i := pow_le_pow_right₀ hD1 hi
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i cexp (q x)‖ ≤ Real.exp (q x).re :=
    fun i _ => (norm_iteratedFDeriv_cexp i (q x)).le
  calc ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
      ≤ n ! * Real.exp (q x).re * (max K 1 * (1 + ‖x‖) ^ m) ^ n :=
        norm_iteratedFDeriv_comp_le (N := n) Complex.contDiff_exp (hq.1.of_le (mod_cast le_top))
          le_rfl x hC hD
    _ = n ! * (max K 1) ^ n * (1 + ‖x‖) ^ (m * n) * Real.exp (q x).re := by
        rw [mul_pow, ← pow_mul]; ring

def cexpSchwartz {q : E → ℂ} (hq : q.HasTemperateGrowth) {c : ℝ} (hc : 0 < c)
    (hre : ∀ x, (q x).re ≤ -c * ‖x‖ ^ 2) : SchwartzMap E ℂ where
  toFun := cexp ∘ q
  smooth' := Complex.contDiff_exp.comp hq.1
  decay' k n := by
    obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_cexp_comp_le hq n
    refine ⟨C * Real.exp ((k + j : ℕ) ^ 2 / (4 * c)), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    have he : Real.exp (q x).re ≤ Real.exp (-c * ‖x‖ ^ 2) := Real.exp_le_exp.2 (hre x)
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ j * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul hk ((hb x).trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (-c * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * Real.exp ((k + j : ℕ) ^ 2 / (4 * c)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_le hc (norm_nonneg x) _) hC

variable {κ : Type} [Fintype κ]

end GaussSch

end GlobalTheory.CompanionTheory.OM

end
end
