module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Sd
open scoped Matrix

namespace UpperTheory.V.Af.Nf

variable {F : Type} [Field F] [NumberField F]

private def sInt (w : HeightOneSpectrum (𝓞 F)) : w.adicCompletionIntegers F →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w x, Subring.mem_iInf.2 fun v => by
    classical
    change Pi.single (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w (x : w.adicCompletion F) v ∈
      v.adicCompletionIntegers F
    by_cases hv : v = w
    · subst hv
      rw [Pi.single_eq_same]
      exact x.2
    · rw [Pi.single_eq_of_ne hv]
      exact zero_mem _⟩
  map_mul' x y := Subtype.ext (map_mul (sLoc F w) _ _)
  map_zero' := Subtype.ext (map_zero (sLoc F w))
  map_add' x y := Subtype.ext (map_add (sLoc F w) _ _)

private theorem val_le (w : HeightOneSpectrum (𝓞 F)) (c : ℕ) (x : w.adicCompletionIntegers F)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) :
    Valued.v (x : w.adicCompletion F) ≤ WithZero.exp (-(c : ℤ)) := by
  induction c generalizing x with
  | zero => exact x.2
  | succ c ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) fun a b ha hb => ?_
    · have h1 : Valued.v (b : w.adicCompletion F) < 1 :=
        (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).1 hb
      have h2 : Valued.v (b : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
        generalize Valued.v (b : w.adicCompletion F) = t at h1
        induction t using WithZero.expRecOn with
        | zero => exact zero_le
        | exp n =>
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
          rw [WithZero.exp_le_exp]
          omega
      have h3 : WithZero.exp (-((c + 1 : ℕ) : ℤ)) = WithZero.exp (-(c : ℤ)) * WithZero.exp (-1 : ℤ) := by
        rw [← WithZero.exp_add]
        congr 1
        push_cast
        ring
      rw [h3]
      exact (map_mul _ (a : w.adicCompletion F) b).le.trans (mul_le_mul' (ih a ha) h2)
    · exact (Valuation.map_add_le _ ha hb)

private theorem nat_dvd (w : HeightOneSpectrum (𝓞 F)) {M : ℕ} (hM : 1 ≤ M) (x : w.adicCompletionIntegers F)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ ordI w (Ideal.span {(M : 𝓞 F)})) :
    (M : w.adicCompletionIntegers F) ∣ x := by
  have hM0 : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : Valued.v (M : w.adicCompletion F) = WithZero.exp (-(ordI w (Ideal.span {(M : 𝓞 F)}) : ℤ)) := by
    have : (M : w.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F M) := by simp
    rw [this]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (algebraMap (𝓞 F) F M)
    refine h2.trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hM0]
    rfl
  have h0 : (M : w.adicCompletion F) ≠ 0 := fun h => by
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  refine ⟨⟨(M : w.adicCompletion F)⁻¹ * x, ?_⟩, Subtype.ext ?_⟩
  · change Valued.v ((M : w.adicCompletion F)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, h1]
    exact (inv_mul_le_one₀ WithZero.exp_pos).2 (val_le w _ x hx)
  · simp [h0]

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.kLocal :
    UpperTheory.V.Af.Nf.KLocal := by
  rintro M hM w _ ⟨k, hk, rfl⟩
  refine ⟨cornerGL 2 (sInt w) k, ?_, ?_⟩
  · refine funext fun j => ?_
    have h0 : ![0, 1] ᵥ* (k.val.map (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ lev M w))) = ![0, 1] := hk
    have h1 := congrFun h0 j
    have h2 : k 1 j - (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) 1 j ∈
        IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ lev M w := by
      rw [← Ideal.Quotient.eq]
      fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] using h1
    obtain ⟨y, hy⟩ := nat_dvd w hM _ h2
    have h3 : (cornerGL 2 (sInt w) k) 1 j - (1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) 1 j ∈ Ideal.span {(M : ↥(Ohat ℚ))} := by
      have h4 : (cornerGL 2 (sInt w) k) 1 j = (1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) 1 j -
          sInt w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) 1 j) + sInt w (k 1 j) := rfl
      rw [h4, sub_add_eq_add_sub, add_sub_assoc, add_sub_cancel_left, ← map_sub, hy, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [← Ideal.Quotient.eq] at h3
    fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] using h3
  · ext i j : 2
    change ((1 : Matrix (Fin 2) (Fin 2) (Ohat ℚ)) i j : Af ℚ) -
        sLoc ℚ w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers ℚ)) i j) + sLoc ℚ w _ =
      (1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j - sLoc ℚ w ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) + sLoc ℚ w _
    by_cases h : i = j
    · subst h
      simp only [Matrix.one_apply_eq]
      rfl
    · simp only [Matrix.one_apply_ne h]
      rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AvgZero
open MeasureTheory
open scoped Pointwise

theorem UpperTheory.V.Af.Nf.avgZero :
    UpperTheory.V.Af.Nf.AvgZero := by
  intro G _ _ _ _ _ _ _ Γ _ μ 𝓕 hμ h𝓕 ψ hψ hinv e he N hN havg
  by_cases hint : IntegrableOn ψ 𝓕 μ
  swap
  · exact integral_undef hint
  have hΓ : ∀ (g : Γ) (x : G), ψ (g +ᵥ x) = ψ x := fun g x => hinv g g.2 x
  have hF : ∀ a : G, IsAddFundamentalDomain Γ ((fun x => a + x) '' 𝓕) μ := fun a => h𝓕.vadd_of_comm a
  have hmp : ∀ a : G, MeasurePreserving (fun x => a + x) μ μ := fun a => measurePreserving_add_left μ a
  have hem : ∀ a : G, MeasurableEmbedding (fun x : G => a + x) := fun a => measurableEmbedding_addLeft a
  have h1 : ∀ a : G, ∫ x in 𝓕, ψ (a + x) ∂μ = ∫ x in 𝓕, ψ x ∂μ := fun a => by
    rw [← (hmp a).setIntegral_image_emb (hem a) ψ 𝓕]
    exact (hF a).setIntegral_eq h𝓕 hΓ
  have h2 : ∀ a : G, ∫ x in 𝓕, ‖ψ (a + x)‖ ∂μ = ∫ x in 𝓕, ‖ψ x‖ ∂μ := fun a => by
    rw [← (hmp a).setIntegral_image_emb (hem a) (fun x => ‖ψ x‖) 𝓕]
    exact (hF a).setIntegral_eq h𝓕 fun g x => by rw [hΓ]
  have h3 : ∀ a : G, IntegrableOn (fun x => ψ (a + x)) 𝓕 μ := fun a =>
    ((hmp a).integrableOn_image (hem a)).1 (((hF a).integrableOn_iff h𝓕 hΓ).2 hint)
  have hc : Continuous (Function.uncurry fun (t : ℝ) (x : G) => ψ (e t + x)) :=
    hψ.comp ((he.comp continuous_fst).add continuous_snd)
  have hI : Integrable (Function.uncurry fun (t : ℝ) (x : G) => ψ (e t + x))
      ((volume.restrict (Set.Ioc (0 : ℝ) N)).prod (μ.restrict 𝓕)) := by
    rw [integrable_prod_iff hc.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => h3 (e t), ?_⟩
    simp only [Function.uncurry_apply_pair, h2]
    exact integrable_const _
  have hs := integral_integral_swap hI
  simp only [h1, ← intervalIntegral.integral_of_le hN.le, havg, integral_zero, intervalIntegral.integral_const,
    sub_zero, smul_eq_zero, hN.ne', false_or] at hs
  exact hs
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchSm
open UpperHalfPlane hiding I
open scoped Manifold ContDiff

private theorem archSm_eval_eq (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f) (σ : ℂ)
    (x0 : Fin 2 → Fin 2 → ℝ)
    (hD : x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0 ≠ 0)
    (hc : ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) ≠ 0)
    (him : 0 < (σ * (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))).im) :
    ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((|x 0 0 * x 1 1 - x 0 1 * x 1 0| ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-(k : ℤ)) *
        f (ofComplex (σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
          ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))))) x0 := by
  have hre : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ => ((x i j : ℝ) : ℂ)) :=
    fun i j => Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have hDd : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
    fun_prop
  have hcd : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) :=
    ((hre 1 0).mul contDiff_const).add (hre 1 1)
  have had : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      (x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) :=
    ((hre 0 0).mul contDiff_const).add (hre 0 1)
  have habs : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      |x 0 0 * x 1 1 - x 0 1 * x 1 0|) x0 :=
    ContDiffAt.comp (g := fun t : ℝ => |t|) x0 (contDiffAt_abs hD) hDd.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((|x 0 0 * x 1 1 - x 0 1 * x 1 0| ^ ((k : ℝ) / 2) : ℝ) : ℂ)) x0 := by
    refine Complex.ofRealCLM.contDiff.contDiffAt.comp x0 ?_
    exact habs.rpow_const_of_ne (abs_ne_zero.mpr hD)
  have h2 : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-(k : ℤ))) x0 := by
    have hz : AnalyticAt ℂ (fun z : ℂ => z ^ (-(k : ℤ)))
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
      (differentiableOn_zpow (-(k : ℤ)) _ (by tauto)).analyticOnNhd isOpen_compl_singleton _ hc
    exact (hz.contDiffAt.restrict_scalars ℝ).comp x0 hcd.contDiffAt
  have hinv : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-1 : ℤ)) x0 := by
    have hz : AnalyticAt ℂ (fun z : ℂ => z ^ (-1 : ℤ))
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
      (differentiableOn_zpow (-1 : ℤ) _ (by tauto)).analyticOnNhd isOpen_compl_singleton _ hc
    exact ContDiffAt.comp (g := fun z : ℂ => z ^ (-1 : ℤ))
      (f := fun x : Fin 2 → Fin 2 → ℝ =>
        (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) x0
      (hz.contDiffAt.restrict_scalars ℝ) hcd.contDiffAt
  have hw : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))) x0 := by
    simp only [div_eq_mul_inv, ← zpow_neg_one]
    exact contDiffAt_const.mul (had.contDiffAt.mul hinv)
  have hF : AnalyticAt ℂ (f ∘ ofComplex) (σ * (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) +
      (x0 0 1 : ℂ)) / ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))) :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet _ him
  have h3 := ContDiffAt.comp (g := f ∘ ofComplex) (f := fun x : Fin 2 → Fin 2 → ℝ =>
      σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))) x0
    (hF.contDiffAt.restrict_scalars ℝ) hw
  exact (h1.mul h2).mul h3

theorem UpperTheory.V.Af.Nf.archSm :
    UpperTheory.V.Af.Nf.ArchSm := by
  intro k f hf
  have hD : ∀ x : Fin 2 → Fin 2 → ℝ,
      (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
    intro x
    simp [Matrix.det_fin_two]
  have hDc : Continuous (fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
    fun_prop
  intro x0 hx0
  refine ContDiffAt.contDiffWithinAt ?_
  have hx0' : x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0 ≠ 0 := by
    simpa [hD] using hx0
  have hc : ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    apply hx0'
    rw [h1, h2]
    ring
  have hsign : ∀ᶠ x in nhds x0, SignType.sign (x 0 0 * x 1 1 - x 0 1 * x 1 0) =
      SignType.sign (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) := by
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · filter_upwards [hDc.continuousAt.eventually (gt_mem_nhds hneg)] with x hx
      rw [sign_neg hx, sign_neg hneg]
    · filter_upwards [hDc.continuousAt.eventually (lt_mem_nhds hpos)] with x hx
      rw [sign_pos hx, sign_pos hpos]
  have hq : (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
      ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ))).im =
      (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) /
        Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) := by
    rw [Complex.div_im]
    simp
    ring
  have hn : 0 < Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
    Complex.normSq_pos.mpr hc
  have him : 0 < ((((SignType.sign (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) : ℝ)) : ℂ) *
      (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hq]
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · rw [sign_neg hneg]
      have : (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) /
          Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) < 0 :=
        div_neg_of_neg_of_pos hneg hn
      simp only [SignType.coe_neg, SignType.coe_one]
      linarith
    · rw [sign_pos hpos]
      simp only [SignType.coe_one, one_mul]
      exact div_pos hpos hn
  refine (archSm_eval_eq k f hf _ x0 hx0' hc him).congr_of_eventuallyEq ?_
  filter_upwards [hsign] with x hx
  unfold UpperTheory.V.Af.Nf.arch UpperTheory.V.Af.Nf.nsl
  rw [hD, hx]
  simp only [Matrix.of_apply]
end
