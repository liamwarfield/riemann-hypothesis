module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleExistsNonzero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniform

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantWeightShiftAsymptoticLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoBergmanMeasureChernFormPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BergmanFunctionTotalMassExtremal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BergmanFunctionTotalMassExtremal
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp.BergProof

lemma sum_eq_dot {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (w : ι → ℂ) :
    ∑ i, ∑ j, H j i * (w i * (starRingEnd ℂ) (w j)) = star w ⬝ᵥ (H *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring)

lemma berg_eq {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (σ : S) (y : Y σ) :
    bergmanDensity μ v σ y = (star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y)).re := by
  rw [bergmanDensity, sum_eq_dot]

lemma ofReal_re_of_nonneg {z : ℂ} (h : 0 ≤ z) : ((z.re : ℝ) : ℂ) = z := by
  have h' := Complex.le_def.mp h
  apply Complex.ext <;> simp [h'.2.symm]

end GlobalTheory.HSAmp.BergProof


open GlobalTheory.HSAmp.BergProof in
theorem GlobalTheory.HSAmp.berg_mass_extremal : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → (∀ σ, Integrable (bergmanDensity μ v σ) (μ σ)) ∧ ∑ᶠ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = Fintype.card ι ∧ (∀ σ y, 0 ≤ bergmanDensity μ v σ y) ∧ ∀ σ y (M : ℝ), 0 ≤ M → (∀ c : ι → ℂ, cmb v c σ y ≤ M * l2 μ v c) → bergmanDensity μ v σ y ≤ M := by
  intro S Y _ ι _ _ μ v hF hG
  obtain ⟨hHerm, hl2⟩ := GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form S Y ι μ v hF
  have hH : ((gram μ v)⁻¹).PosDef := hG.inv
  have hu : IsUnit (gram μ v).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hGH : gram μ v * (gram μ v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hHG : (gram μ v)⁻¹ * gram μ v = 1 := Matrix.nonsing_inv_mul _ hu
  have hHh : ((gram μ v)⁻¹).IsHermitian := hH.isHermitian
  have hnn : ∀ σ y, 0 ≤ star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y) := fun σ y =>
    hH.posSemidef.dotProduct_mulVec_nonneg _
  have key : ∀ σ y, (bergmanDensity μ v σ y : ℂ) = star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y) := fun σ y => by
    rw [berg_eq]; exact ofReal_re_of_nonneg (hnn σ y)
  have hpos : ∀ σ y, 0 ≤ bergmanDensity μ v σ y := fun σ y => by
    rw [berg_eq]; exact (Complex.le_def.mp (hnn σ y)).1
  have hint : ∀ σ, Integrable (fun y => ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun σ => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _
  refine ⟨fun σ => (hint σ).re, ?_, hpos, ?_⟩
  · haveI : Finite S := hF.finite
    haveI := Fintype.ofFinite S
    have hσ : ∀ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ =
        (∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ).re := fun σ => by
      have e1 : ∫ y, bergmanDensity μ v σ y ∂μ σ =
          RCLike.re (∫ y, ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) ∂μ σ) :=
        integral_re (hint σ)
      rw [e1, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]
      change Complex.re _ = Complex.re _
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    have hsum : ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j = (Fintype.card ι : ℂ) := by
      rw [Finset.sum_comm]
      have : ∀ j, ∑ i, (gram μ v)⁻¹ j i * gram μ v i j = ((gram μ v)⁻¹ * gram μ v) j j :=
        fun j => (Matrix.mul_apply).symm
      simp only [this, hHG, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [finsum_eq_sum_of_fintype]
    simp only [hσ]
    rw [← Complex.re_sum]
    have hg : ∀ i j, gram μ v i j = ∑ σ, ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := fun i j => by
      rw [gram, Matrix.of_apply, finsum_eq_sum_of_fintype]
    have hswap : ∑ σ, ∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ =
        ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j := by
      simp only [hg, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hswap, hsum, Complex.natCast_re]
  · intro σ y M hM h
    set w := v σ y with hw
    set u := (gram μ v)⁻¹ *ᵥ w with hu'
    have hB := key σ y
    rw [← hw] at hB
    have hdot : star u ⬝ᵥ w = star w ⬝ᵥ ((gram μ v)⁻¹ *ᵥ w) := by
      rw [hu', Matrix.star_mulVec, hHh.eq, ← Matrix.dotProduct_mulVec]
    have hc : cmb v (star u) σ y = bergmanDensity μ v σ y ^ 2 := by
      have : ∑ i, star u i * v σ y i = (bergmanDensity μ v σ y : ℂ) := by
        rw [hB, ← hdot]; rfl
      rw [cmb, this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hl : l2 μ v (star u) = bergmanDensity μ v σ y := by
      apply Complex.ofReal_injective
      rw [(hl2 (star u)).2.2, hB, ← hdot]
      have hGu : gram μ v *ᵥ u = w := by
        rw [hu', Matrix.mulVec_mulVec, hGH, Matrix.one_mulVec]
      conv_rhs => rw [← hGu]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 := h (star u)
    rw [hc, hl] at h2
    have h0 := hpos σ y
    nlinarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BergmanFunctionTotalMassExtremalStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bergman_function_total_mass_extremal : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → (∀ σ, Integrable (bergmanDensity μ v σ) (μ σ)) ∧ ∑ᶠ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = Fintype.card ι ∧ (∀ σ y, 0 ≤ bergmanDensity μ v σ y) ∧ ∀ σ y (M : ℝ), 0 ≤ M → (∀ c : ι → ℂ, cmb v c σ y ≤ M * l2 μ v c) → bergmanDensity μ v σ y ≤ M := by
  first | exact @GlobalTheory.HSAmp.berg_mass_extremal | exact GlobalTheory.HSAmp.berg_mass_extremal | (intros; apply GlobalTheory.HSAmp.berg_mass_extremal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFinsumIntegralWeightSubLe
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem abs_integral_weight_sub_le_one {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (B β w : Y → ℝ) (C : ℝ) (hB : Integrable B μ) (hβ : Integrable β μ) (hle : ∀ y, B y ≤ β y)
    (hw : Measurable w) (hC : ∀ y, |w y| ≤ C) :
    |∫ y, w y * B y ∂μ - ∫ y, w y * β y ∂μ| ≤ C * (∫ y, β y ∂μ - ∫ y, B y ∂μ) := by
  have hwm : AEStronglyMeasurable w μ := hw.aestronglyMeasurable
  have hb : ∀ᵐ y ∂μ, ‖w y‖ ≤ C := Eventually.of_forall fun y => by simpa using hC y
  have h1 : Integrable (fun y => w y * B y) μ := hB.bdd_mul hwm hb
  have h2 : Integrable (fun y => w y * β y) μ := hβ.bdd_mul hwm hb
  rw [← integral_sub h1 h2, ← integral_sub hβ hB, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono (h1.sub h2).abs ((hβ.sub hB).const_mul C) fun y => ?_
  have h3 : 0 ≤ β y - B y := sub_nonneg.2 (hle y)
  show |w y * B y - w y * β y| ≤ C * (β y - B y)
  rw [← mul_sub, abs_mul, abs_sub_comm, abs_of_nonneg h3]
  exact mul_le_mul_of_nonneg_right (hC y) h3

theorem abs_finsum_integral_weight_sub_le :
    ∀ (S : Type) [Finite S] (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (μ : ∀ σ, Measure (Y σ)) (B β w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Integrable (B σ) (μ σ)) → (∀ σ, Integrable (β σ) (μ σ)) → (∀ σ y, B σ y ≤ β σ y) → (∀ σ, Measurable (w σ)) → 0 ≤ C → (∀ σ y, |w σ y| ≤ C) → |∑ᶠ σ, ∫ y, w σ y * B σ y ∂μ σ - ∑ᶠ σ, ∫ y, w σ y * β σ y ∂μ σ| ≤ C * (∑ᶠ σ, ∫ y, β σ y ∂μ σ - ∑ᶠ σ, ∫ y, B σ y ∂μ σ) := by
  intro S _ Y _ μ B β w C hB hβ hle hw _ hC
  haveI := Fintype.ofFinite S
  simp only [finsum_eq_sum_of_fintype]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  exact abs_integral_weight_sub_le_one (μ σ) (B σ) (β σ) (w σ) C (hB σ) (hβ σ) (hle σ) (hw σ) (hC σ)

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoBergmanMeasureChernFormPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem tendsto_of_abs_sub_le_eventually (a q : ℕ → ℝ) (I G W V C : ℝ) (hC : 0 ≤ C) (hq : Tendsto q atTop (𝓝 G))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, |a m - I - ε * W| ≤ C * (G + ε * V - q m)) : Tendsto a atTop (𝓝 I) := by
  rw [Metric.tendsto_nhds]
  intro e he
  have hK : 0 < |W| + C * |V| + 1 := by positivity
  set ε := e / (2 * (|W| + C * |V| + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hq' := Metric.tendsto_nhds.1 hq (e / (2 * (C + 1))) (by positivity)
  filter_upwards [h ε hε0, hq'] with m hm hqm
  rw [Real.dist_eq] at hqm ⊢
  have h1 : |a m - I| ≤ |a m - I - ε * W| + ε * |W| := by
    have := abs_add_le (a m - I - ε * W) (ε * W)
    rw [abs_mul, abs_of_pos hε0] at this
    simpa using this
  have h2 : C * (G + ε * V - q m) ≤ C * |q m - G| + C * (ε * |V|) := by
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have := neg_abs_le (q m - G)
    have := le_abs_self V
    nlinarith
  have h3 : C * |q m - G| ≤ (C + 1) * |q m - G| := by nlinarith [abs_nonneg (q m - G)]
  have h4 : (C + 1) * |q m - G| < e / 2 := by
    have := mul_lt_mul_of_pos_left hqm (by linarith : (0:ℝ) < C + 1)
    rwa [mul_div_assoc', mul_comm 2 (C + 1), ← div_div, mul_div_cancel_left₀ _ (by linarith : (C + 1) ≠ 0)] at this
  have h5 : ε * (|W| + C * |V|) < e / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg W, abs_nonneg V]
  nlinarith

end GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem tendsto_finsum_integral_berg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ w : ∀ σ, CxPts p σ → ℝ, (∀ σ, Continuous (w σ)) → Tendsto (fun m : ℕ => (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas) / (m : ℝ) ^ D) atTop (𝓝 (chInt P.L D w / D.factorial)) := by
  intro k _ X _ p D hX hG P hpos ω r f hf hli hr w hw
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hcpt : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hfm : ∀ σ, IsFiniteMeasure (ω σ).meas := fun σ => (GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hG σ (ω σ)).1
  choose ρ hρR hρ0 hρint using fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hG P.L hpos σ (ω σ)
  have hbd : ∀ σ (g : CxPts p σ → ℝ), Continuous g → ∃ C, ∀ y, |g y| ≤ C := fun σ g hg => by
    haveI := hcpt σ
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  have hint : ∀ σ (g : CxPts p σ → ℝ), Continuous g → Integrable g (ω σ).meas := fun σ g hg => by
    haveI := hfm σ
    obtain ⟨C, hC⟩ := hbd σ g hg
    exact Integrable.of_bound hg.aestronglyMeasurable C
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  choose Cw hCw using fun σ => hbd σ (w σ) (hw σ)
  set C : ℝ := ∑ σ, |Cw σ| with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hwC : ∀ σ y, |w σ y| ≤ C := fun σ y => (hCw σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |Cw σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set Iw : ℝ := ∑ σ, ∫ y, w σ y * ρ σ y ∂(ω σ).meas with hIw
  set G' : ℝ := ∑ σ, ∫ y, ρ σ y ∂(ω σ).meas with hG'
  set W : ℝ := ∑ σ, ∫ y, w σ y ∂(ω σ).meas with hW
  set V : ℝ := ∑ σ, ∫ _y, (1 : ℝ) ∂(ω σ).meas with hV
  have hch : chInt P.L D w = Iw := by
    simp only [chInt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hρint σ (w σ) (hw σ)
  have hgd : gdeg P.L D = G' := by
    simp only [gdeg, chInt, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hρint σ _ continuous_const]
    simp
  rw [hch]
  rw [hgd] at hr
  refine tendsto_of_abs_sub_le_eventually _ (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) (Iw / D.factorial)
    (G' / D.factorial) W V C hC0 hr fun ε hε => ?_
  filter_upwards [GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hG P hpos ω ρ hρR ε hε, eventually_ge_atTop 1] with m hmo hm1
  obtain ⟨hfam, hpd, -⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  obtain ⟨hBi, hBs, hB0, hBx⟩ := GlobalTheory.T.bergman_function_total_mass_extremal (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m))
    (fun σ => (ω σ).meas) (vals P m 1 (f m)) hfam hpd
  set M : ℝ := (m : ℝ) ^ D with hMdef
  have hM : 0 < M := pow_pos (by exact_mod_cast hm1) D
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hle : ∀ σ y, bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ≤ (ρ σ y / D.factorial + ε) * M :=
    fun σ y => hBx σ y _ (mul_nonneg (add_nonneg (div_nonneg (hρ0 σ y) hDf.le) hε.le) hM.le)
      fun c => hmo (Fin (r m)) (f m) (hf m) c σ y
  have hβi : ∀ σ, Integrable (fun y => (ρ σ y / D.factorial + ε) * M) (ω σ).meas := fun σ => by
    haveI := hfm σ
    exact (((hint σ _ (hρR σ).1).div_const _).add (integrable_const ε)).mul_const M
  have hl1 := abs_finsum_integral_weight_sub_le (k →+* ℂ) (fun σ => CxPts p σ) (fun σ => (ω σ).meas)
    (bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m))) (fun σ y => (ρ σ y / D.factorial + ε) * M) w C hBi hβi hle
    (fun σ => (hw σ).measurable) hC0 hwC
  have e1 : ∀ σ, ∫ y, w σ y * ((ρ σ y / D.factorial + ε) * M) ∂(ω σ).meas =
      M / D.factorial * ∫ y, w σ y * ρ σ y ∂(ω σ).meas + M * ε * ∫ y, w σ y ∂(ω σ).meas := fun σ => by
    have h1 : Integrable (fun y => w σ y * ρ σ y) (ω σ).meas := hint σ _ ((hw σ).mul (hρR σ).1)
    have h2 := hint σ _ (hw σ)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _) (h2.const_mul _)]
    congr 1; funext y; ring
  have e2 : ∀ σ, ∫ y, (ρ σ y / D.factorial + ε) * M ∂(ω σ).meas =
      M / D.factorial * ∫ y, ρ σ y ∂(ω σ).meas + M * ε * ∫ _y, (1 : ℝ) ∂(ω σ).meas := fun σ => by
    haveI := hfm σ
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint σ _ (hρR σ).1).const_mul _) ((integrable_const (1 : ℝ)).const_mul _)]
    congr 1; funext y; ring
  simp only [finsum_eq_sum_of_fintype] at hl1 hBs ⊢
  simp only [Fintype.card_fin] at hBs
  rw [Finset.sum_congr rfl fun σ _ => e1 σ, Finset.sum_congr rfl fun σ _ => e2 σ, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hBs] at hl1
  rw [← hIw, ← hW, ← hG', ← hV] at hl1
  set A : ℝ := ∑ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas with hA
  have eq1 : A / M - Iw / D.factorial - ε * W = (A - (M / D.factorial * Iw + M * ε * W)) / M := by
    field_simp
    ring
  rw [eq1, abs_div, abs_of_pos hM, div_le_iff₀ hM]
  have eq2 : C * (G' / D.factorial + ε * V - (r m : ℝ) / M) * M =
      C * (M / D.factorial * G' + M * ε * V - (r m : ℝ)) := by
    field_simp
  rw [eq2]
  exact hl1

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoBergmanMeasureChernFormPowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_bergmanMeasure_chernForm_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ w : ∀ σ, CxPts p σ → ℝ, (∀ σ, Continuous (w σ)) → Tendsto (fun m : ℕ => (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas) / (m : ℝ) ^ D) atTop (𝓝 (chInt P.L D w / D.factorial)) := by
  first | exact @GlobalTheory.HSAmp.tendsto_finsum_integral_berg | exact GlobalTheory.HSAmp.tendsto_finsum_integral_berg | (intros; apply GlobalTheory.HSAmp.tendsto_finsum_integral_berg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantJensenChangeOfWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantJensenChangeOfWeight
set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.GramJensen

variable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type} [Fintype ι] [DecidableEq ι]

def twist (v : ∀ σ, Y σ → ι → ℂ) (w : ∀ σ, Y σ → ℝ) : ∀ σ, Y σ → ι → ℂ :=
  fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)

def col (T : Matrix ι ι ℂ) (a : ι) : ι → ℂ := fun i => star (T i a)

theorem exp_half_sq (t : ℝ) : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
  rw [sq, ← Real.exp_add]; ring_nf

theorem cmb_twist (v : ∀ σ, Y σ → ι → ℂ) (w : ∀ σ, Y σ → ℝ) (c : ι → ℂ) (σ : S) (y : Y σ) :
    cmb (twist v w) c σ y = cmb v c σ y * Real.exp (-(w σ y)) := by
  have h : ∑ i, c i * twist v w σ y i = (∑ i, c i * v σ y i) * (Real.exp (-(w σ y) / 2) : ℝ) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [twist]; ring
  rw [cmb, cmb, h, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, exp_half_sq]

theorem cmb_nonneg (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) (σ : S) (y : Y σ) : 0 ≤ cmb v c σ y := by
  unfold cmb; positivity

theorem exp_neg_le {C t : ℝ} (h : |t| ≤ C) : Real.exp (-t) ≤ Real.exp C :=
  Real.exp_le_exp.2 (by linarith [neg_le_abs t])

theorem exp_neg_ge {C t : ℝ} (h : |t| ≤ C) : Real.exp (-C) ≤ Real.exp (-t) :=
  Real.exp_le_exp.2 (by linarith [le_abs_self t])

variable {μ : ∀ σ, Measure (Y σ)} {v : ∀ σ, Y σ → ι → ℂ} {w : ∀ σ, Y σ → ℝ} {C : ℝ}

theorem isFam_twist (h : IsFam μ v) (hw : ∀ σ, Measurable (w σ)) (hC : ∀ σ y, |w σ y| ≤ C) :
    IsFam μ (twist v w) := by
  refine ⟨h.finite, fun σ i j => ?_⟩
  have e : (fun y => twist v w σ y i * (starRingEnd ℂ) (twist v w σ y j)) =
      fun y => ((Real.exp (-(w σ y)) : ℝ) : ℂ) * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
    funext y
    simp only [twist, map_mul, Complex.conj_ofReal]
    rw [← exp_half_sq]; push_cast; ring
  rw [e]
  refine (h.integrable σ i j).bdd_mul (c := Real.exp C) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hw σ).neg)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_neg_le (hC σ y)

theorem l2_twist_eq_finsum_integral_mul_exp_neg (c : ι → ℂ) :
    l2 μ (twist v w) c = ∑ᶠ σ, ∫ y, cmb v c σ y * Real.exp (-(w σ y)) ∂μ σ := by
  simp only [l2, cmb_twist]

theorem quad (M T : Matrix ι ι ℂ) (a : ι) :
    ∑ i, ∑ j, col T a i * (starRingEnd ℂ) (col T a j) * M i j = (Tᴴ * M * T) a a := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, col]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]; ring

theorem quad_vec (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, star x i * (starRingEnd ℂ) (star x j) * M i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

theorem exp_neg_bound_mul_l2_le_l2_twist (h : IsFam μ v) (hw : ∀ σ, Measurable (w σ)) (hC : ∀ σ y, |w σ y| ≤ C) (c : ι → ℂ) :
    Real.exp (-C) * l2 μ v c ≤ l2 μ (twist v w) c := by
  have hS := h.finite
  haveI := Fintype.ofFinite S
  obtain ⟨-, hc⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  rw [l2_twist_eq_finsum_integral_mul_exp_neg]
  simp only [l2, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [← integral_const_mul]
  refine integral_mono (((hc c).1 σ).const_mul _) ?_ fun y => ?_
  · exact ((hc c).1 σ).mul_bdd (c := Real.exp C) (Real.measurable_exp.comp (hw σ).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_le (hC σ y))
  · have h0 := cmb_nonneg v c σ y
    have h1 := exp_neg_ge (hC σ y)
    simp only
    nlinarith

theorem posDef_twist (h : IsFam μ v) (hG : (gram μ v).PosDef) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) : (gram μ (twist v w)).PosDef := by
  refine GlobalTheory.T.gram_posDef_of_l2_definite S Y ι μ _ (isFam_twist h hw hC) fun c hc0 => ?_
  by_contra hne
  have hx : star c ≠ 0 := fun h' => hne (by simpa using congrArg star h')
  have hpos := hG.dotProduct_mulVec_pos hx
  obtain ⟨-, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  rw [quad_vec, star_star, ← (hl c).2.2] at hpos
  have hp : 0 < l2 μ v c := by exact_mod_cast hpos
  have := exp_neg_bound_mul_l2_le_l2_twist h hw hC c
  rw [hc0] at this
  nlinarith [Real.exp_pos (-C)]

theorem jensen (hS : Finite S) (f : ∀ σ, Y σ → ℝ) (hf0 : ∀ σ y, 0 ≤ f σ y)
    (hfi : ∀ σ, Integrable (f σ) (μ σ)) (hf1 : ∑ᶠ σ, ∫ y, f σ y ∂μ σ = 1) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) :
    Real.exp (-(∑ᶠ σ, ∫ y, w σ y * f σ y ∂μ σ)) ≤ ∑ᶠ σ, ∫ y, f σ y * Real.exp (-(w σ y)) ∂μ σ := by
  haveI := Fintype.ofFinite S
  simp only [finsum_eq_sum_of_fintype] at hf1 ⊢
  obtain ⟨m, hm⟩ : ∃ m, m = ∑ σ, ∫ y, w σ y * f σ y ∂μ σ := ⟨_, rfl⟩
  rw [← hm]
  have hwi : ∀ σ, Integrable (fun y => w σ y * f σ y) (μ σ) := fun σ =>
    (hfi σ).bdd_mul (c := C) (hw σ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC σ y)
  have hei : ∀ σ, Integrable (fun y => f σ y * Real.exp (-(w σ y))) (μ σ) := fun σ =>
    (hfi σ).mul_bdd (c := Real.exp C) (Real.measurable_exp.comp (hw σ).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_le (hC σ y))
  have pt : ∀ σ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ≤ f σ y * Real.exp (-(w σ y)) := by
    intro σ y
    have h1 := Real.add_one_le_exp (m - w σ y)
    have h2 : Real.exp (-m) * Real.exp (m - w σ y) = Real.exp (-(w σ y)) := by rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-m) * (m - w σ y + 1) ≤ Real.exp (-(w σ y)) := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have h4 := mul_le_mul_of_nonneg_left h3 (hf0 σ y)
    nlinarith
  have e : ∀ σ, ∫ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ∂μ σ =
      Real.exp (-m) * ((1 + m) * ∫ y, f σ y ∂μ σ - ∫ y, w σ y * f σ y ∂μ σ) := by
    intro σ
    rw [integral_const_mul, integral_sub ((hfi σ).mul_const _) (hwi σ), integral_mul_const]; ring
  calc Real.exp (-m) = Real.exp (-m) * ((1 + m) * ∑ σ, ∫ y, f σ y ∂μ σ - ∑ σ, ∫ y, w σ y * f σ y ∂μ σ) := by
        rw [hf1, ← hm]; ring
    _ = ∑ σ, ∫ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ∂μ σ := by
        rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ ≤ ∑ σ, ∫ y, f σ y * Real.exp (-(w σ y)) ∂μ σ :=
        Finset.sum_le_sum fun σ _ => integral_mono ((((hfi σ).mul_const _).sub (hwi σ)).const_mul _) (hei σ) (pt σ)

theorem berg_sum (T : Matrix ι ι ℂ) (hT : Tᴴ * gram μ v * T = 1) (σ : S) (y : Y σ) :
    ∑ a, cmb v (col T a) σ y = bergmanDensity μ v σ y := by
  have hinv : (gram μ v)⁻¹ = T * Tᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.1 hT
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : ((∑ a, cmb v (col T a) σ y : ℝ) : ℂ) =
      ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
    have ha : ∀ a, ((cmb v (col T a) σ y : ℝ) : ℂ) =
        ∑ i, ∑ j, T j a * star (T i a) * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
      intro a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [cmb, hn, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [col, map_mul, Complex.star_def, Complex.conj_conj]; ring
    rw [hinv, Complex.ofReal_sum]
    simp only [ha, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [bergmanDensity, ← key, Complex.ofReal_re]

theorem jensen_gram (h : IsFam μ v) (hG : (gram μ v).PosDef) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) :
    IsFam μ (twist v w) ∧ (gram μ (twist v w)).PosDef ∧
      Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤
        Real.log (gram μ (twist v w)).det.re := by
  have hF := isFam_twist h hw hC
  have hG' := posDef_twist h hG hw hC
  refine ⟨hF, hG', ?_⟩
  have hS := h.finite
  haveI := Fintype.ofFinite S
  obtain ⟨T, d, -, hT, hT'⟩ := GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian ι _ _ hG hG'.1
  obtain ⟨-, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  obtain ⟨-, hl'⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ _ hF
  have hl1 : ∀ a, l2 μ v (col T a) = 1 := fun a => by
    have := (hl (col T a)).2.2
    rw [quad, hT, Matrix.one_apply_eq] at this; exact_mod_cast this
  have hld : ∀ a, l2 μ (twist v w) (col T a) = d a := fun a => by
    have := (hl' (col T a)).2.2
    rw [quad, hT', Matrix.diagonal_apply_eq] at this; exact_mod_cast this
  have hj : ∀ a, Real.exp (-(∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ)) ≤ d a := fun a => by
    rw [← hld a, l2_twist_eq_finsum_integral_mul_exp_neg]
    exact jensen hS (cmb v (col T a)) (cmb_nonneg v _) (hl (col T a)).1 (hl1 a) hw hC
  have hd : ∀ a, 0 < d a := fun a => (Real.exp_pos _).trans_le (hj a)
  have hdet : (gram μ (twist v w)).det = (gram μ v).det * ∏ a, (d a : ℂ) := by
    have e1 := congrArg Matrix.det hT
    have e2 := congrArg Matrix.det hT'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at e2
    linear_combination (gram μ v).det * e2 - (gram μ (twist v w)).det * e1
  have hpos := Complex.pos_iff.1 (Matrix.PosDef.det_pos hG)
  have hre : (gram μ (twist v w)).det.re = (gram μ v).det.re * ∏ a, d a := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_mul_ofReal]
  rw [hre, Real.log_mul hpos.1.ne' (Finset.prod_pos fun a _ => hd a).ne', Real.log_prod fun a _ => (hd a).ne']
  have hsum : ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ = ∑ a, ∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ := by
    simp only [finsum_eq_sum_of_fintype]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← integral_finsetSum Finset.univ fun a _ => ((hl (col T a)).1 σ).bdd_mul (c := C)
      (hw σ).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC σ y)]
    congr 1; funext y; rw [← Finset.mul_sum, berg_sum T hT]
  have hlog : ∀ a, -(∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ) ≤ Real.log (d a) := fun a => by
    have := Real.log_le_log (Real.exp_pos _) (hj a); rwa [Real.log_exp] at this
  rw [hsum]
  have := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hlog a
  rw [Finset.sum_neg_distrib] at this
  linarith

theorem gram_det_jensen : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → ∀ (w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Measurable (w σ)) → (∀ σ y, |w σ y| ≤ C) → IsFam μ (fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)) ∧ (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).PosDef ∧ Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤ Real.log (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).det.re := by
  intro S Y _ ι _ _ μ v h hG w C hw hC
  exact jensen_gram h hG hw hC

end GlobalTheory.GramJensen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantJensenChangeOfWeightStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramDeterminant_jensen_change_of_weight : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → ∀ (w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Measurable (w σ)) → (∀ σ y, |w σ y| ≤ C) → IsFam μ (fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)) ∧ (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).PosDef ∧ Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤ Real.log (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).det.re := by
  first | exact @GlobalTheory.GramJensen.gram_det_jensen | exact GlobalTheory.GramJensen.gram_det_jensen | (intros; apply GlobalTheory.GramJensen.gram_det_jensen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantWeightShiftAsymptoticLe
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem gram_det_up_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (ε : ℝ), 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re ≤ (chInt P.L D u.u / D.factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX hG P hL ω r f hf hli hr u ε hε
  have hcomp : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hcont : ∀ σ, Continuous (u.u σ) := fun σ =>
    continuous_iff_continuousAt.2 fun y => (u.cInf σ y).continuousAt
  have hT := GlobalTheory.T.tendsto_bergmanMeasure_chernForm_pow k X p D hX hG P hL ω r f hf hli hr u.u hcont
  have hev : ∀ᶠ m : ℕ in atTop, (∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas)
      / (m : ℝ) ^ D < chInt P.L D u.u / D.factorial + ε :=
    hT (Iio_mem_nhds (by linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  obtain ⟨hF, hPD, -⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  haveI : Finite (k →+* ℂ) := hF.finite
  haveI : Fintype (k →+* ℂ) := Fintype.ofFinite _
  have hB : ∀ σ, ∃ C : ℝ, ∀ y, |u.u σ y| ≤ C := fun σ => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont σ).continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  choose C hC using hB
  set w : ∀ σ, CxPts p σ → ℝ := fun σ y => (((m : ℤ) : ℝ)) * u.u σ y with hw
  have hwm : ∀ σ, Measurable (w σ) := fun σ => (continuous_const.mul (hcont σ)).measurable
  have hwb : ∀ σ y, |w σ y| ≤ (m : ℝ) * ∑ τ, |C τ| := fun σ y => by
    simp only [hw, Int.cast_natCast, abs_mul, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
    exact (hC σ y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun τ => |C τ|) (fun τ _ => abs_nonneg _) (Finset.mem_univ σ)))
  obtain ⟨-, -, hJ⟩ := GlobalTheory.T.gramDeterminant_jensen_change_of_weight (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m)) (fun σ => (ω σ).meas)
    (vals P m 1 (f m)) hF hPD w _ hwm hwb
  have hnew : (fun σ y i => vals P m 1 (f m) σ y i * ((Real.exp (-(w σ y) / 2) : ℝ) : ℂ))
      = vals (upperParabolic P u) m 1 (f m) := by
    funext σ y i
    simp only [vals, hw]
    rw [((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ y (f m i)).1]
  rw [hnew] at hJ
  have hsum : (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas)
      = (m : ℝ) * ∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas := by
    rw [mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hw, Int.cast_natCast]
    ring
  rw [hsum] at hJ
  have hmpos : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast hm1) D
  rw [div_lt_iff₀ hmpos] at hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 := mul_le_mul_of_nonneg_left hm.le hm0
  calc _ ≤ (m : ℝ) * ∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas := by linarith
    _ ≤ _ := h2
    _ = _ := by ring

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantWeightShiftAsymptoticLeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramDeterminant_weightShift_asymptotic_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (ε : ℝ), 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re ≤ (chInt P.L D u.u / D.factorial + ε) * (m : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSAmp.gram_det_up_le | exact GlobalTheory.HSAmp.gram_det_up_le | (intros; apply GlobalTheory.HSAmp.gram_det_up_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRaiseWeightSegmentSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRaiseWeightSegmentSmul
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem semiPos_up_smul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (u : SmFn p)
    (t : ℝ), 0 ≤ t → t ≤ 1 → L.SemiPos D → (up L u).SemiPos D → (up L (u.smul t)).SemiPos D := by
  intro k _ X p D L u t h0 h1 hL hLu σ i c y hy ξ
  set f : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => (L.φ σ).φ i (c.e.symm v) with hfdef
  set g : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => u.u σ (c.e.symm v) with hgdef
  have hf : ContDiffAt ℝ 2 f (c.e y) := (L.cInf σ).contDiffAt c hy.1 hy.2
  have hfg : ContDiffAt ℝ 2 (fun v => f v + g v) (c.e y) := ((up L u).cInf σ).contDiffAt c hy.1 hy.2
  have a : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (f v : ℂ)) (c.e y) ξ).re := hL σ i c y hy ξ
  have b : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((f v + g v : ℝ) : ℂ)) (c.e y) ξ).re := hLu σ i c y hy ξ
  have e : (fun v => (((up L (u.smul t)).φ σ).φ i (c.e.symm v) : ℂ)) =
      fun v => ((((1 - t) * f v + 0) + (t * (f v + g v) + 0) : ℝ) : ℂ) := by
    funext v
    show ((((L.φ σ).φ i (c.e.symm v) + t * u.u σ (c.e.symm v)) : ℝ) : ℂ) = _
    congr 1
    simp only [hfdef, hgdef]
    ring
  rw [e, ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_add, ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hf,
    ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (f := fun v => f v + g v) hfg]
  · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have : 0 ≤ 1 - t := by linarith
    positivity
  · exact (hf.const_smul (1 - t)).add contDiffAt_const
  · exact (hfg.const_smul t).add contDiffAt_const

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRaiseWeightSegmentSmulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_raiseWeight_segment_smul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (u : SmFn p) (t : ℝ), 0 ≤ t → t ≤ 1 → L.SemiPos D → (up L u).SemiPos D → (up L (u.smul t)).SemiPos D := by
  first | exact @GlobalTheory.HSAmp.semiPos_up_smul | exact GlobalTheory.HSAmp.semiPos_up_smul | (intros; apply GlobalTheory.HSAmp.semiPos_up_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannSumOfOneSidedIncrements
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannSumOfOneSidedIncrements
open Filter Topology

namespace GlobalTheory

theorem polynomial_increment_near_derivative (s : Polynomial ℝ) {η δ : ℝ}
    (hδ : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, dist x y < δ →
      dist (s.derivative.eval x) (s.derivative.eval y) < η)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hba : b - a < δ) :
    (b - a) * s.derivative.eval a ≤ s.eval b - s.eval a + η * (b - a) ∧
    s.eval b - s.eval a ≤ (b - a) * s.derivative.eval b + η * (b - a) := by
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun x => s.eval x) hab
    s.continuous.continuousOn (fun x _ => s.differentiableAt.differentiableWithinAt)
  rw [Polynomial.deriv] at hcd
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hsc : s.eval b - s.eval a = (b - a) * s.derivative.eval c := by
    rw [hcd]; field_simp
  have h1 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ a ⟨ha, by linarith⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  have h2 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ b ⟨by linarith, hb⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  rw [Real.dist_eq, abs_lt] at h1 h2
  constructor
  · rw [hsc]; nlinarith [mul_lt_mul_of_pos_left h1.1 hpos]
  · rw [hsc]; nlinarith [mul_lt_mul_of_pos_left h2.2 hpos]

theorem riemann_sum_of_one_sided_increments : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ),
    (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) →
    Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  intro s ℓ h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / 4 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous s.derivative.continuous.continuousOn) η hηpos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hnpos : (0:ℝ) < n := lt_trans (by positivity) hn
  have hn0 : n ≠ 0 := by exact_mod_cast hnpos.ne'
  have hstep : (1:ℝ) / n < δ := by
    rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hδpos] at hn; linarith
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℚ, t = fun j : ℕ => (j : ℚ) / n := ⟨_, rfl⟩
  have ht0 : ∀ j, 0 ≤ t j := fun j => by rw [ht]; positivity
  have ht1 : ∀ j ≤ n, t j ≤ 1 := fun j hj => by
    rw [ht]; show (j:ℚ) / n ≤ 1
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)]; exact_mod_cast hj
  have htR : ∀ j, ((t j : ℚ) : ℝ) = (j : ℝ) / n := fun j => by rw [ht]; push_cast; ring
  have hdiff : ∀ j, ((t (j+1) : ℚ) : ℝ) - t j = 1 / n := fun j => by
    rw [htR, htR]; push_cast; ring
  have hηn : η * (1 / (n:ℝ)) = η / n := by ring
  have hup : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t j) m - ℓ (t (j+1)) m ≤
      (((t (j+1)) : ℝ) - t j) * s.derivative.eval (t j : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 j) (ht1 j hj'.le) (ht0 (j+1)) (ht1 (j+1) hj') _ (by positivity)
  have hlo : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t (j+1)) m - ℓ (t j) m ≤
      (((t j) : ℝ) - t (j+1)) * s.derivative.eval (t (j+1) : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 (j+1)) (ht1 (j+1) hj') (ht0 j) (ht1 j hj'.le) _ (by positivity)
  filter_upwards [hup, hlo] with m hu hl
  have t0 : t 0 = 0 := by rw [ht]; simp
  have tn : t n = 1 := by
    rw [ht]; show (n:ℚ) / n = 1; exact div_self (by exact_mod_cast hn0)
  have hsumℓ : ℓ 0 m - ℓ 1 m = ∑ j ∈ Finset.range n, (ℓ (t j) m - ℓ (t (j+1)) m) := by
    have := Finset.sum_range_sub' (fun j => ℓ (t j) m) n
    rw [this, t0, tn]
  have hsums : s.eval 1 - s.eval 0 =
      ∑ j ∈ Finset.range n, (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)) := by
    have := Finset.sum_range_sub (fun j => s.eval (t j : ℝ)) n
    rw [this, t0, tn]; simp
  have hstepb : ∀ j ∈ Finset.range n,
      |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| ≤ 2 * (η / n) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hd := hdiff j
    have h1n : (0:ℝ) < 1 / n := by positivity
    obtain ⟨k1, k2⟩ := polynomial_increment_near_derivative s hδ (a := t j) (b := t (j+1))
      (by exact_mod_cast ht0 j) (by linarith) (by exact_mod_cast ht1 _ hj') (by rw [hd]; exact hstep)
    have u := hu j hj
    have l := hl j hj
    have hd' : ((t j : ℚ) : ℝ) - t (j+1) = -(1 / n) := by linarith
    rw [hd] at k1 k2 u
    rw [hd'] at l
    rw [hηn] at k1 k2
    rw [abs_le]; constructor
    · nlinarith
    · nlinarith
  rw [Real.dist_eq, hsumℓ, hsums, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range n, ((ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)))|
      ≤ ∑ j ∈ Finset.range n, |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, 2 * (η / n) := Finset.sum_le_sum hstepb
    _ = 2 * η := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by rw [hη]; linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannSumOfOneSidedIncrementsStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ), (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) → Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  first | exact @GlobalTheory.riemann_sum_of_one_sided_increments | exact GlobalTheory.riemann_sum_of_one_sided_increments | (intros; apply GlobalTheory.riemann_sum_of_one_sided_increments <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogDetGramChangeSemiPositiveMetric
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSAmpDet

theorem chInt_smul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ) (c : ℝ) (u : SmFn p) :
    chInt L D (u.smul c).u = c * chInt L D u.u := by
  simp only [chInt, SmFn.smul, Weight.chernInt_const_mul, mul_finsum]

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem vals_smul (P : Pair p) (u : SmFn p) (t : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul t)) a b g = fun σ y i => vals P a b g σ y i * (Real.exp (-(a * (t * u.u σ y)) / 2) : ℝ) := by
  funext σ y i
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul t) a b).2.2 σ y (g i)).1

theorem vals_zero (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 0)) a b g = vals P a b g := by
  rw [vals_smul]
  funext σ y i
  simp

theorem vals_one (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 1)) a b g = vals (upperParabolic P u) a b g := by
  rw [vals_smul]
  funext σ y i
  rw [one_mul]
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u a b).2.2 σ y (g i)).1.symm

theorem vals_two (P : Pair p) (u : SmFn p) (t t' : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic (upperParabolic P (u.smul t)) (u.smul (t' - t))) a b g = vals (upperParabolic P (u.smul t')) a b g := by
  rw [vals_smul, vals_smul, vals_smul]
  funext σ y i
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

end

theorem tendsto_logDet_gram_sub : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  intro hA k _ X _ p D hX hG P hP ω r f hf hli hr u a a' hsp ha ha'
  obtain ⟨s, hs0, hs1, hsd⟩ := GlobalTheory.T.self_intersection_metric_segment_polynomial hA k X p D hX P.L u a a' ha ha'
  set c : ℝ := 2 / ((D + 1).factorial : ℝ) with hc
  let ℓ : ℚ → ℕ → ℝ := fun t m =>
    Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P (u.smul (t : ℝ))) m 1 (f m))).det.re / (m : ℝ) ^ (D + 1)
  have hR := GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative (Polynomial.C c * s) ℓ ?_
  · have hfun : (fun m => ℓ 0 m - ℓ 1 m) = fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1) := by
      funext m
      simp only [ℓ, Rat.cast_zero, Rat.cast_one, vals_zero, vals_one, sub_div]
    have hval : (Polynomial.C c * s).eval 1 - (Polynomial.C c * s).eval 0 = 2 * (a' - a) / (D + 1).factorial := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, hs0, hs1, hc]
      ring
    rw [hfun, hval] at hR
    exact hR
  · intro t t' ht0 ht1 ht0' ht1' ε hε
    have hsemi : (upperParabolic P (u.smul (t : ℝ))).L.SemiPos D :=
      GlobalTheory.T.semiPos_raiseWeight_segment_smul k X p D P.L u t (by exact_mod_cast ht0) (by exact_mod_cast ht1) hP hsp
    have hH : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P (u.smul (t : ℝ))).H m 1 := fun m i => by
      rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul (t : ℝ)) m 1).1]
      exact hf m i
    have hrk : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
        (𝓝 (gdeg (upperParabolic P (u.smul (t : ℝ))).L D / D.factorial)) := by
      rw [show (upperParabolic P (u.smul (t : ℝ))).L = up P.L (u.smul (t : ℝ)) from rfl,
        GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L (u.smul (t : ℝ))]
      exact hr
    have hstep := GlobalTheory.T.gramDeterminant_weightShift_asymptotic_le k X p D hX hG (upperParabolic P (u.smul (t : ℝ))) hsemi ω r f hH hli hrk
      (u.smul ((t' : ℝ) - t)) ε hε
    have hch : chInt (upperParabolic P (u.smul (t : ℝ))).L D (u.smul ((t' : ℝ) - t)).u / D.factorial =
        ((t' : ℝ) - t) * (Polynomial.C c * s).derivative.eval (t : ℝ) := by
      rw [chInt_smul, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, ← hsd t, hc,
        Nat.factorial_succ]
      have hf0 : (D.factorial : ℝ) ≠ 0 := by positivity
      show ((t' : ℝ) - t) * chInt (up P.L (u.smul (t : ℝ))) D u.u / D.factorial = _
      push_cast
      field_simp
    filter_upwards [hstep, eventually_ge_atTop 1] with m hm hm1
    have hpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      positivity
    rw [vals_two, hch] at hm
    simp only [ℓ]
    rw [← sub_div, div_le_iff₀ hpos]
    linarith

end GlobalTheory.HSAmpDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogDetGramChangeSemiPositiveMetricStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_logDet_gram_change_semiPositive_metric : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  first | exact @GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub | exact GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub | (intros; apply GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub <;> assumption)
end
