module

public import Development.AutomorphicSpectrum.RootSurvey.GeometrySurvey.ExistsTopDegreeCoefficientFormAndEqOnTopForms
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatTwist
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredBound

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IntegralOverPlaceDensity
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.PlaceIntegralDensity

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sheetDensity_sum {S : Type} [Fintype S] {e : ℕ} (W : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (ψ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (t : S → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : S → ((Σ k, ι k) → ℂ) → ℝ)
    (h : ∀ z ∈ mcPts W, u z = ∑ σ, t σ * χ σ z) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity W Ψ ψ u y w = ∑ σ, t σ * sheetDensity W Ψ ψ (χ σ) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [h _ hγ.choose_spec.2.self_of_nhds.2.1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by ring
  · simp

theorem finsum_mem_sum {α S : Type} [Fintype S] {s : Set α} (hs : s.Finite) (t : S → ℝ) (f : S → α → ℝ) :
    ∑ᶠ w ∈ s, ∑ σ, t σ * f σ w = ∑ σ, t σ * ∑ᶠ w ∈ s, f σ w := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.mul_sum]
  exact Finset.sum_comm

theorem eq_sum {Ω : Type} [Field Ω] {F : Type} [Field F] [NumberField F] {y : (Σ k, ι k) → Ω} {φ : F →+* Ω}
    {t : (F →+* ℂ) → ℝ} {u : ((Σ k, ι k) → ℂ) → ℝ} {χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ}
    (hO : OverInt y φ) (hu : ∀ σ z, PtOver y φ σ z → u z = t σ)
    (hχ : ∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : u z = ∑ σ, t σ * χ σ z := by
  obtain ⟨σ₀, hσ₀, -⟩ := existsUnique_ptOver _ _ _ _ y φ hO z hz
  rw [hu σ₀ z hσ₀, Finset.sum_eq_single σ₀]
  · rw [((hχ σ₀).near σ₀ z hσ₀).self_of_nhds]
    simp
  · intro b _ hb
    rw [((hχ b).near σ₀ z hσ₀).self_of_nhds]
    simp [Set.indicator, Ne.symm hb]
  · simp

end PositivityTheory.Xgn.PlaceIntegralDensity

open PositivityTheory.Xgn.PlaceIntegralDensity in
theorem PositivityTheory.Xgn.integral_over_place_density : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ), OverInt y φ → mCoordIdeal y ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ z, PtOver y φ σ z → u z = t σ) → (∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) → ptsIntegral W (pot L) u = ∑ σ : F →+* ℂ, t σ * ptsIntegral W (pot L) (χ σ) := by
  intro hPI K _ ι _ Ω _ F _ _ y φ W n L t u χ hO hW hA hL hu hχ
  have hmc : ∀ z ∈ mcPts W, z ∈ mcPts (mCoordIdeal y) := fun z hz => ⟨hz.1, fun f hf => hz.2 f (hW hf)⟩
  have hsum : ∀ z ∈ mcPts W, u z = ∑ σ, t σ * χ σ z := fun z hz => eq_sum hO hu hχ (hmc z hz)
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hfin := fibreFinite K ι W n hΨ.choose hA hΨ.choose_spec
    have hpt : ∀ y', ∑ᶠ (w) (_ : w ∈ fibre W hΨ.choose y'), ∑ σ, t σ * sheetDensity W hΨ.choose (pot L) (χ σ) y' w =
        ∑ σ, t σ * ∑ᶠ (w) (_ : w ∈ fibre W hΨ.choose y'), sheetDensity W hΨ.choose (pot L) (χ σ) y' w :=
      fun y' => finsum_mem_sum (hfin y') t (fun σ w => sheetDensity W hΨ.choose (pot L) (χ σ) y' w)
    simp_rw [sheetDensity_sum W _ (pot L) t u χ hsum, hpt]
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl fun σ _ => MeasureTheory.integral_const_mul (t σ) _
    · intro σ _
      refine MeasureTheory.Integrable.const_mul ?_ (t σ)
      let A : HermLine ι :=
        { a := fun _ => 0
          h := fun z => Real.exp (-χ σ z)
          pos := fun z _ => Real.exp_pos _
          smul := fun c z hc => by simp [(hχ σ).inv c z hc] }
      have hAs : IsSmoothHerm A := Real.contDiff_exp.comp_contDiffOn (hχ σ).smooth.neg
      have hsec : IsSectionOn W A 1 :=
        ⟨fun _ => 0, fun k => by simp [A], isMultiHomog_one,
          fun h => hA.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)⟩
      have hlog : logNorm A 1 = χ σ := by
        funext z
        simp [logNorm, A, Real.exp_neg, Real.log_exp]
      have hI := hPI K ι W n hΨ.choose L A 1 hA hΨ.choose_spec hL hAs hsec
      rw [hlog] at hI
      exact hI
  · simp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootFlatPushforwardGeoFun
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyMultilinear
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatHerm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyPlaceWeight
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GreenCurrentIntegralFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GreenCurrentIntegralFormula
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ptsIntegral_place : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ), OverInt y φ → mCoordIdeal y ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ z, PtOver y φ σ z → u z = t σ) → (∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) → ptsIntegral W (pot L) u = ∑ σ : F →+* ℂ, t σ * ptsIntegral W (pot L) (χ σ) :=
  PositivityTheory.Xgn.integral_over_place_density

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GreenCurrentIntegralFormulaStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.green_current_integral_formula : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ), OverInt y φ → mCoordIdeal y ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ z, PtOver y φ σ z → u z = t σ) → (∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) → ptsIntegral W (pot L) u = ∑ σ : F →+* ℂ, t σ * ptsIntegral W (pot L) (χ σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_place | exact GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_place | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_place <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstant
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstant
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem notMem_mCoordIdeal_of_aeval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {h : MRing ι} (h0 : aeval y h ≠ 0) : h ∉ mCoordIdeal y := by
  intro hh
  apply h0
  have e := UnitChart.aeval_scaled y (fun _ => 1) h
  simp only [mul_one] at e
  rw [e, show mConeMap y h = 0 from hh, map_zero]

theorem exists_flatHerm_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  intro K _ ι _ Ω _ F _ _ y φ α hO
  obtain ⟨hy, hR⟩ := hO
  choose c hc using id hy
  obtain ⟨m, G, hG, e⟩ := UnitChart.chart_form hc (hR c hc (α : 𝓞 F))
  have hα : ((α : 𝓞 F) : F) ≠ 0 := by
    simp
  have hφα : φ ((α : 𝓞 F) : F) ≠ 0 := (map_ne_zero φ).2 hα
  have hprod : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hg0 : aeval y (UnitChart.cMon c m) ≠ 0 := by rwa [UnitChart.aeval_cMon]
  have hG0 : aeval y G ≠ 0 := by rw [← e]; exact mul_ne_zero hφα hprod
  have e' : aeval y G = φ ((α : 𝓞 F) : F) * aeval y (UnitChart.cMon c m) := by
    rw [UnitChart.aeval_cMon, e]
  have hq : aeval y G / aeval y (UnitChart.cMon c m) = φ ((α : 𝓞 F) : F) := by
    rw [e', mul_div_cancel_right₀ _ hg0]
  have hinv : φ (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = (φ ((α : 𝓞 F) : F))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    have : (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((α : 𝓞 F) : F) = 1 := by
      have h1 : ((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (α : 𝓞 F) = 1 := α.inv_mul
      have h2 := congrArg (algebraMap (𝓞 F) F) h1
      rw [map_mul, map_one] at h2
      exact h2
    rw [this, map_one]
  have hfn := notMem_mCoordIdeal_of_aeval_ne_zero hG0
  have hgn := notMem_mCoordIdeal_of_aeval_ne_zero hg0
  refine ⟨{ M := 1
            M_pos := one_pos
            f := G
            g := UnitChart.cMon c m
            df := m
            dg := m
            hf := hG
            hg := UnitChart.homog_cMon c m
            deg := fun k => by simp [constLine, HermLine.ofWeight]
            f_ne := hfn
            g_ne := hgn
            unit := ?_
            κ := fun σ => ‖σ ((α : 𝓞 F) : F)‖
            κ_pos := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hα)
            κ_conj := fun σ => by simp [ComplexEmbedding.conjugate_coe_eq]
            norm := ?_ }, rfl, fun _ => rfl⟩
  · rw [isUnitSec_iff_chart K ι Ω y G _ m m hy hG (UnitChart.homog_cMon c m) hfn hgn]
    intro c' hc'
    simp only [sub_self, neg_zero, zpow_zero, Finset.prod_const_one, mul_one, hq]
    exact ⟨hR c' hc' _, hinv ▸ hR c' hc' _⟩
  · intro σ z hz
    rw [hz.2 _ m G _ hG (UnitChart.homog_cMon c m) e', norm_mul]
    simp [constLine, HermLine.ofWeight]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstantStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_herm_unit_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyPlaceWeight
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem constLine_zero_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    (constLine (ι := ι) 0).tensor (constLine 0) = constLine 0 := by
  simp [HermLine.tensor, constLine, HermLine.ofWeight]

theorem ptsIntegral_eq_mean : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (d : ℕ) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → (∀ σ z, PtOver y φ σ z → u z = t σ) → ptsIntegral W (pot L) u = meanEmb t * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hPI K _ ι _ Ω _ F _ _ y φ I W n L d t u hI hd hO hle hW hL ht hu
  have hex := fun σ : F →+* ℂ => GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (Set.indicator {σ} 1) hO
  choose χ hχ _ using hex
  have hsplit : ∀ (t' : (F →+* ℂ) → ℝ) (u' : ((Σ k, ι k) → ℂ) → ℝ),
      (∀ σ z, PtOver y φ σ z → u' z = t' σ) →
      ptsIntegral W (pot L) u' = ∑ σ : F →+* ℂ, t' σ * ptsIntegral W (pot L) (χ σ) :=
    fun t' u' h => GlobalTheory.T.green_current_integral_formula hPI K ι Ω F y φ W n L t' u' χ hO hle hW hL h hχ
  have hc : IsSmoothHerm (constLine (ι := ι) 0) := contDiffOn_const
  have hzero : I W (n + 1) (Fin.snoc L (constLine 0)) = 0 := by
    have h := hI.2.1 W n L (constLine 0) (constLine 0) hW hL hc hc
    rw [constLine_zero_tensor] at h
    linarith
  have hunit : ∀ α : (𝓞 F)ˣ,
      ∑ σ : F →+* ℂ, Real.log ‖σ ((α : 𝓞 F) : F)‖ * ptsIntegral W (pot L) (χ σ) = 0 := by
    intro α
    obtain ⟨S, -, hκ⟩ := GlobalTheory.T.flat_herm_unit_constant K ι Ω F y φ α hO
    obtain ⟨v, hv, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
    have h1 := GlobalTheory.T.intersection_family_flat_twist K ι Ω F y φ I W n L (constLine 0) S d v hI hd hO hle hW hL hc hv
    have h2 := hsplit (fun σ => Real.log (S.κ σ)) v fun σ z hz => (hv.near σ z hz).self_of_nhds
    simp only [hκ] at h2
    linarith
  have hmain := sum_eq_mean_of_units F (fun σ => ptsIntegral W (pot L) (χ σ)) t hunit ht
  have hone := hsplit (fun _ => 1) (fun _ => 1) fun _ _ _ => rfl
  simp only [one_mul] at hone
  rw [hsplit t u hu, hone, hmain]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyPlaceWeightStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_family_place_weight : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (d : ℕ) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → (∀ σ z, PtOver y φ σ z → u z = t σ) → ptsIntegral W (pot L) u = meanEmb t * ptsIntegral W (pot L) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean | exact GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatHerm
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem FlatHerm.inter_eq : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ),
    IsIntersectionFamily I → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    I W (n + 1) (Fin.snoc L A) = S.ht * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hP K _ ι _ Ω _ F _ _ y φ I W n L A S d hI hY hO hyW hW hL hA
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
  rw [GlobalTheory.T.intersection_family_flat_twist K ι Ω F y φ I W n L A S d u hI hY hO hyW hW hL hA hu,
    GlobalTheory.T.intersection_family_place_weight hP K ι Ω F y φ I W n L d (fun σ => Real.log (S.κ σ)) u hI hY hO hyW hW hL
      (fun σ => congrArg Real.log (S.κ_conj σ)) (fun σ z hz => (hu.near σ z hz).self_of_nhds),
    FlatHerm.ht, neg_mul]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatHermStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_family_flat_herm : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ), IsIntersectionFamily I → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → I W (n + 1) (Fin.snoc L A) = S.ht * ptsIntegral W (pot L) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyMultilinear
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.SumRoots

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_ofWeight (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (hs : SmoothFn u) :
    IsSmoothHerm (HermLine.ofWeight u hu) :=
  ContDiffOn.exp hs.neg

theorem smooth_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

theorem homog_one : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [← C_1, C_apply] at hm
  have := Finset.mem_singleton.mp (support_monomial_subset hm)
  simp [this]

theorem inter_ofWeight {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι}
    (hW : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (hs : SmoothFn u) :
    I W (n + 1) (Fin.snoc L (HermLine.ofWeight u hu)) = -ptsIntegral W (pot L) u := by
  have h1 : (1 : MRing ι) ∉ W := (Ideal.ne_top_iff_one W).mp hW.2.1.1.ne_top
  rw [hI.2.2 W n L _ 1 (fun _ => 0) hW hL (smooth_ofWeight u hu hs) (fun k => by simp [HermLine.ofWeight])
    homog_one h1]
  have hd : divSupp W (1 : MRing ι) = ∅ := by
    ext V
    simp [divSupp, Ideal.minimalPrimes_top]
  have hl : logNorm (HermLine.ofWeight u hu) (1 : MRing ι) = u := by
    funext z
    simp [logNorm, HermLine.ofWeight]
  unfold recR arInt
  rw [hd, hl]
  simp only [finsum_mem_empty, zero_sub]
  rfl

noncomputable def tens : (N : ℕ) → (Fin N → HermLine ι) → HermLine ι
  | 0, _ => HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)
  | N + 1, x => (tens N (fun i => x i.castSucc)).tensor (x (Fin.last N))

theorem tens_a : ∀ (N : ℕ) (x : Fin N → HermLine ι), (tens N x).a = ∑ i, (x i).a
  | 0, _ => by simp [tens, HermLine.ofWeight]
  | N + 1, x => by
    rw [Fin.sum_univ_castSucc, ← tens_a N (fun i => x i.castSucc)]
    rfl

theorem tens_h : ∀ (N : ℕ) (x : Fin N → HermLine ι) z, (tens N x).h z = ∏ i, (x i).h z
  | 0, _, _ => by simp [tens, HermLine.ofWeight]
  | N + 1, x, z => by
    rw [Fin.prod_univ_castSucc, ← tens_h N (fun i => x i.castSucc)]
    rfl

theorem tens_smooth : ∀ (N : ℕ) (x : Fin N → HermLine ι), (∀ i, IsSmoothHerm (x i)) → IsSmoothHerm (tens N x)
  | 0, _, _ => smooth_ofWeight _ _ contDiffOn_const
  | N + 1, x, hx => smooth_tensor (tens_smooth N _ fun _ => hx _) (hx _)

theorem ptsIntegral_zero (W : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral W φ (fun _ => 0) = 0 := by
  unfold ptsIntegral
  split_ifs with h
  · have : ∀ y w, sheetDensity W h.choose φ (fun _ => 0) y w = 0 := fun y w => by
      unfold sheetDensity
      split_ifs <;> simp
    simp [ptsIntegralAt, this]
  · rfl

theorem inter_tens {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι}
    (hW : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ (N : ℕ) (x : Fin N → HermLine ι), (∀ i, IsSmoothHerm (x i)) →
      I W (n + 1) (Fin.snoc L (tens N x)) = ∑ i, I W (n + 1) (Fin.snoc L (x i))
  | 0, _, _ => by
    rw [tens, inter_ofWeight hI hW hL _ _ contDiffOn_const, ptsIntegral_zero]
    simp
  | N + 1, x, hx => by
    rw [tens, hI.2.1 W n L _ _ hW hL (tens_smooth N _ fun _ => hx _) (hx _),
      inter_tens hI hW hL N _ (fun _ => hx _), Fin.sum_univ_castSucc]

end GlobalTheory.CompanionTheory.Ar.Flat.SumRoots

theorem GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq : PtsIntegrableStatement → MetricLocalStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d N : ℕ) (x : Fin N → HermLine ι) (v : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → (∀ i, IsSmoothHerm (x i)) → (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → v (fun p => c p.1 * z p) = v z) → SmoothFn v → ∑ i, (x i).a = A.a → (∀ z ∈ mcPts W, ∏ i, (x i).h z = A.h z * Real.exp (-v z)) → ∑ i, I W (n + 1) (Fin.snoc L (x i)) = S.ht * ptsIntegral W (pot L) (fun _ => 1) - ptsIntegral W (pot L) v := by
  intro hP hM K _ ι _ Ω _ F _ _ y φ I W n L A S d N x v hI hV hO hyW hW hL hA hx hv hs ha hh
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  have hsn : ∀ B : HermLine ι, IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc L B : Fin (n + 1) → HermLine ι) j) := fun B hB j => by
    induction j using Fin.lastCases with
    | last => simpa using hB
    | cast j => simpa using hL j
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  have hloc : I W (n + 1) (Fin.snoc L (tens N x)) =
      I W (n + 1) (Fin.snoc L (A.tensor (HermLine.ofWeight v hv))) := by
    refine hM K ι I hI W (n + 1) _ _ hW (hsn _ (tens_smooth N x hx))
      (hsn _ (smooth_tensor hA (smooth_ofWeight v hv hs))) (fun j => ?_) (fun j z hz => ?_)
    · induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [tens_a, ha]
        simp [HermLine.tensor, HermLine.ofWeight]
      | cast j => simp only [Fin.snoc_castSucc]
    · induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [tens_h, hh z hz]
        rfl
      | cast j => simp only [Fin.snoc_castSucc]
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  rw [← inter_tens hI hW hL N x hx, hloc, hI.2.1 W n L _ _ hW hL hA (smooth_ofWeight v hv hs),
    inter_ofWeight hI hW hL v hv hs,
    GlobalTheory.T.intersection_family_flat_herm hP K ι Ω F y φ I W n L A S d hI hV hO hyW hW hL hA, sub_eq_add_neg]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyMultilinearStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_family_multilinear : PtsIntegrableStatement → MetricLocalStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d N : ℕ) (x : Fin N → HermLine ι) (v : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → (∀ i, IsSmoothHerm (x i)) → (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → v (fun p => c p.1 * z p) = v z) → SmoothFn v → ∑ i, (x i).a = A.a → (∀ z ∈ mcPts W, ∏ i, (x i).h z = A.h z * Real.exp (-v z)) → ∑ i, I W (n + 1) (Fin.snoc L (x i)) = S.ht * ptsIntegral W (pot L) (fun _ => 1) - ptsIntegral W (pot L) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArMonoAddSingle
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

namespace RootMono

theorem card_fiber {α : Type*} [DecidableEq α] (l : List α) (c : α) :
    Fintype.card {i : Fin l.length // l.get i = c} = l.count c := by
  rw [Fintype.card_subtype, Finset.card_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := Fin.sum_univ_succ (n := l.length)
      (fun i : Fin (l.length + 1) => if (a :: l).get i = c then 1 else 0)
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at h ih
    simp only [List.get_eq_getElem, List.length_cons]
    rw [h, ih, List.count_cons]
    by_cases hac : a = c
    · simp [hac, add_comm]
    · simp [hac, add_comm]

theorem exists_perm_fin {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (h : l₁.Perm l₂) {n : ℕ} (hn : l₁.length = n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n) (h₁ : (i : ℕ) < l₁.length) (h₂ : (σ i : ℕ) < l₂.length),
      l₂[(σ i : ℕ)] = l₁[(i : ℕ)] := by
  subst hn
  have hc : ∀ c, Fintype.card {i : Fin l₁.length // l₁.get i = c} =
      Fintype.card {i : Fin l₂.length // l₂.get i = c} := fun c => by
    rw [card_fiber, card_fiber, h.count_eq]
  let e : Fin l₁.length ≃ Fin l₂.length := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c)
  have he : ∀ i, l₂.get (e i) = l₁.get i := Equiv.ofFiberEquiv_map _
  refine ⟨e.trans (finCongr h.length_eq.symm), fun i h₁ h₂ => ?_⟩
  simpa using he i

theorem length_toList {J : Type} (m : J →₀ ℕ) : (Finsupp.toMultiset m).toList.length = m.degree := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  simp only [Finsupp.sum, id]
  rfl

end RootMono


open RootMono in
theorem arMono_add_single (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem)
    (t : ℝ) (m : Ψ × Fin N →₀ ℕ) (r : Ψ × Fin N) (hII : IsIntersectionSystem II) (hm : m.degree = dimFl Ψ N) :
    M.arMono II t ((m + Finsupp.single r 1).mapDomain some) =
      II M.K M.ι M.P (dimFl Ψ N + 1)
        (Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r)) / (M.δ : ℝ) := by
  classical
  have hn : (m + Finsupp.single r 1).mapDomain some = m.mapDomain some + Finsupp.single (some r) 1 := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  have hdm : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hdeg : ((m + Finsupp.single r 1).mapDomain some).degree = dimFl Ψ N + 1 := by
    rw [hn, map_add (f := _), hdm, Finsupp.degree_single]
  have hnone : ((m + Finsupp.single r 1).mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have hperm : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.Perm
      ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList, hn, map_add (f := _)]
    simp
  have hlen₁ : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length = dimFl Ψ N + 1 := by
    rw [length_toList, hdeg]
  have hlen₀ : (Finsupp.toMultiset (m.mapDomain some)).toList.length = dimFl Ψ N := by
    rw [length_toList, hdm]
  have hsm : ∀ o, IsSmoothHerm (M.line t o) := by
    intro o
    cases o with
    | none => exact M.A_smooth
    | some b => exact M.x_smooth t b
  set L : Fin (dimFl Ψ N + 1) → HermLine M.ι :=
    Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r) with hL
  have hval : ∀ (j : Fin (dimFl Ψ N + 1))
      (hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length),
      L j = M.line t (((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[(j : ℕ)]) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro hj
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.last (dimFl Ψ N) : Fin _) : ℕ)] = some r := by
        simp [List.getElem_append, hlen₀]
      rw [this, hL, Fin.snoc_last]
      rfl
    · intro hj
      have hk : (k : ℕ) < (Finsupp.toMultiset (m.mapDomain some)).toList.length := by
        rw [hlen₀]; exact k.2
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.castSucc k : Fin _) : ℕ)] =
          (Finsupp.toMultiset (m.mapDomain some)).toList[(k : ℕ)] := by
        exact List.getElem_append_left hk
      rw [this, hL, Fin.snoc_castSucc]
      simp only [monoLines, dif_pos hk]
      rfl
  have hLs : ∀ j, IsSmoothHerm (L j) := by
    intro j
    have hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, j.2]
    rw [hval j hj]
    exact hsm _
  obtain ⟨σ, hσ⟩ := exists_perm_fin hperm hlen₁
  have hfun : monoLines (M.line t) ((m + Finsupp.single r 1).mapDomain some) (dimFl Ψ N + 1) = L ∘ σ := by
    funext i
    have h₁ : (i : ℕ) < (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length := by
      rw [hlen₁]; exact i.2
    have h₂ : (σ i : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, (σ i).2]
    simp only [monoLines, dif_pos h₁, Function.comp, hval (σ i) h₂, hσ i h₁ h₂]
    rfl
  unfold RootModel.arMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one, hfun]
  congr 1
  exact (hII M.K M.ι).1 M.P (dimFl Ψ N + 1) L σ M.arith hLs

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MonoLinesLineSmooth
noncomputable section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem line_smooth_at (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem line_a_eq (M : RootModel Ψ N) (t s : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line s j).a := by
  cases j with
  | none => rfl
  | some r => exact (M.x_deg t r).trans (M.x_deg s r).symm

theorem monoLines_line_smooth (M : RootModel Ψ N) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (k : Fin d) :
    IsSmoothHerm (monoLines (M.line t) m d k) := by
  unfold monoLines
  split_ifs with h
  · exact line_smooth_at M t _
  · exact contDiffOn_const

theorem monoLines_line_a (M : RootModel Ψ N) (t s : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (k : Fin d) :
    (monoLines (M.line t) m d k).a = (monoLines (M.line s) m d k).a := by
  unfold monoLines
  split_ifs with h
  · exact line_a_eq M t s _
  · rfl

theorem ptsIntegral_line_eq (hD : DegreeStatement) (M : RootModel Ψ N) (t s : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    ptsIntegral M.P (pot (monoLines (M.line t) m (dimFl Ψ N))) (fun _ => 1) =
      ptsIntegral M.P (pot (monoLines (M.line s) m (dimFl Ψ N))) (fun _ => 1) := by
  rw [hD M.K M.ι M.P (dimFl Ψ N) _ 2 M.arith (monoLines_line_smooth M t m _) Nat.prime_two,
    hD M.K M.ι M.P (dimFl Ψ N) _ 2 M.arith (monoLines_line_smooth M s m _) Nat.prime_two]
  simp only [monoLines_line_a M t s m]

theorem geoMono_eq (hD : DegreeStatement) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ)
    (m : Ψ × Fin N →₀ ℕ) (hm : m.degree = dimFl Ψ N) :
    ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (fun _ => 1) / (M.δ : ℝ) =
      M.geoMono (m.mapDomain some) := by
  have hdeg : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hnone : (m.mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  rw [ptsIntegral_line_eq hD M t 1]
  unfold RootModel.geoMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootFlatPushforwardGeoFun
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RootSum

theorem mono_smooth {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (t : ℝ)
    (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (j : Fin d) : IsSmoothHerm (monoLines (M.line t) m d j) := by
  unfold monoLines
  split_ifs
  · rename_i h
    generalize (Finsupp.toMultiset m).toList.get ⟨j, h⟩ = o
    cases o with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  · unfold IsSmoothHerm
    simp only [trivLine]
    exact contDiffOn_const

theorem PP_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem)
    (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.PP II (monomial m 1) = limUnder (𝓝[>] 0) fun t => M.arMono II t m := by
  exact Module.Basis.constr_basis (basisMonomials (Option (Ψ × Fin N)) ℝ) ℝ _ m

theorem geoFun_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)
    (m : Option (Ψ × Fin N) →₀ ℕ) : M.geoFun (monomial m 1) = M.geoMono m := by
  exact Module.Basis.constr_basis (basisMonomials (Option (Ψ × Fin N)) ℝ) ℝ _ m

theorem toA_pk_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (τ : Ψ) (m : Ψ × Fin N →₀ ℕ) :
    toA (pk τ 1 * monomial m (1 : ℝ) : RP Ψ N) =
      ∑ i : Fin N, monomial ((m + Finsupp.single (τ, i) 1).mapDomain some) (1 : ℝ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [toA, pk, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_one, X, monomial_mul, rename_monomial, add_comm, mul_one]

theorem sum_arMono (hP : PtsIntegrableStatement) (hM : MetricLocalStatement) (hD : DegreeStatement)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ)
    (R : RootFlat M τ) (hII : IsIntersectionSystem II) (m : Ψ × Fin N →₀ ℕ) (hm : m.degree = dimFl Ψ N)
    (t : ℝ) (ht : 0 < t) :
    ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some) =
      R.ht * M.geoMono (m.mapDomain some) -
        ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (R.v t) / (M.δ : ℝ) := by
  have h1 := GlobalTheory.T.intersection_family_multilinear hP hM M.K M.ι M.Ω R.F M.y R.φ (II M.K M.ι) M.P (dimFl Ψ N)
    (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) R.A R.S (dimFl Ψ N + 1) N
    (fun i => M.x t (τ, i)) (R.v t) (hII M.K M.ι) M.arith R.overInt le_rfl M.arith
    (mono_smooth M t _ _) R.A_smooth (fun i => M.x_smooth t _) (R.v_inv t) (R.v_smooth t)
    (by simp only [M.x_deg]; exact R.deg) (R.prod t ht)
  rw [Finset.sum_congr rfl fun i _ => arMono_add_single Ψ N M II t m (τ, i) hII hm, ← Finset.sum_div, h1,
    ← geoMono_eq hD Ψ N M t m hm, RootFlat.ht]
  ring

theorem PP_mono (hP : PtsIntegrableStatement) (hM : MetricLocalStatement) (hD : DegreeStatement)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ)
    (R : RootFlat M τ) (hII : IsIntersectionSystem II) (hC : M.Converges II) (m : Ψ × Fin N →₀ ℕ)
    (hm : m.degree = dimFl Ψ N) :
    M.PP II (toA (pk τ 1 * monomial m 1)) = R.ht * M.geoFun (toA (monomial m 1)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [toA_pk_monomial, map_sum, toA, rename_monomial, geoFun_monomial]
  simp only [PP_monomial]
  have h1 : Tendsto (fun t => ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))
      (𝓝[>] 0) (𝓝 (∑ i : Fin N, limUnder (𝓝[>] 0) fun t =>
        M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))) :=
    tendsto_finsetSum _ fun i _ => tendsto_nhds_limUnder (hC _)
  have h2 : Tendsto (fun t => ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))
      (𝓝[>] 0) (𝓝 (R.ht * M.geoMono (m.mapDomain some) - 0 / (M.δ : ℝ))) := by
    refine (tendsto_const_nhds.sub ((R.small m hm).div_const _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (sum_arMono hP hM hD M II τ R hII m hm t ht).symm
  rw [tendsto_nhds_unique h1 h2, zero_div, sub_zero]

end GlobalTheory.CompanionTheory.Ar.Flat.RootSum

open GlobalTheory.CompanionTheory.Ar.Flat.RootSum in
theorem GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq : PtsIntegrableStatement → MetricLocalStatement → DegreeStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ) (R : RootFlat M τ) (Q : RP Ψ N), IsIntersectionSystem II → M.Converges II → Q.IsHomogeneous (dimFl Ψ N) → M.PP II (toA (pk τ 1 * Q)) = R.ht * M.geoFun (toA Q) := by
  intro hP hM hD Ψ _ _ N M II τ R Q hII hC hQ
  have hQ' : Q = ∑ m ∈ Q.support, Q.coeff m • monomial m (1 : ℝ) := by
    conv_lhs => rw [Q.as_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have hA : ∀ (c : ℝ) (F : RP Ψ N), toA (c • F) = c • toA F := fun c F => map_smul (rename some) c F
  have hS : ∀ (s : Finset (Ψ × Fin N →₀ ℕ)) (F : _ → RP Ψ N), toA (∑ m ∈ s, F m) = ∑ m ∈ s, toA (F m) :=
    fun s F => map_sum (rename some) F s
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hQ', Finset.mul_sum, hS, hS, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = dimFl Ψ N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.mp hm)
  rw [mul_smul_comm, hA, hA, map_smul, map_smul, PP_mono hP hM hD M II τ R hII hC m hd, smul_eq_mul, smul_eq_mul]
  ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootFlatPushforwardGeoFunStatement
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_flat_pushforward_geoFun : PtsIntegrableStatement → MetricLocalStatement → DegreeStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ) (R : RootFlat M τ) (Q : RP Ψ N), IsIntersectionSystem II → M.Converges II → Q.IsHomogeneous (dimFl Ψ N) → M.PP II (toA (pk τ 1 * Q)) = R.ht * M.geoFun (toA Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaTermLogDegreeBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpSplit
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_split : ∀ (p j : ℕ), 2 ≤ p →
    HasSum (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1)) := by
  intro p j hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hr : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left ((j : ℝ) / p)
  have hf : (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) =
      fun n : ℕ => (j : ℝ) / p * (1 / (p : ℝ)) ^ n := by
    funext n
    rw [one_div_pow, pow_succ]
    field_simp
  have hv : (j : ℝ) / ((p : ℝ) - 1) = (j : ℝ) / p * (1 - 1 / (p : ℝ))⁻¹ := by
    rw [one_sub_div h0, inv_div]
    field_simp
  rw [hf, hv]
  exact hs

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpInert
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_inert : ∀ (p N j : ℕ), 2 ≤ p → j ≤ N → HasSum (fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ |((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)| ≤ N / ((p : ℝ) - 1) := by
  intro p N j hp hjN
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpsq : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp0' : (p : ℝ) ≠ 0 := hp0.ne'
  have hp1' : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hpsq' : (p : ℝ) ^ 2 - 1 ≠ 0 := hpsq.ne'
  refine ⟨?_, ?_⟩
  · have hr1 : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have hg := hasSum_geometric_of_lt_one (by positivity) hr1
    have hE : HasSum (fun k : ℕ => (if Even (2 * k + 1) then (j : ℝ) else (N : ℝ) - j) /
        (p : ℝ) ^ (2 * k + 1)) (((N : ℝ) - j) / p * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
      have hf : (fun k : ℕ => (if Even (2 * k + 1) then (j : ℝ) else (N : ℝ) - j) /
          (p : ℝ) ^ (2 * k + 1)) = fun k => ((N : ℝ) - j) / p * ((p : ℝ) ^ 2)⁻¹ ^ k := by
        funext k
        rw [if_neg (Nat.not_even_two_mul_add_one k), inv_pow, ← pow_mul, pow_succ,
          ← div_eq_mul_inv, div_div, mul_comm ((p : ℝ) ^ (2 * k)) (p : ℝ)]
      rw [hf]
      exact hg.mul_left _
    have hO : HasSum (fun k : ℕ => (if Even (2 * k + 1 + 1) then (j : ℝ) else (N : ℝ) - j) /
        (p : ℝ) ^ (2 * k + 1 + 1)) ((j : ℝ) / (p : ℝ) ^ 2 * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
      have hf : (fun k : ℕ => (if Even (2 * k + 1 + 1) then (j : ℝ) else (N : ℝ) - j) /
          (p : ℝ) ^ (2 * k + 1 + 1)) = fun k => (j : ℝ) / (p : ℝ) ^ 2 * ((p : ℝ) ^ 2)⁻¹ ^ k := by
        funext k
        rw [if_pos ⟨k + 1, by ring⟩, inv_pow, ← pow_mul, ← div_eq_mul_inv, div_div, ← pow_add,
          show 2 * k + 1 + 1 = 2 + 2 * k by ring]
      rw [hf]
      exact hg.mul_left _
    have h := HasSum.even_add_odd (f := fun n : ℕ =>
      (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)) hE hO
    have hinv : (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ = (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) := by
      rw [show (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 by
        rw [sub_div, div_self (pow_ne_zero 2 hp0'), one_div], inv_div]
    have hv : (j : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1) =
        ((N : ℝ) - j) / p * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ + (j : ℝ) / (p : ℝ) ^ 2 * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
      rw [hinv]
      field_simp
      ring
    rw [hv]
    exact h
  · have hA : |(N : ℝ) - 2 * j| ≤ N := abs_le.2 ⟨by linarith, by linarith⟩
    rw [abs_div, abs_mul, abs_of_pos hp0, abs_of_pos hpsq, div_le_div_iff₀ hpsq hp1]
    nlinarith [abs_nonneg ((N : ℝ) - 2 * j),
      mul_le_mul_of_nonneg_right hA (by nlinarith : (0 : ℝ) ≤ p * (p - 1)),
      mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hp1.le]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaTermLogDegreeBound
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem deltaTerm_one : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  intro Ψ _ _ N j p τ fr hj hp
  refine ⟨Bound₂.ep N j p fr, Bound₂.abs_ep_le hj hp fr, fun h => ?_, fun h => ?_,
    fun Q => Bound₂.delta_one hj p τ fr Q⟩
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1) := by
      funext n
      obtain ⟨σ, hσ⟩ := h n
      rw [hσ, inv_pow, div_eq_inv_mul]
      rfl
    unfold Bound₂.ep
    rw [e, (ep_split p j hp).tsum_eq, sub_self]
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1) := by
      funext n
      rw [inv_pow, div_eq_inv_mul]
      congr 1
      rcases hs : fr n with σ | σ
      · have : Odd n := (h n).1 ⟨σ, hs⟩
        rw [if_pos this.add_one]
        rfl
      · have : ¬ Odd n := fun ho => by
          obtain ⟨σ', h'⟩ := (h n).2 ho
          rw [hs] at h'
          cases h'
        rw [if_neg (by simpa [Nat.even_add_one] using this)]
        rfl
    unfold Bound₂.ep
    rw [e, (ep_inert p N j hp hj).1.tsum_eq]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaTermLogDegreeBoundStatement
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_term_log_degree_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one | exact GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropFTopHolds
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

def propFTopE {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (p : ℕ) (τ : Ψ) : ℝ :=
  if hp : 2 ≤ p then Classical.choose (GlobalTheory.T.delta_term_log_degree_bound Ψ N T.j p τ (frob p τ) T.j_lt.le hp) else 0

theorem propFTopE_spec {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (p : ℕ) (τ : Ψ) (hp : 2 ≤ p) :
    |propFTopE T frob p τ| ≤ N / ((p : ℝ) - 1) ∧
      ∀ Q : RP Ψ N, deltaTerm T.j p τ (frob p τ) 1 Q = propFTopE T frob p τ * Real.log p * degFl Q := by
  have h := Classical.choose_spec (GlobalTheory.T.delta_term_log_degree_bound Ψ N T.j p τ (frob p τ) T.j_lt.le hp)
  simp only [propFTopE, dif_pos hp]
  exact ⟨h.1, h.2.2.2⟩

theorem propFTop : PropFTop := by
  intro hPI hML hDS Ψ _ _ N T II frob rd Lval hII hConv hProp hP6 hrd hbad hNear
  classical
  choose R hR using hNear
  let good : ℕ → Finset ℕ := fun B => (Finset.Ioc 2 B).filter (fun p => p.Prime ∧ p ∉ T.bad)
  refine ⟨fun B c τ => (R c τ).ht - ∑ p ∈ good B, propFTopE T frob p τ * Real.log p, ?_, ?_⟩
  · intro B hB c τ Q hQ
    have hN : 1 ≤ N := by have := T.j_pos; have := T.j_lt; omega
    have hQ' : Q.IsHomogeneous (dimFl Ψ N + 1 - 1) := by rwa [Nat.add_sub_cancel]
    have h6 := hP6 2 B le_rfl hB c τ 1 le_rfl hN Q hQ'
    have hroot := GlobalTheory.T.root_flat_pushforward_geoFun hPI hML hDS Ψ N (T.M 2 c) II τ (R c τ) Q hII (hConv 2 c) hQ
    have hgeo := hProp.2.1 2 c Q
    have hd : ∀ p ∈ good B, deltaTerm T.j p τ (frob p τ) 1 Q = propFTopE T frob p τ * Real.log p * degFl Q :=
      fun p hp => (propFTopE_spec T frob p τ (Finset.mem_filter.mp hp).2.1.two_le).2 Q
    have h2 : T.PPc II 2 c (pk τ 1 * Q) = (R c τ).ht * (T.vol c * degFl Q) := by
      simp only [RootTower.PPc]; rw [hroot, hgeo]
    rw [Finset.sum_congr rfl hd] at h6
    rw [sub_mul, Finset.sum_mul]
    rw [h2] at h6
    rw [← Finset.sum_mul] at h6 ⊢
    change _ = _ + T.vol c * ((∑ p ∈ good B, propFTopE T frob p τ * Real.log p) * degFl Q) at h6
    linarith [h6]
  · intro B hB hcard c τ
    obtain ⟨hrec, d, v, hrec_le, hEq, hdv, hvsum⟩ := hR c τ
    have hdisj : Disjoint T.bad (good B) :=
      Finset.disjoint_left.mpr fun p hp hg => (Finset.mem_filter.mp hg).2.2 hp
    let d' : ℕ → ℝ := fun p => if p ∈ T.bad then d p else -(propFTopE T frob p τ * Real.log p)
    let v' : ℕ → ℝ := fun p => if p ∈ T.bad then v p else 0
    have hsb : ∑ p ∈ T.bad, d' p = ∑ p ∈ T.bad, d p :=
      Finset.sum_congr rfl fun p hp => by simp [d', hp]
    have hsg : ∑ p ∈ good B, d' p = -∑ p ∈ good B, propFTopE T frob p τ * Real.log p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => by
        simp [d', Finset.disjoint_right.mp hdisj hp]
    have hvb : ∑ p ∈ T.bad ∪ good B, v' p * Real.log p = ∑ p ∈ T.bad, v p * Real.log p := by
      rw [Finset.sum_union hdisj]
      have h1 : ∑ p ∈ T.bad, v' p * Real.log p = ∑ p ∈ T.bad, v p * Real.log p :=
        Finset.sum_congr rfl fun p hp => by simp [v', hp]
      have h2 : ∑ p ∈ good B, v' p * Real.log p = 0 :=
        Finset.sum_eq_zero fun p hp => by simp [v', Finset.disjoint_right.mp hdisj hp]
      rw [h1, h2, add_zero]
    have hS : ∀ p ∈ T.bad ∪ good B, p.Prime ∧ (p ≤ B ∨ p ∈ T.bad) := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨hbad p hp, Or.inr hp⟩
      · have := Finset.mem_filter.mp hp
        exact ⟨this.2.1, Or.inl (Finset.mem_Ioc.mp this.1).2⟩
    have hB3 : 3 ≤ B := by omega
    have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
    have hmain := hB_bound N T.j B (T.bad ∪ good B) d' v' (Real.log rd) Lval hrec
      ((R c τ).ht - ∑ p ∈ good B, propFTopE T frob p τ * Real.log p) T.j_lt.le hB3 hlrd hrec_le
      (by rw [Finset.sum_union hdisj, hsb, hsg, hEq]; ring)
      (fun p hp => (hS p hp).1)
      (fun p hp => by
        by_cases hb : p ∈ T.bad
        · simp only [v', hb, if_true]; exact (hdv p hb).1
        · simp [v', hb])
      (fun p hp => by
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        by_cases hb : p ∈ T.bad
        · simp only [d', v', hb, if_true]
          refine (hdv p hb).2.trans (le_of_eq ?_)
          ring
        · simp only [d', v', hb, if_false, mul_zero, add_zero, abs_neg, abs_mul, abs_of_nonneg hlog]
          exact mul_le_mul_of_nonneg_right
            (propFTopE_spec T frob p τ (hS p hp).1.two_le).1 hlog)
      (by rw [hvb]; exact hvsum)
      (GlobalTheory.T.sum_log_prime_div_pred_bound B T.bad (T.bad ∪ good B) hB hcard hS)
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hrdpos : (0 : ℝ) < rd := by linarith
    simp only [bigLam]
    rw [Real.log_mul hBpos.ne' hrdpos.ne']
    simpa [add_assoc] using hmain

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropFTopHoldsStatement
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PropFTop_holds : PropFTop := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.propFTop | exact GlobalTheory.CompanionTheory.Ar.Flat.propFTop | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.propFTop <;> assumption)
end
