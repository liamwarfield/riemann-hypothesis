module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import GroundTheory.AutomorphicForms.GeometricLemma

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.OnlyStab

section Core

variable {K : Type} [Field K] {n : ℕ}

theorem prof_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ} (hk : k ≤ n) : 0 ≤ prof n τ k := by
  have h : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold prof
  exact mul_nonneg (mul_nonneg hτ h0) (by linarith)

theorem finrank_le_n (W : Submodule K (Fin n → K)) : Module.finrank K W ≤ n := by
  simpa using Submodule.finrank_le W

theorem prof_second_diff (τ : ℝ) (a b k : ℕ) (hab : a + b = 2 * k) :
    prof n τ a + prof n τ b = 2 * prof n τ k - 2 * τ * ((k : ℝ) - a) ^ 2 := by
  have h : (b : ℝ) = 2 * k - a := by
    have : ((a + b : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [hab]
    push_cast at this
    linarith
  unfold prof
  rw [h]
  ring

theorem core (deg' : Submodule K (Fin n → K) → ℝ) (g : Submodule K (Fin n → K) → Submodule K (Fin n → K))
    (τ D : ℝ) (hτ : 0 < τ) (hD : D < 2 * τ) (hbdd : BddAbove (Set.range deg'))
    (hsub : ∀ W W', deg' W + deg' W' ≤ deg' (W ⊓ W') + deg' (W ⊔ W'))
    (hmove : ∀ W, deg' W - D ≤ deg' (g W))
    (hrank : ∀ W, Module.finrank K (g W) = Module.finrank K W)
    (hst : ∀ W, g W = W → deg' W ≤ prof n τ (Module.finrank K W)) (W₀ : Submodule K (Fin n → K)) :
    deg' W₀ ≤ prof n τ (Module.finrank K W₀) := by
  by_contra hW₀
  push Not at hW₀
  set ψ : Submodule K (Fin n → K) → ℝ := fun W => deg' W - prof n τ (Module.finrank K W) with hψ
  have hψb : BddAbove (Set.range ψ) := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B, ?_⟩
    rintro _ ⟨W, rfl⟩
    have h1 : deg' W ≤ B := hB ⟨W, rfl⟩
    have h2 := prof_nonneg (n := n) hτ.le (finrank_le_n W)
    simp only [hψ]
    linarith
  set s : ℝ := ⨆ W, ψ W with hs
  have hle : ∀ W, ψ W ≤ s := fun W => le_ciSup hψb W
  have hs0 : 0 < s := lt_of_lt_of_le (by simp only [hψ]; linarith) (hle W₀)
  have hε : 0 < min s (τ - D / 2) := lt_min hs0 (by linarith)
  obtain ⟨W, hW⟩ : ∃ W, s - min s (τ - D / 2) < ψ W :=
    exists_lt_of_lt_ciSup (by rw [hs]; linarith [hε])
  have hε1 : min s (τ - D / 2) ≤ s := min_le_left _ _
  have hε2 : min s (τ - D / 2) ≤ τ - D / 2 := min_le_right _ _
  by_cases hg : g W = W
  · have h := hst W hg
    simp only [hψ] at hW
    linarith
  · have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (g W)
    rw [hrank W] at hsum
    have hne : W ⊓ g W ≠ W := fun h => hg
      (Submodule.eq_of_le_of_finrank_le (inf_eq_left.1 h) (by rw [hrank W])).symm
    have hlt : Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) < Module.finrank K W :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
    have hid := prof_second_diff (n := n) τ (Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)))
      (Module.finrank K (W ⊔ g W : Submodule K (Fin n → K))) (Module.finrank K W) (by omega)
    have hj : (1 : ℝ) ≤ (Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) := by
      have : ((Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) + 1 : ℕ) : ℝ) ≤ Module.finrank K W := by
        exact_mod_cast hlt
      push_cast at this
      linarith
    have hj2 : τ * 1 ≤ τ * ((Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K))) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hτ.le
    have h1 := hle (W ⊓ g W)
    have h2 := hle (W ⊔ g W)
    have h3 := hsub W (g W)
    have h4 := hmove W
    simp only [hψ] at h1 h2 hW
    linarith

end Core

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finrank_img (g : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    Module.finrank E (img g W) = Module.finrank E W := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro a b hab
    have h : (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ a) = (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ b) := by
      simpa [Matrix.toLin'_apply] using congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W).symm

theorem conjSrc_invol (v : HeightOneSpectrum (𝓞 E)) :
    conjSrc (IsCMField.complexConj E).toRingEquiv (conjSrc (IsCMField.complexConj E).toRingEquiv v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v ((IsCMField.complexConj E).toRingEquiv x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

theorem conjFin_invol (x : Af E) :
    conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => key v _ (conjSrc_invol v) (conjLoc _ v ∘ conjLoc _ _)
    ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_
  rw [Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

theorem pInf_conj (x : Ad E) : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem conjAd_invol (x : Ad E) : conjAd E (conjAd E x) = x :=
  ad_ext (by rw [pInf_conj, pInf_conj, starRingEnd_self_apply]) (conjFin_invol _)

theorem thetaA_invol (x : GA E n) : thetaA E n (thetaA E n x) = x := by
  refine Units.ext ?_
  ext i j
  change conjAd E (conjAd E (x.val i j)) = x.val i j
  exact conjAd_invol _

theorem ratGL_thetaE (d : GL (Fin n) E) : ratGL E n (thetaE E n d) = thetaA E n (ratGL E n d) := by
  refine Units.ext ?_
  ext i j
  have h : ((ratGL E n d)⁻¹ : GA E n) = ratGL E n d⁻¹ := (map_inv _ _).symm
  rw [thetaR_val, h]
  change algebraMap E (Ad E) (conjE E ((d⁻¹ : GL (Fin n) E).val j i)) =
    conjAd E (algebraMap E (Ad E) ((d⁻¹ : GL (Fin n) E).val j i))
  rw [conjAd_algebraMap]
  rfl

theorem conj_nrm (x : GA E n) (d : GL (Fin n) E) :
    x⁻¹ * ratGL E n (nrm d) * x =
      twConj (thetaA E n) x (ratGL E n d) * thetaA E n (twConj (thetaA E n) x (ratGL E n d)) := by
  simp only [twConj, nrm, map_mul, map_inv, thetaA_invol, ratGL_thetaE]
  group

end Global

theorem arith (C₁ C₂ c L l τ : ℝ) (hL0 : 0 ≤ L) (hl0 : 0 ≤ l) (hl : l ≤ 2 * L + |c|)
    (hτ : (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) ≤ τ) :
    0 < τ ∧ C₁ * (1 + l) < 2 * τ ∧ C₂ * (1 + L) ≤ τ := by
  have ha : 0 ≤ |C₁| := abs_nonneg _
  have hb : 0 ≤ |C₂| := abs_nonneg _
  have hcc : 0 ≤ |c| := abs_nonneg _
  have hprod : 0 ≤ |C₁| * (2 + |c|) * (1 + L) := by positivity
  have hprod2 : 0 ≤ |C₂| * (1 + L) := by positivity
  have hτ' : 1 + L + |C₁| * (2 + |c|) * (1 + L) + |C₂| * (1 + L) ≤ τ := by
    calc _ = (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) := by ring
      _ ≤ τ := hτ
  have hτ0 : 0 < τ := by linarith
  refine ⟨hτ0, ?_, ?_⟩
  · have e1 : C₁ * (1 + l) ≤ |C₁| * (1 + l) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have e2 : |C₁| * (1 + l) ≤ |C₁| * (1 + (2 * L + |c|)) := mul_le_mul_of_nonneg_left (by linarith) ha
    have e3 : |C₁| * (1 + (2 * L + |c|)) ≤ |C₁| * (2 + |c|) * (1 + L) := by
      have : 0 ≤ |C₁| * (1 + |c| * L) := by positivity
      nlinarith
    linarith
  · have h3 : C₂ * (1 + L) ≤ |C₂| * (1 + L) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith

theorem onlyStable_of : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  intro hSub hMove hBdd hPair hSize E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hMove E n
  obtain ⟨C₂, h₂⟩ := hPair E n
  obtain ⟨-, hnn, hθ, c, hc⟩ := hSize E n
  refine ⟨1 + |C₁| * (2 + |c|) + |C₂|, fun τ x d hτ => ?_⟩
  have hls : logSize (x⁻¹ * ratGL E n (nrm d) * x) ≤
      2 * logSize (twConj (thetaA E n) x (ratGL E n d)) + |c| := by
    rw [conj_nrm]
    have h := hc (twConj (thetaA E n) x (ratGL E n d)) (thetaA E n (twConj (thetaA E n) x (ratGL E n d)))
    rw [hθ] at h
    have := le_abs_self c
    linarith
  obtain ⟨hτ0, hD, hC₂⟩ := arith C₁ C₂ c _ _ τ (hnn _) (hnn _) hls hτ
  constructor
  · exact fun h W _ => h.1 W
  · intro hst
    refine ⟨fun W => ?_, ?_⟩
    · exact core (deg x) (img (nrm d)) τ _ hτ0 hD ((hBdd E n).1 x) (hSub E n x) (fun W => h₁ x (nrm d) W)
        (fun W => finrank_img _ W) hst W
    · have h := (h₂ x d).2
      have := neg_abs_le (deg x (⊤ : Submodule E (Fin n → E)))
      linarith

end GlobalTheory.CompanionTheory.OnlyStab
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspacesStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.only_stable_subspaces : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  first | exact @GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | exact GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | (intros; apply GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotNorm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
  {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]

theorem ae_lt_top_of_normaliser {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    ∀ᵐ g ∂μG, ρ g < ∞ := by
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  set E : Set G := {g | ρ g = ∞} with hEdef
  have hE : MeasurableSet E := hρ.1 (measurableSet_singleton ∞)
  have hind : Measurable (E.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hE
  have hzero : ∀ g : G, ∫⁻ h : H, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μH = 0 := by
    intro g
    have hm : Measurable fun h : H => ρ ((h : G) * g) :=
      hρ.1.comp (measurable_subtype_coe.mul_const g)
    have hfin : ∀ᵐ h : H ∂μH, ρ ((h : G) * g) < ∞ :=
      ae_lt_top hm (by rw [hρ.2 g]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hfin] with h hh
    simp [hEdef, Set.indicator, hh.ne]
  have key : ∫⁻ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG ∂μH = 0 := by
    rw [lintegral_lintegral_swap]
    · simp [hzero]
    · exact (hind.comp hmulH).aemeasurable
  have h2 : ∀ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG = μG E := fun h => by
    rw [lintegral_mul_left_eq_self (E.indicator (1 : G → ℝ≥0∞)) (h : G),
      lintegral_indicator_one hE]
  simp only [h2, lintegral_const] at key
  have hne : μH Set.univ ≠ 0 := by
    intro h0
    have h1 := hρ.2 1
    rw [Measure.measure_univ_eq_zero.1 h0] at h1
    simp at h1
  have hE0 : μG E = 0 := (mul_eq_zero.1 key).resolve_right hne
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE0] with g hg
  exact lt_top_iff_ne_top.2 hg

theorem integral_nonneg_normaliser_eq {f : G → ℝ} (hf : Measurable f) (hf0 : ∀ g, 0 ≤ f g)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫ g, f g * (σ g).toReal ∂μG = (∫⁻ g, ENNReal.ofReal (f g) * σ g ∂μG).toReal := by
    intro σ hσ
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun g => mul_nonneg (hf0 g) ENNReal.toReal_nonneg)
      (hf.mul hσ.1.ennreal_toReal).aestronglyMeasurable]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [ENNReal.ofReal_mul (hf0 g), ENNReal.ofReal_toReal hg.ne]
  rw [aux hρ, aux hρ', lintegral_normaliser_eq (F := fun g => ENNReal.ofReal (f g))
    hf.ennreal_ofReal (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integrable_normaliser_iff {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG ↔
      Integrable (fun g => F g * ((ρ' g).toReal : ℂ)) μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫⁻ g, ‖F g * ((σ g).toReal : ℂ)‖ₑ ∂μG = ∫⁻ g, ‖F g‖ₑ * σ g ∂μG := by
    intro σ hσ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((σ g).toReal : ℂ), Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hg.ne]
  have hm : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      AEStronglyMeasurable (fun g => F g * ((σ g).toReal : ℂ)) μG := fun hσ =>
    (hF.mul (Complex.measurable_ofReal.comp hσ.1.ennreal_toReal)).aestronglyMeasurable
  have heq := lintegral_normaliser_eq (μG := μG) (F := fun g => ‖F g‖ₑ) hF.enorm
    (fun h hh g => by simp only [hFH h hh g]) hρ hρ'
  simp only [Integrable, hm hρ, hm hρ', true_and, hasFiniteIntegral_iff_enorm, aux hρ, aux hρ', heq]

theorem integral_real_normaliser_eq {f : G → ℝ} (hf : Measurable f)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ')
    (hi : Integrable (fun g => f g * (ρ g).toReal) μG)
    (hi' : Integrable (fun g => f g * (ρ' g).toReal) μG) :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have part : ∀ {σ : G → ℝ≥0∞} {u : G → ℝ}, IsQuotNormaliser H μH σ → Measurable u →
      (∀ g, |u g| ≤ |f g|) → Integrable (fun g => f g * (σ g).toReal) μG →
      Integrable (fun g => u g * (σ g).toReal) μG := by
    intro σ u hσ hu hle h
    refine h.mono (hu.mul hσ.1.ennreal_toReal).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle g) (abs_nonneg _)
  have hp : Measurable fun g => max (f g) 0 := hf.max measurable_const
  have hn : Measurable fun g => max (-f g) 0 := hf.neg.max measurable_const
  have hpl : ∀ g, |max (f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnl : ∀ g, |max (-f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have dec : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      Integrable (fun g => f g * (σ g).toReal) μG →
      ∫ g, f g * (σ g).toReal ∂μG =
        ∫ g, max (f g) 0 * (σ g).toReal ∂μG - ∫ g, max (-f g) 0 * (σ g).toReal ∂μG := by
    intro σ hσ h
    rw [← integral_sub (part hσ hp hpl h) (part hσ hn hnl h)]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    have : f g = max (f g) 0 - max (-f g) 0 := (max_zero_sub_max_neg_zero_eq_self (f g)).symm
    simp only
    rw [← sub_mul, ← this]
  rw [dec hρ hi, dec hρ' hi',
    integral_nonneg_normaliser_eq hp (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ',
    integral_nonneg_normaliser_eq hn (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integral_normaliser_eq_of {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μG := by
  have hiff := integrable_normaliser_iff (μG := μG) hF hFH hρ hρ'
  by_cases hi : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG
  · have hi' := hiff.1 hi
    have ere : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).re * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).re = ∫ g, (F g).re * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.reCLM.integrable_comp h
      have h2 := Complex.reCLM.integral_comp_comm h
      simp only [Complex.reCLM_apply, Complex.re_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    have eim : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).im * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).im = ∫ g, (F g).im * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.imCLM.integrable_comp h
      have h2 := Complex.imCLM.integral_comp_comm h
      simp only [Complex.imCLM_apply, Complex.im_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    apply Complex.ext
    · rw [(ere hi).2, (ere hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_re.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (ere hi).1 (ere hi').1
    · rw [(eim hi).2, (eim hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_im.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (eim hi).1 (eim hi').1
  · rw [integral_undef hi, integral_undef (fun h => hi (hiff.2 h))]

theorem quotIntegral_eq {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    quotIntegral μG H μH F = ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG := by
  have hex : ∃ ρ, IsQuotNormaliser H μH ρ := ⟨ρ, hρ⟩
  rw [quotIntegral, dite_eq_left hex]
  exact integral_normaliser_eq_of hF hFH hex.choose_spec hρ

theorem integral_normaliser_eq : PositivityTheory.Rg.BcB.D4.NormEq := by
  intro G _ _ _ _ _ _ _ μ _ H μH _ _ F ρ₁ ρ₂ hF hFH hρ₁ hρ₂
  exact integral_normaliser_eq_of (μG := μ) hF hFH hρ₁ hρ₂

end GlobalTheory.CompanionTheory.QuotNorm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
noncomputable section

open NumberField IsDedekindDomain PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.LogAbs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem norm_cW_eq_one (u : Ad E) (hu : IsUnit u) : ∀ᶠ w in Filter.cofinite, ‖cW w u‖ = 1 := by
  have h := (FiniteAdeleRing.isUnit_iff.1 (hu.map (pFin E))).2
  filter_upwards [h] with w hw
  have e : cW w u = (pFin E u) w := rfl
  rw [e, FinitePlace.norm_def, hw]
  simp

theorem support_log_finite (u : Ad E) (hu : IsUnit u) :
    (Function.support fun w => Real.log ‖cW w u‖).Finite := by
  refine (Filter.eventually_cofinite.1 (norm_cW_eq_one u hu)).subset fun w hw h1 => hw ?_
  simp [h1]

theorem logAbs_mul (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') :
    logAbs (u * u') = logAbs u + logAbs u' := by
  have h1 : ∀ v, Real.log (‖cV v (u * u')‖ ^ 2) = Real.log (‖cV v u‖ ^ 2) + Real.log (‖cV v u'‖ ^ 2) := fun v => by
    rw [map_mul, norm_mul, mul_pow, Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero))
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu'.map (cV v)).ne_zero))]
  have h2 : ∀ w, Real.log ‖cW w (u * u')‖ = Real.log ‖cW w u‖ + Real.log ‖cW w u'‖ := fun w => by
    rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero)
      (norm_ne_zero_iff.2 (hu'.map (cW w)).ne_zero)]
  unfold logAbs
  simp only [h1, h2]
  rw [Finset.sum_add_distrib, finsum_add_distrib (support_log_finite u hu) (support_log_finite u' hu')]
  ring

theorem norm_cV_algebraMap (v : InfinitePlace E) (c : E) : ‖cV v (algebraMap E (Ad E) c)‖ = v c := by
  rw [← InfinitePlace.norm_embedding_eq]
  exact congrArg norm (pInf_algebraMap c v)

theorem norm_cW_algebraMap (w : HeightOneSpectrum (𝓞 E)) (c : E) :
    ‖cW w (algebraMap E (Ad E) c)‖ = FinitePlace.mk w c := rfl

theorem logAbs_algebraMap (c : E) (hc : c ≠ 0) : logAbs (algebraMap E (Ad E) c) = 0 := by
  have hprod := prod_abs_eq_one hc
  have hA : (∏ w : InfinitePlace E, w c ^ w.mult) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hB : (∏ᶠ w : FinitePlace E, w c) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA hB, Real.log_one, Real.log_prod (fun w _ => pow_ne_zero _ ((InfinitePlace.pos_iff.2 hc).ne')),
    Real.log_finprod fun w : FinitePlace E => FinitePlace.pos_iff.2 hc] at hlog
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  unfold logAbs
  simp only [norm_cV_algebraMap, norm_cW_algebraMap]
  simp only [hm] at hlog
  rw [← hlog, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  rfl

theorem logAbsBasic : LogAbsBasic := fun _ _ _ _ =>
  ⟨support_log_finite, logAbs_mul, logAbs_algebraMap⟩

end GlobalTheory.CompanionTheory.LogAbs

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFactsStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_abs_basic_facts : LogAbsBasic := by
  first | exact @GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | exact GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | (intros; apply GlobalTheory.CompanionTheory.LogAbs.logAbsBasic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.Dblock.SzFinProof

theorem finite_one_lt_norm_cW {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : Ad E) :
    {w : HeightOneSpectrum (𝓞 E) | 1 < ‖cW w a‖}.Finite := by
  delta PositivityTheory.Rg.BcB.cW GlobalTheory.CuspRep.pLoc GlobalTheory.CuspRep.pFin
  have h := RestrictedProduct.eventually _ _ (RingHom.snd (InfiniteAdeleRing E) (Af E) a)
  refine (Filter.eventually_cofinite.mp h).subset ?_
  intro w hw
  simp only [Set.mem_ofPred_eq, RingHom.comp_apply, RestrictedProduct.evalRingHom_apply] at hw ⊢
  intro hmem
  exact absurd hw (not_lt.mpr (Valued.toNormedField.norm_le_one_iff.mpr
    ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem)))

theorem szFin : SzFin := by
  intro E _ _ _ ι κ _ _ A
  refine (Set.Finite.biUnion (s := (Set.univ : Set (ι × κ))) Set.finite_univ
    fun p _ => finite_one_lt_norm_cW (A p.1 p.2)).subset ?_
  intro w hw
  change 1 < ⨆ p : ι × κ, ‖(A.map (PositivityTheory.Rg.BcB.cW w)) p.1 p.2‖ at hw
  rcases isEmpty_or_nonempty (ι × κ) with hι | hι
  · rw [Real.iSup_of_isEmpty] at hw
    exact absurd hw (by norm_num)
  · obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hw
    exact Set.mem_biUnion (Set.mem_univ p) hp

end GlobalTheory.CompanionTheory.Dblock.SzFinProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlacesStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_finite_places : SzFin := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin | exact GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin | (intros; apply GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormula
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegAdelicProof

theorem exists_leftInv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ L : Matrix (Fin k) (Fin n) K, L * M = 1 := by
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' M) = 1 := by
    rw [Matrix.toLin'_apply', hg, LinearMap.toMatrix'_id]
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n k : ℕ}

theorem frame_mul (x t : GA E n) (s : GA E k) (M : Matrix (Fin n) (Fin k) E)
    (h : t.val * M.map (algebraMap E (Ad E)) = M.map (algebraMap E (Ad E)) * s.val) :
    frame (t * x) M = frame x M * (s⁻¹ : GA E k).val := by
  have h' : (t⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) =
      M.map (algebraMap E (Ad E)) * (s⁻¹ : GA E k).val := by
    calc (t⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))
        = (t⁻¹ : GA E n).val * (M.map (algebraMap E (Ad E)) * (s.val * (s⁻¹ : GA E k).val)) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = (t⁻¹ : GA E n).val * (t.val * M.map (algebraMap E (Ad E))) * (s⁻¹ : GA E k).val := by
          rw [h, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = M.map (algebraMap E (Ad E)) * (s⁻¹ : GA E k).val := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, h', Matrix.mul_assoc]

theorem lognInf_mul (hI : MulI) (v : InfinitePlace E) (A : Matrix (Fin n) (Fin k) (Ad E))
    (S : Matrix (Fin k) (Fin k) (Ad E)) (hA : nI (A.map (cV v)) ≠ 0) (hS : IsUnit S.det) :
    lognInf v (A * S) = lognInf v A + Real.log (‖cV v S.det‖ ^ 2) := by
  have hd : (S.map (cV v)).det = cV v S.det := (RingHom.map_det (cV v) S).symm
  have h0 : cV v S.det ≠ 0 := (hS.map (cV v)).ne_zero
  change Real.log (nI ((A * S).map (cV v))) = Real.log (nI (A.map (cV v))) + _
  rw [Matrix.map_mul, (hI (Fin n) (Fin n) (Fin k) _).2.1, hd,
    Real.log_mul hA (pow_ne_zero 2 (norm_ne_zero_iff.2 h0))]

theorem lognFin_mul (hF : MulF) (w : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (S : Matrix (Fin k) (Fin k) (Ad E)) (hA : nF (A.map (cW w)) ≠ 0) (hS : IsUnit S.det) :
    lognFin w (A * S) = lognFin w A + Real.log ‖cW w S.det‖ := by
  have hd : (S.map (cW w)).det = cW w S.det := (RingHom.map_det (cW w) S).symm
  have h0 : cW w S.det ≠ 0 := (hS.map (cW w)).ne_zero
  change Real.log (nF ((A * S).map (cW w))) = Real.log (nF (A.map (cW w))) + _
  rw [Matrix.map_mul, (hF _ (Fin n) (Fin n) (Fin k) _).2.1, hd,
    Real.log_mul hA (norm_ne_zero_iff.2 h0)]

theorem logAbs_inv (hL : LogAbsBasic) (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') (h : u * u' = 1) :
    logAbs u = -logAbs u' := by
  have h1 := (hL E).2.1 u u' hu hu'
  have h2 := (hL E).2.2 1 one_ne_zero
  rw [map_one] at h2
  rw [h, h2] at h1
  linarith

theorem frame_leftInv (x : GA E n) (M : Matrix (Fin n) (Fin k) E) (L : Matrix (Fin k) (Fin n) E)
    (hLM : L * M = 1) :
    (L.map (algebraMap E (Ad E)) * x.val) * frame x M = 1 := by
  unfold frame
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul,
    ← Matrix.map_mul, hLM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem degAdelic_of (hF : MulF) (hI : MulI) (hL : LogAbsBasic) (hS : FinSupp) : DegAdelic := by
  intro E _ _ _ n k x t s M hM h
  obtain ⟨L, hLM⟩ := exists_leftInv M hM
  obtain ⟨h1, h2, h3⟩ := hS E (Fin n) (Fin k) (frame x M) _ (frame_leftInv x M L hLM)
  have hδ : IsUnit (s⁻¹ : GA E k).val.det := Matrix.isUnits_det_units _
  have hs : IsUnit s.val.det := Matrix.isUnits_det_units _
  have hmul : (s⁻¹ : GA E k).val.det * s.val.det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  have hinv := logAbs_inv hL _ _ hδ hs hmul
  have hfin₁ : (Function.support fun w => lognFin w (frame x M)).Finite := by
    refine h3.subset fun w hw hw1 => hw ?_
    change Real.log (nF ((frame x M).map (cW w))) = 0
    rw [show nF ((frame x M).map (cW w)) = 1 from hw1, Real.log_one]
  have hfin₂ := (hL E).1 _ hδ
  rw [degM, degM, frame_mul x t s M h]
  have e₁ : ∀ v, lognInf v (frame x M * (s⁻¹ : GA E k).val) =
      lognInf v (frame x M) + Real.log (‖cV v (s⁻¹ : GA E k).val.det‖ ^ 2) :=
    fun v => lognInf_mul hI v _ _ (h1 v) hδ
  have e₂ : ∀ w, lognFin w (frame x M * (s⁻¹ : GA E k).val) =
      lognFin w (frame x M) + Real.log ‖cW w (s⁻¹ : GA E k).val.det‖ :=
    fun w => lognFin_mul hF w _ _ (h2 w) hδ
  simp_rw [e₁, e₂]
  rw [Finset.sum_add_distrib, finsum_add_distrib hfin₁ hfin₂]
  unfold logAbs at hinv ⊢
  linarith

end GlobalTheory.CompanionTheory.DegAdelicProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormulaStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_degree_formula : MulF → MulI → LogAbsBasic → FinSupp → DegAdelic := by
  first | exact @GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | exact GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | (intros; apply GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodular
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodular
open MeasureTheory Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.GLUnimod

variable {n : ℕ}

noncomputable def dg (d : Fin n → ℂˣ) : GL (Fin n) ℂ where
  val := diagonal fun i => (d i : ℂ)
  inv := diagonal fun i => (((d i)⁻¹ : ℂˣ) : ℂ)
  val_inv := by simp [diagonal_mul_diagonal, diagonal_one]
  inv_val := by simp [diagonal_mul_diagonal, diagonal_one]

theorem dg_mul (d e : Fin n → ℂˣ) : dg (d * e) = dg d * dg e := by
  apply Units.ext
  simp [dg, diagonal_mul_diagonal]

theorem dg_one : dg (1 : Fin n → ℂˣ) = 1 := by
  apply Units.ext
  simp [dg, diagonal_one]

noncomputable def pm (σ : Equiv.Perm (Fin n)) : GL (Fin n) ℂ where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.one_apply]
  inv_val := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.one_apply]

theorem pm_mul_dg (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂˣ) :
    pm σ * dg d = dg (d ∘ σ) * pm σ := by
  ext1
  ext i j
  simp only [pm, dg, Units.val_mul, mul_diagonal, diagonal_mul, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Function.comp_apply]
  split_ifs with h
  · subst h
    ring
  · ring

noncomputable def tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) : GL (Fin n) ℂ where
  val := transvection i j c
  inv := transvection i j (-c)
  val_inv := by rw [transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [transvection_mul_transvection_same _ _ hij]; simp

theorem tv_mul {i j : Fin n} (hij : i ≠ j) (c : ℂ) : tv hij c * tv hij c = tv hij (2 * c) := by
  ext1
  simp only [tv, Units.val_mul]
  rw [transvection_mul_transvection_same _ _ hij, two_mul]

theorem dg_mul_tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) (d : Fin n → ℂˣ) (hi : (d i : ℂ) = 2)
    (hj : (d j : ℂ) = 1) : dg d * tv hij c = tv hij (2 * c) * dg d := by
  ext1
  ext k l
  simp only [dg, tv, Units.val_mul, transvection, diagonal_mul, mul_diagonal, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hk : i = k <;> by_cases hl : j = l
  · subst hk hl
    simp [hij, hi, hj]
  · subst hk
    simp [hl]
    split_ifs with h <;> simp only [h]
  · subst hl
    simp [hk]
    split_ifs with h <;> simp only [h]
  · simp [hk, hl]
    split_ifs with h <;> simp only [h]

theorem char_ne_zero {H : Type*} [Group H] (χ : H →* ℝ≥0) (g : H) : χ g ≠ 0 := by
  intro h
  have h1 : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem char_tv (χ : GL (Fin n) ℂ →* ℝ≥0) {i j : Fin n} (hij : i ≠ j) (c : ℂ) :
    χ (tv hij c) = 1 := by
  have h1 : χ (tv hij c) * χ (tv hij c) = χ (tv hij (2 * c)) := by rw [← map_mul, tv_mul]
  let d : Fin n → ℂˣ := fun k => if k = i then Units.mk0 2 two_ne_zero else 1
  have hi : (d i : ℂ) = 2 := by simp [d]
  have hj : (d j : ℂ) = 1 := by simp [d, hij.symm]
  have h2 : χ (dg d) * χ (tv hij c) = χ (tv hij (2 * c)) * χ (dg d) := by
    rw [← map_mul, ← map_mul, dg_mul_tv hij c d hi hj]
  have h3 : χ (tv hij c) = χ (tv hij (2 * c)) := by
    rw [mul_comm (χ (tv hij (2 * c)))] at h2
    exact mul_left_cancel₀ (char_ne_zero χ _) h2
  have h4 : χ (tv hij c) * χ (tv hij c) = χ (tv hij c) * 1 := by rw [mul_one, h1, h3]
  exact mul_left_cancel₀ (char_ne_zero χ _) h4

theorem char_dg (χ : GL (Fin n) ℂ →* ℝ≥0) (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1)
    (d : Fin n → ℂˣ) : χ (dg d) = 1 := by
  let D : (Fin n → ℂˣ) →* GL (Fin n) ℂ :=
    { toFun := dg, map_one' := dg_one, map_mul' := dg_mul }
  have hperm : ∀ σ : Equiv.Perm (Fin n), χ (dg (d ∘ σ)) = χ (dg d) := by
    intro σ
    have h := congrArg χ (pm_mul_dg σ d)
    rw [map_mul, map_mul, mul_comm (χ (pm σ))] at h
    exact (mul_right_cancel₀ (char_ne_zero χ (pm σ)) h).symm
  obtain ⟨v, hv_def⟩ : ∃ v : Fin n → ℂˣ, v = ∏ σ : Equiv.Perm (Fin n), d ∘ σ := ⟨_, rfl⟩
  have hv : ∀ k l, v k = v l := by
    intro k l
    rw [hv_def, Finset.prod_apply, Finset.prod_apply]
    exact Fintype.prod_equiv (Equiv.mulRight (Equiv.swap k l)) _ _
      (fun σ => by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right])
  have hcent : ∀ g, dg v * g = g * dg v := by
    intro g
    ext1
    ext k l
    simp only [dg, Units.val_mul, diagonal_mul, mul_diagonal]
    rw [hv k l, mul_comm]
  have h1 : χ (dg v) = 1 := hz _ hcent
  have h2 : χ (dg v) = χ (dg d) ^ (Fintype.card (Equiv.Perm (Fin n))) := by
    have e : χ (dg v) = (χ.comp D) v := rfl
    rw [e, hv_def, map_prod]
    simp only [MonoidHom.comp_apply, D, MonoidHom.coe_mk, OneHom.coe_mk, hperm]
    rw [Finset.prod_const, Finset.card_univ]
  have hm : Fintype.card (Equiv.Perm (Fin n)) ≠ 0 := Fintype.card_ne_zero
  rw [h1] at h2
  exact (pow_eq_one_iff_of_nonneg (by simp) hm).1 h2.symm

theorem char_eq_one (χ : GL (Fin n) ℂ →* ℝ≥0)
    (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1) (g : GL (Fin n) ℂ) : χ g = 1 := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : GL (Fin n) ℂ, (u : Matrix (Fin n) (Fin n) ℂ) = M → χ u = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) ?_ ?_ ?_ ?_ g rfl
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  · intro D hD u hu
    rw [det_diagonal] at hD
    have hD' : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = dg (fun i => Units.mk0 (D i) (hD' i)) := by
      ext1
      simp [hu, dg]
    rw [hu']
    exact char_dg χ hz _
  · intro t u hu
    have hu' : u = tv t.hij t.c := by
      ext1
      simp [hu, tv, Matrix.TransvectionStruct.toMatrix]
    rw [hu']
    exact char_tv χ t.hij t.c
  · intro A B hA hB hPA hPB u hu
    obtain ⟨a, rfl⟩ : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA)
    obtain ⟨b, rfl⟩ : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB)
    have hu' : u = a * b := by
      ext1
      simp [hu]
    rw [hu', map_mul, hPA a rfl, hPB b rfl, one_mul]

theorem unimod : PositivityTheory.RgBcC.Unimod := by
  intro n _ _ μ _
  haveI : T2Space (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (T2Space (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (PositivityTheory.RgTw.G n) :=
    (Units.isClosedEmbedding_embedProduct :
      Topology.IsClosedEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).locallyCompactSpace
  haveI : SecondCountableTopology (PositivityTheory.RgTw.G n) :=
    (Units.isEmbedding_embedProduct :
      Topology.IsEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).secondCountableTopology
  have hmap : ∀ g : PositivityTheory.RgTw.G n,
      Measure.map (· * g) μ = Measure.modularCharacter g • μ := by
    intro g
    have e1 := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ g
    rw [← e2] at e1
    exact e1
  have hχ : ∀ g : PositivityTheory.RgTw.G n, Measure.modularCharacter g = 1 := by
    refine char_eq_one Measure.modularCharacter ?_
    intro z hz
    have hc : Measure.map (· * z) μ = μ := by
      have h : (fun x => x * z) = (fun x => z * x) := funext fun x => (hz x).symm
      rw [h, map_mul_left_eq_self]
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ z
    simp only [hc, Measure.haarScalarFactor_self] at e2
    exact e2
  have hR : μ.IsMulRightInvariant := ⟨fun g => by rw [hmap, hχ g, one_smul]⟩
  exact ⟨hR, GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ⟩

end GlobalTheory.CompanionTheory.GLUnimod
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodularStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.general_linear_group_unimodular : PositivityTheory.RgBcC.Unimod := by
  first | exact @GlobalTheory.CompanionTheory.GLUnimod.unimod | exact GlobalTheory.CompanionTheory.GLUnimod.unimod | (intros; apply GlobalTheory.CompanionTheory.GLUnimod.unimod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpper
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpper
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParabBridge

theorem parab_eq_blockUpper : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → parab k e = blockUpper k N β := by
  intro k _ _ _ _ α _ _ N m _ _ e β h
  ext g
  rw [mem_parab, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
  exact forall₂_congr fun i j => by rw [h j i]

end GlobalTheory.CompanionTheory.ParabBridge
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpperStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_eq_block_upper : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → parab k e = blockUpper k N β := by
  first | exact @GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper | exact GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper | (intros; apply GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper <;> assumption)
end
end
