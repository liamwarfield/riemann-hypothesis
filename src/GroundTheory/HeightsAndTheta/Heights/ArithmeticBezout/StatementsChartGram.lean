module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsZeroLocusDimH
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity)

def gramVol {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re

def ChartGramMA.Statement : Prop :=
  ∀ (e n : ℕ) (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ v y') → v y ≠ 0 →
      maDensity (fun _ y' => Real.log ‖WithLp.toLp 2 (v y')‖) y =
        (e.factorial : ℝ) / Real.pi ^ e * gramVol v y / ‖WithLp.toLp 2 (v y)‖ ^ (2 * (e + 1))

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ConeIntegralMass.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      coneIntegral h W e (fun _ => 1) = δ

def ChowFormBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I k f →
      (∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, IsProjPrime W) ∧
        IsChowFormCycle (fundCycle (I.map (MvPolynomial.map σ))) k (MvPolynomial.map σ f)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def BaseChangeAvoid.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (u : Fin n → K) (σ : K →+* ℂ), IsProjPrime I → linForm u ∉ I →
      ∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, linForm (fun j => σ (u j)) ∉ W

def coneBall {n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0}

def ConeBallFinite.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤

def ConeFsLogIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      IntegrableOn (fun y => fsLog h u (h.pointOf y)) (coneBall h W)
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))

def ConeHyperplaneNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) = 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem map_eq_maximalIdeal_of_isRadical {A : Type*} [CommRing A] {J W : Ideal A} [W.IsPrime]
    (hJ : J.IsRadical) (hW : W ∈ J.minimalPrimes) :
    J.map (algebraMap A (Localization.AtPrime W)) = IsLocalRing.maximalIdeal (Localization.AtPrime W) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W),
    ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W J hW,
    ← IsLocalization.map_radical W.primeCompl (Localization.AtPrime W) J, hJ.radical]

theorem localMult_eq_one_of_isRadical {A : Type*} [CommRing A] {J W : Ideal A} (hJ : J.IsRadical)
    (hW : W ∈ J.minimalPrimes) : localMult J W = 1 := by
  have hWp : W.IsPrime := hW.1.1
  unfold localMult
  rw [dite_eq_left hWp, map_eq_maximalIdeal_of_isRadical hJ hW]
  have : IsSimpleModule (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one]
  rfl

theorem fundCycle_apply_of_isRadical {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) R)} (hJ : J.IsRadical) {W : Ideal (MvPolynomial (Fin n) R)}
    (hW : W ∈ (fundCycle J).support) : fundCycle J W = 1 := by
  classical
  have hval : fundCycle J W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hrel : W ∈ relComps J := by
    by_contra h
    apply hval
    unfold fundCycle
    rw [Finsupp.onFinset_apply, if_neg h]
  unfold fundCycle
  rw [Finsupp.onFinset_apply, if_pos hrel]
  exact localMult_eq_one_of_isRadical hJ hrel.1

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

variable {m n : ℕ}

def coneSet (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {y | ∀ q ∈ J, eval (h.pointOf y) q = 0}

def linProj (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 fun i => ∑ j, π i j * y j

def fibreCount (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : ℕ∞ :=
  {y | y ∈ coneSet h J ∧ linProj π y = w}.encard

def ConeFibreDegree.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)),
        fibreCount h W π w = δ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

section General

variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)

def gaussNormOf (f : MvPolynomial ι R) : ℝ :=
  let s : NNReal := f.support.sup fun m => ⟨w (f.coeff m), w.nonneg _⟩
  (s : ℝ)

theorem gaussNormOf_def (f : MvPolynomial ι R) :
    gaussNormOf w f = (((f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) : NNReal) : ℝ) :=
  rfl

theorem gaussNormOf_nonneg (f : MvPolynomial ι R) : 0 ≤ gaussNormOf w f := NNReal.coe_nonneg _

theorem le_gaussNormOf (f : MvPolynomial ι R) (m : ι →₀ ℕ) : w (f.coeff m) ≤ gaussNormOf w f := by
  by_cases hm : m ∈ f.support
  · have h : (⟨w (f.coeff m), w.nonneg _⟩ : NNReal) ≤
        f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal) :=
      Finset.le_sup (f := fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) hm
    rw [gaussNormOf_def]
    exact NNReal.coe_le_coe.mpr h
  · rw [notMem_support_iff.mp hm, map_zero]
    exact gaussNormOf_nonneg w f

theorem gaussNormOf_le {f : MvPolynomial ι R} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m, w (f.coeff m) ≤ r) : gaussNormOf w f ≤ r := by
  have h' : (f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) ≤ ⟨r, hr⟩ :=
    Finset.sup_le fun m _ => h m
  rw [gaussNormOf_def]
  exact NNReal.coe_le_coe.mpr h'

theorem exists_gaussNormOf_eq {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ m ∈ f.support, gaussNormOf w f = w (f.coeff m) := by
  obtain ⟨m, hm, h⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal))
  refine ⟨m, hm, ?_⟩
  rw [gaussNormOf_def]
  exact congrArg Subtype.val h

theorem gaussNormOf_pos {f : MvPolynomial ι R} (hf : f ≠ 0) : 0 < gaussNormOf w f := by
  obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hf
  rw [h]
  exact w.pos (mem_support_iff.mp hm)

theorem gaussNormOf_zero : gaussNormOf w (0 : MvPolynomial ι R) = 0 :=
  le_antisymm (gaussNormOf_le w le_rfl fun m => by simp) (gaussNormOf_nonneg w 0)

theorem gaussNormOf_C (c : R) : gaussNormOf w (C c : MvPolynomial ι R) = w c := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (w.nonneg c) fun m => ?_
    rw [coeff_C]
    split_ifs
    · exact le_rfl
    · rw [map_zero]
      exact w.nonneg c
  · simpa using le_gaussNormOf w (C c : MvPolynomial ι R) 0

variable {w}

theorem gaussNormOf_mul_le (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) ≤ gaussNormOf w f * gaussNormOf w g := by
  classical
  refine gaussNormOf_le w (mul_nonneg (gaussNormOf_nonneg w f) (gaussNormOf_nonneg w g)) fun m => ?_
  rw [coeff_mul]
  refine (hna.apply_sum_le_sup (s := Finset.HasAntidiagonal.antidiagonal m) ⟨(0, m), by simp⟩).trans ?_
  refine Finset.sup'_le _ _ fun p _ => ?_
  rw [map_mul]
  exact mul_le_mul (le_gaussNormOf w f _) (le_gaussNormOf w g _) (w.nonneg _)
    (gaussNormOf_nonneg w f)

theorem le_gaussNormOf_mul (hna : IsNonarchimedean w) {f g : MvPolynomial ι R} (hf : f ≠ 0)
    (hg : g ≠ 0) : gaussNormOf w f * gaussNormOf w g ≤ gaussNormOf w (f * g) := by
  classical
  let _ : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hNf := gaussNormOf_pos w hf
  have hNg := gaussNormOf_pos w hg
  obtain ⟨i, hi, hmin_i⟩ :=
    (f.support.filter fun a => w (f.coeff a) = gaussNormOf w f).exists_min_image toLex (by
      obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hf
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h.symm⟩⟩)
  obtain ⟨j, hj, hmin_j⟩ :=
    (g.support.filter fun a => w (g.coeff a) = gaussNormOf w g).exists_min_image toLex (by
      obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hg
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h.symm⟩⟩)
  have hi' : w (f.coeff i) = gaussNormOf w f := (Finset.mem_filter.mp hi).2
  have hj' : w (g.coeff j) = gaussNormOf w g := (Finset.mem_filter.mp hj).2
  have ltf : ∀ a, toLex a < toLex i → w (f.coeff a) < gaussNormOf w f := by
    intro a ha
    refine lt_of_le_of_ne (le_gaussNormOf w f a) fun h => ?_
    have ha' : a ∈ f.support.filter fun a => w (f.coeff a) = gaussNormOf w f := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h⟩
      rw [h0, map_zero] at h
      exact hNf.ne h
    exact absurd (hmin_i a ha') (not_le.mpr ha)
  have ltg : ∀ a, toLex a < toLex j → w (g.coeff a) < gaussNormOf w g := by
    intro a ha
    refine lt_of_le_of_ne (le_gaussNormOf w g a) fun h => ?_
    have ha' : a ∈ g.support.filter fun a => w (g.coeff a) = gaussNormOf w g := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h⟩
      rw [h0, map_zero] at h
      exact hNg.ne h
    exact absurd (hmin_j a ha') (not_le.mpr ha)
  have key : w ((f * g).coeff (i + j)) = gaussNormOf w f * gaussNormOf w g := by
    rw [coeff_mul]
    have hk : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [hna.apply_sum_eq_of_lt _ (fun a => w.map_neg a) hk ?_, map_mul, hi', hj']
    intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_mul, map_mul, hi', hj']
    rcases lt_trichotomy (toLex p.1) (toLex i) with h | h | h
    · calc w (f.coeff p.1) * w (g.coeff p.2) ≤ w (f.coeff p.1) * gaussNormOf w g :=
            mul_le_mul_of_nonneg_left (le_gaussNormOf w g _) (w.nonneg _)
        _ < gaussNormOf w f * gaussNormOf w g := mul_lt_mul_of_pos_right (ltf _ h) hNg
    · have h1 : p.1 = i := toLex.injective h
      have h2 : p.2 = j := by
        rw [h1] at hp
        exact add_left_cancel hp
      exact absurd (Prod.ext h1 h2) hne
    · have h2 : toLex p.2 < toLex j := by
        by_contra hc
        rw [not_lt] at hc
        have hlt : toLex i + toLex j < toLex p.1 + toLex p.2 := add_lt_add_of_lt_of_le h hc
        have e : toLex p.1 + toLex p.2 = toLex i + toLex j := by
          rw [← toLex_add, ← toLex_add, hp]
        rw [e] at hlt
        exact lt_irrefl _ hlt
      calc w (f.coeff p.1) * w (g.coeff p.2) ≤ gaussNormOf w f * w (g.coeff p.2) :=
            mul_le_mul_of_nonneg_right (le_gaussNormOf w f _) (w.nonneg _)
        _ < gaussNormOf w f * gaussNormOf w g := mul_lt_mul_of_pos_left (ltg _ h2) hNf
  rw [← key]
  exact le_gaussNormOf w _ _

theorem gaussNormOf_mul (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) = gaussNormOf w f * gaussNormOf w g := by
  by_cases hf : f = 0
  · simp [hf, gaussNormOf_zero]
  by_cases hg : g = 0
  · simp [hg, gaussNormOf_zero]
  exact le_antisymm (gaussNormOf_mul_le hna f g) (le_gaussNormOf_mul hna hf hg)

end General

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_eq_gaussNormOf (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) :
    gaussNorm v f = gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) f := rfl

theorem gaussNorm_mul (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f g : MvPolynomial ι K) : gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g :=
  gaussNormOf_mul (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v) f g

theorem gaussNorm_C (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K) :
    gaussNorm v (C c : MvPolynomial ι K) = NumberField.HeightOneSpectrum.adicAbv K v c :=
  gaussNormOf_C _ c

theorem gaussNorm_C_mul (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K)
    (f : MvPolynomial ι K) :
    gaussNorm v (C c * f) = NumberField.HeightOneSpectrum.adicAbv K v c * gaussNorm v f := by
  rw [gaussNorm_mul, gaussNorm_C]

theorem gaussNorm_nonneg (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) : 0 ≤ gaussNorm v f := gaussNormOf_nonneg _ f

theorem gaussNorm_pos (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    {f : MvPolynomial ι K} (hf : f ≠ 0) : 0 < gaussNorm v f := gaussNormOf_pos _ hf

theorem adicAbv_mulSupport_finite {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x).Finite := by
  have h := FinitePlace.hasFiniteMulSupport hx
  have e : (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x) =
      FinitePlace.equivHeightOneSpectrum.symm ⁻¹'
        (Function.mulSupport fun w : FinitePlace K => w x) := by
    ext v
    simp only [Function.mem_mulSupport, Set.mem_preimage,
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  rw [e]
  exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h

theorem log_gaussNorm_support_finite {ι : Type*} {f : MvPolynomial ι K} (hf : f ≠ 0) :
    (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v f)).Finite := by
  classical
  refine (Set.Finite.biUnion (s := (f.support : Set (ι →₀ ℕ))) f.support.finite_toSet
    fun m hm => adicAbv_mulSupport_finite (K := K) (mem_support_iff.mp hm)).subset ?_
  intro v hv
  rw [Function.mem_support] at hv
  by_contra hc
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hc
  apply hv
  have h1 : gaussNorm v f = 1 := by
    apply le_antisymm
    · refine gaussNormOf_le _ zero_le_one fun m => ?_
      by_cases hm : m ∈ f.support
      · exact (hc m hm).le
      · rw [notMem_support_iff.mp hm, map_zero]
        exact zero_le_one
    · obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq (NumberField.HeightOneSpectrum.adicAbv K v) hf
      rw [gaussNorm_eq_gaussNormOf, h, hc m hm]
  rw [h1, Real.log_one]

end NumberField

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionPerfect
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowFormSectionPerfect.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMinimalPrimeComap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def MinimalPrimeComap.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) (I : Ideal (MvPolynomial ι K)),
    I.IsPrime → ∀ P ∈ (I.map (MvPolynomial.map σ)).minimalPrimes,
      P.comap (MvPolynomial.map σ) = I

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def RadicalBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (ι : Type)
    (I : Ideal (MvPolynomial ι K)), I.IsRadical → (I.map (MvPolynomial.map σ)).IsRadical

def ChowFormExtend.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n k : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin k × Fin n) K),
    IsChowForm I k f → IsChowForm (I.map (MvPolynomial.map σ)) k (MvPolynomial.map σ f)

def ChowFormReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) F))
    (h : MvPolynomial (Fin k × Fin n) F),
    IsHomogIdeal J → J.IsRadical → IsChowForm J k h → IsChowFormCycle (fundCycle J) k h

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegAdjoinLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Algebra Cardinal Set AlgebraicIndependent

noncomputable section

section TrdegRank

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem matroid_subalgebra_eq_comap (S : Subalgebra K Ω) :
    AlgebraicIndependent.matroid K S = (AlgebraicIndependent.matroid K Ω).comap ((↑) : S → Ω) := by
  refine Matroid.ext_indep (by simp) fun I _ => ?_
  have hinj : InjOn ((↑) : S → Ω) I := Subtype.val_injective.injOn
  rw [Matroid.comap_indep_iff, matroid_indep_iff, matroid_indep_iff]
  simp only [hinj, and_true]
  change AlgebraicIndependent K (fun i : I => (i : S)) ↔
    AlgebraicIndependent K (fun x : (((↑) : S → Ω) '' I) => (x : Ω))
  rw [← algebraicIndependent_image hinj]
  exact (S.val.algebraicIndependent_iff Subtype.val_injective).symm

theorem trdeg_adjoin_eq_cRk (A : Set Ω) :
    Algebra.trdeg K (Algebra.adjoin K A) = (AlgebraicIndependent.matroid K Ω).cRk A := by
  rw [← matroid_cRank_eq, matroid_subalgebra_eq_comap, ← Matroid.cRk_ground, Matroid.comap_ground_eq,
    Matroid.cRk_comap, matroid_e, preimage_univ, image_univ, Subtype.range_coe]
  refine le_antisymm ?_ (Matroid.cRk_le_of_subset _ Algebra.subset_adjoin)
  refine (Matroid.cRk_le_of_subset _ ?_).trans_eq (Matroid.cRk_closure _ A)
  intro x hx
  rw [matroid_closure_eq]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin K A)

end TrdegRank

theorem TrdegAdjoinLe.proof : TrdegAdjoinLe.Statement := by
  intro K Ω _ _ _ s ι _ t ι' w hw
  set M := AlgebraicIndependent.matroid K Ω
  rw [trdeg_adjoin_eq_cRk, trdeg_adjoin_eq_cRk]
  have hcl : range w ⊆ M.closure (s ∪ range t) := by
    rintro _ ⟨i, rfl⟩
    rw [matroid_closure_eq]
    exact hw i
  calc M.cRk (range w) ≤ M.cRk (M.closure (s ∪ range t)) := M.cRk_le_of_subset hcl
    _ = M.cRk (s ∪ range t) := M.cRk_closure _
    _ ≤ M.cRk (s ∩ range t) + M.cRk (s ∪ range t) := le_add_self
    _ ≤ M.cRk s + M.cRk (range t) := M.cRk_inter_add_cRk_union_le s (range t)
    _ ≤ M.cRk s + #(range t) := by gcongr; exact M.cRk_le_cardinalMk _
    _ ≤ M.cRk s + #ι := by gcongr; exact mk_range_le
    _ = M.cRk s + Fintype.card ι := by rw [mk_fintype]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Swap

variable {F : Type*} [Field F] {n k : ℕ}

theorem comp_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)} {u : Fin k × Fin n → AlgebraicClosure F}
    (hu : u ∈ incidence I k) (τ : Equiv.Perm (Fin k)) : u ∘ Prod.map τ id ∈ incidence I k := by
  obtain ⟨x, hx, hI, hlin⟩ := hu
  exact ⟨x, hx, hI, fun i => by simpa using hlin (τ i)⟩

theorem IsChowForm.dvd_rename {I : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) : f ∣ rename (Prod.map τ id) f := by
  refine (hf.2 _).mp fun u hu => ?_
  rw [aeval_rename]
  exact (hf.2 f).mpr dvd_rfl _ (comp_mem_incidence hu τ)

theorem rename_prodMap_mul (σ τ : Equiv.Perm (Fin k)) (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map (σ * τ) id) p = rename (Prod.map σ id) (rename (Prod.map τ id) p) := by
  rw [rename_rename]
  rfl

theorem rename_prodMap_one (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map ⇑(1 : Equiv.Perm (Fin k)) id) p = p := by
  have : Prod.map ⇑(1 : Equiv.Perm (Fin k)) (id : Fin n → Fin n) = id := by
    funext ij
    rfl
  rw [this]
  exact rename_id_apply p

theorem IsChowForm.rename_eq_C_mul {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) :
    ∃ c : F, rename (Prod.map τ id) f = C c * f := by
  obtain ⟨a, ha⟩ := hf.dvd_rename τ
  obtain ⟨b, hb⟩ := hf.dvd_rename (τ⁻¹ : Equiv.Perm (Fin k))
  have hback : rename (Prod.map τ id) (rename (Prod.map ⇑(τ⁻¹ : Equiv.Perm (Fin k)) id) f) = f := by
    rw [← rename_prodMap_mul, mul_inv_cancel, rename_prodMap_one]
  have hab : a * rename (Prod.map τ id) b = 1 := by
    have h1 : f * (a * rename (Prod.map τ id) b) = f * 1 := by
      rw [mul_one, ← mul_assoc, ← ha]
      conv_rhs => rw [← hback, hb]
      rw [map_mul]
    exact mul_left_cancel₀ hf.1 h1
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (IsUnit.of_mul_eq_one _ hab)
  exact ⟨c, by rw [ha, mul_comm]⟩

theorem IsChowForm.rename_swap {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (x y : Fin k) :
    ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map (Equiv.swap x y) id) f = C c * f := by
  obtain ⟨c, hc⟩ := hf.rename_eq_C_mul (Equiv.swap x y)
  refine ⟨c, ?_, hc⟩
  have h2 : rename (Prod.map (Equiv.swap x y * Equiv.swap x y) id) f = C (c ^ 2) * f := by
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hc, ← mul_assoc, ← C_mul, sq]
  rw [Equiv.swap_mul_self, rename_prodMap_one] at h2
  have h3 : (C (c ^ 2) - 1) * f = 0 := by
    rw [sub_mul, ← h2, one_mul, sub_self]
  have h4 : C (c ^ 2) - 1 = (0 : MvPolynomial (Fin k × Fin n) F) :=
    (mul_eq_zero.mp h3).resolve_right hf.1
  rw [sub_eq_zero, ← C_1] at h4
  exact C_injective _ _ h4

theorem chowFormSwap : ChowFormSwap.Statement := by
  intro F _ n k I f hf τ
  induction τ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_pow 2, by rw [C_1, one_mul, rename_prodMap_one]⟩
  | swap_mul σ x y _ ih =>
    obtain ⟨c, hc2, hc⟩ := ih
    obtain ⟨d, hd2, hd⟩ := hf.rename_swap x y
    refine ⟨d * c, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hd, C_mul]
    ring

end Swap

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegBaseAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Cardinal

theorem TrdegBaseAlgebraic.proof : TrdegBaseAlgebraic.Statement := by
  intro F K Ω _ _ _ _ _ _ _ hKF ι z
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F Ω, A = Algebra.adjoin F (Set.range z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subalgebra K Ω, B = Algebra.adjoin K (Set.range z) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hAB : ∀ w ∈ A, w ∈ B := by
    intro w hw
    rw [hA] at hw
    rw [hB]
    induction hw using Algebra.adjoin_induction with
    | mem w hw => exact Algebra.subset_adjoin hw
    | algebraMap c =>
      rw [IsScalarTower.algebraMap_apply F K Ω c]
      exact Subalgebra.algebraMap_mem _ _
    | add u v _ _ hu hv => exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv => exact Subalgebra.mul_mem _ hu hv

  let i : A →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis F A
  let x : t → B := fun a => i a
  set C : Subalgebra K B := Algebra.adjoin K (Set.range x) with hC

  have hFC : ∀ r ∈ Algebra.adjoin F (Set.range ((↑) : t → A)), i r ∈ C := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
      obtain ⟨a, rfl⟩ := hr
      exact Algebra.subset_adjoin ⟨a, rfl⟩
    | algebraMap c =>
      have : i (algebraMap F A c) = algebraMap K B (algebraMap F K c) := by
        apply Subtype.ext
        exact (IsScalarTower.algebraMap_apply F K Ω c)
      rw [this]
      exact C.algebraMap_mem _
    | add r s _ _ hr hs =>
      rw [map_add (f := _)]
      exact C.add_mem hr hs
    | mul r s _ _ hr hs =>
      rw [map_mul]
      exact C.mul_mem hr hs
  let f : Algebra.adjoin F (Set.range ((↑) : t → A)) →+* C :=
    { toFun := fun r => ⟨i r, hFC r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => ((c : B) : Ω)) hab
  have key : ∀ (w : Ω), w ∈ Algebra.adjoin K (Set.range z) →
      ∀ (hw : w ∈ B), IsAlgebraic C (⟨w, hw⟩ : B) := by
    intro w hw'
    induction hw' using Algebra.adjoin_induction with
    | mem w hw' =>
      intro hw
      obtain ⟨m, rfl⟩ := hw'
      have hzA : z m ∈ A := hA ▸ Algebra.subset_adjoin ⟨m, rfl⟩
      have h1 : IsAlgebraic (Algebra.adjoin F (Set.range ((↑) : t → A))) (⟨z m, hzA⟩ : A) :=
        ht.isAlgebraic.isAlgebraic _
      exact h1.ringHom_of_comp_eq f i hf (RingHom.ext fun _ => rfl)
    | algebraMap k =>
      intro hw
      exact (hKF.isAlgebraic k).ringHom_of_comp_eq ((algebraMap K C).comp (algebraMap F K))
        (algebraMap K B) (RingHom.injective _) (RingHom.ext fun _ => rfl)
    | add u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).add (hv (hB ▸ hv'))
    | mul u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).mul (hv (hB ▸ hv'))
  have alg : Algebra.IsAlgebraic C B := ⟨fun b => key b.1 (hB ▸ b.2) b.2⟩
  calc Algebra.trdeg K B ≤ #(Set.range x) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range x)
    _ ≤ #t := Cardinal.mk_range_le
    _ = Algebra.trdeg F A := ht.cardinalMk_eq_trdeg

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFundCycleBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def FundCycleBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) K)),
      fundCycle (J.map (MvPolynomial.map σ)) =
        ∑ W ∈ (fundCycle J).support, fundCycle J W • fundCycle (W.map (MvPolynomial.map σ))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeClosedPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowDegreeClosedPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      chowDegree I 1 = Module.finrank F (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1}))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChowFormDimLe.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F),
    IsProjPrime I → IsChowForm I k f → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) ≤ k

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjDegreeChow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjDegreeChow.Statement : Prop :=
  ∀ (n e δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      ComplexSets.IsFiniteProjection W A → ComplexSets.projDegree W A = δ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjPrimeHasPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)), IsProjPrime W →
    ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ ∀ q ∈ W, aeval x q = 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionLengthSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights


open Classical in
def SectionLengthSum.Statement : Prop := by
  classical
  exact
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J W : Ideal A) (f : A),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    W ∈ (J ⊔ Ideal.span {f}).minimalPrimes →
    (∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) →
      GroundTheory.Heights₂.Heights.localMult (J ⊔ Ideal.span {f}) W =
        ∑ P ∈ (J.finite_minimalPrimes_of_isNoetherianRing A).toFinset with P ≤ W,
          GroundTheory.Heights₂.Heights.localMult (P ⊔ Ideal.span {f}) W

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaInjSet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaInjSet.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A →
        μH[(k : ℝ)] (f '' A) =
          ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
end
end
