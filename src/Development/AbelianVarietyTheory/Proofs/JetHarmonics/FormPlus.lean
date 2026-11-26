module

public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallPointMultiplicativeCoordinateExistsUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPoles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
noncomputable section

namespace GlobalTheory.ShortMove

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

def Marked {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (l : Level H)
    (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (mk : Dw.La → (Fin r → D.host.E)) (h : GA D V) : Prop :=
  (Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V h : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V h, finVec V (mk a ∘ Fin.cast hr) - (finHom V h).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
def FormPlus {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y)))

end GlobalTheory.ShortMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqConstMulArchPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqConstMulArchPairing
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNorm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCTx2

theorem beta_self_eq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) {A : ℝ} (hF : InCC A 4 F) :
    beta D F F = (((B.normSq D F).toReal : ℝ) : ℂ) := by
  have hc : ContinuousOn F (GV k r) := P.B7.jc_cont hF
  have hJ : AEStronglyMeasurable (fun q => JF D F (gq D q)) (volume.restrict (Qset D)) := by
    have h0 := P.B7.jc_aesm_J D hc (1, 1)
    have e : (fun q => Jtau D (1, 1) F (gq D q)) = fun q => JF D F (gq D q) :=
      funext fun q => P.bessel_function_trivial_index k r Wp Wq D F (gq D q)
    rwa [e] at h0
  set f : (Fin r → ℂ) × ℂ → ℝ := fun q =>
    bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖hsVec (JF D F (gq D q))‖ ^ 2 with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => mul_nonneg (bcWeight_nonneg' _ _ q) (sq_nonneg _)
  have hzero : ∀ q, q ∉ Qset D → f q = 0 := by
    intro q hq
    have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := P.BetaSesquilinearity.wt_eq_zero D hq
    simp [hf, hw]
  have hfm : AEStronglyMeasurable f volume := by
    have hind : Set.indicator (Qset D) f = f := by
      funext q
      by_cases hq : q ∈ Qset D
      · simp [hq]
      · simp [hq, hzero q hq]
    rw [← hind, aestronglyMeasurable_indicator_iff (P.BetaSesquilinearity.Qset_measurable D)]
    have hw : Measurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q) := P.BetaSesquilinearity.wt_measurable D
    exact hw.aestronglyMeasurable.mul ((P.BetaSesquilinearity.hsVec_cont.comp_aestronglyMeasurable hJ).norm.pow 2)
  have hinner : ∀ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) *
      inner ℂ (hsVec (JF D F (gq D q))) (hsVec (JF D F (gq D q))) = ((f q : ℝ) : ℂ) := by
    intro q
    rw [inner_self_eq_norm_sq_to_K]
    simp [hf]
  show (∫ p, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') p : ℝ) : ℂ) *
      inner ℂ (hsVec (JF D F (gq D p))) (hsVec (JF D F (gq D p)))) =
    (((∫⁻ p, ENNReal.ofReal (f p)).toReal : ℝ) : ℂ)
  simp only [hinner]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm]

end GlobalTheory.BesselNorm

namespace GlobalTheory.BesselNorm

theorem normSq_eq_betaInf_of_xi : B.XiExists → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F → B.normSq D F = ENNReal.ofReal (c * B.betaInf D F F).re := by
  intro hX k r Wp _ _ _ _ Wq _ _ _ _ D
  obtain ⟨c, hc0, -, hB1, hB2, -⟩ := (P.lemma_b_from_xi hX).2 k r Wp Wq D (B.AB k r) le_rfl
  refine ⟨(c : ℝ), by exact_mod_cast hc0, fun A F hA hF => ?_⟩
  have hF0 : B.InCC (B.AB k r) 5 F := P.BetaSesquilinearity.sInCC_mono hA le_rfl hF
  obtain ⟨c0, hc0F⟩ := id hF0
  obtain ⟨C, hC⟩ := hB1
  have h4 := P.BetaSesquilinearity.CCle_mono_m (show 4 ≤ 5 by norm_num) hc0F
  have hfin : B.normSq D F ≠ ⊤ := (hC F F c0 c0 hF0 hF0 h4 h4).1
  have hβ := hB2 F F hF0 hF0
  have h1 := beta_self_eq D F (P.BetaSesquilinearity.InCC_mono (show 4 ≤ 5 by norm_num) hF0)
  have hre : (B.normSq D F).toReal = (B.beta D F F).re := by
    rw [h1, Complex.ofReal_re]
  rw [← ENNReal.ofReal_toReal hfin, hre, hβ]

theorem normSq_eq_betaInf : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F → B.normSq D F = ENNReal.ofReal (c * B.betaInf D F F).re := normSq_eq_betaInf_of_xi P.exists_auxiliary_xi

end GlobalTheory.BesselNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqConstMulArchPairingStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselNormSq_eq_const_mul_archPairing : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F → B.normSq D F = ENNReal.ofReal (c * B.betaInf D F F).re := by
  first | exact @GlobalTheory.BesselNorm.normSq_eq_betaInf | exact GlobalTheory.BesselNorm.normSq_eq_betaInf | (intros; apply GlobalTheory.BesselNorm.normSq_eq_betaInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaFinsetSumSmulOfXiExists
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.BetaSum

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2 MeasureTheory Filter
open scoped ComplexConjugate

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable [FiniteDimensional ℂ Wp]

theorem _root_.GlobalTheory.BetaSum.beta_sesq (hXi : _root_.Formalism.FourierDecayAlt.B.XiExists) (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ}
    (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {F F' G : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)} (hF : _root_.Formalism.FourierDecayAlt.B.InCC A 5 F) (hF' : _root_.Formalism.FourierDecayAlt.B.InCC A 5 F')
    (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) (c : ℂ) :
    _root_.Formalism.FourierDecayAlt.B.beta D (F + c • F') G = _root_.Formalism.FourierDecayAlt.B.beta D F G + c * _root_.Formalism.FourierDecayAlt.B.beta D F' G ∧
      _root_.Formalism.FourierDecayAlt.B.beta D G (F + c • F') = _root_.Formalism.FourierDecayAlt.B.beta D G F + conj c * _root_.Formalism.FourierDecayAlt.B.beta D G F' :=
  _root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA hF hF' hG c

end GlobalTheory.BetaSum

namespace GlobalTheory

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
private lemma beta_eq_star_beta_swap (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (F G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) :
    _root_.Formalism.FourierDecayAlt.B.beta D F G = star (_root_.Formalism.FourierDecayAlt.B.beta D G F) := by
  unfold _root_.Formalism.FourierDecayAlt.B.beta _root_.Formalism.QuantumDeterminants.betaBig
  rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl, ← integral_conj]
  congr 1
  ext p
  simp [inner_conj_symm]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
private lemma beta_congr_right_on_GV (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {F G G₂ : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp}
    (h : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, G g = G₂ g) : _root_.Formalism.FourierDecayAlt.B.beta D F G = _root_.Formalism.FourierDecayAlt.B.beta D F G₂ := by
  rw [beta_eq_star_beta_swap D F G, beta_eq_star_beta_swap D F G₂, _root_.Formalism.FourierDecayAlt.P.Dx1.LZ.beta_congr_left D h]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
private lemma beta_sum_smul_left (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp)
    (hFi : ∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) :
    _root_.Formalism.FourierDecayAlt.B.beta D (fun g ↦ ∑ i ∈ s, c i • Fi i g) G = ∑ i ∈ s, c i * _root_.Formalism.FourierDecayAlt.B.beta D (Fi i) G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : _root_.Formalism.FourierDecayAlt.B.InCC A 5 (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) := _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_zero
    have h := (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA h0 h0 hG 1).1
    have e : ((fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) +
        (1 : ℂ) • (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp))) =
        (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) := by
      funext g; simp
    rw [e, one_mul] at h
    simp only [Finset.sum_empty]
    have : _root_.Formalism.FourierDecayAlt.B.beta D (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) G = 0 := by
      linear_combination -h
    exact this
  | insert x s hx ih =>
    have hs : _root_.Formalism.FourierDecayAlt.B.InCC A 5 (fun g ↦ ∑ i ∈ s, c i • Fi i g) :=
      _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum s (fun i g ↦ c i • Fi i g) (fun i _ ↦ _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_smul (c i) (hFi i))
    have e : (fun g ↦ ∑ i ∈ insert x s, c i • Fi i g) =
        (fun g ↦ ∑ i ∈ s, c i • Fi i g) + c x • Fi x := by
      funext g; simp [Finset.sum_insert hx, add_comm]
    rw [e, (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA hs (hFi x) hG (c x)).1, ih, Finset.sum_insert hx, add_comm]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
private lemma beta_sum_smul_right (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp)
    (hFi : ∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) :
    _root_.Formalism.FourierDecayAlt.B.beta D G (fun g ↦ ∑ i ∈ s, c i • Fi i g) = ∑ i ∈ s, star (c i) * _root_.Formalism.FourierDecayAlt.B.beta D G (Fi i) := by
  rw [beta_eq_star_beta_swap, beta_sum_smul_left D hA s c Fi hFi hG, star_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [star_mul', beta_eq_star_beta_swap D G (Fi i)]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
theorem _root_.GlobalTheory.beta_finset_sum_smul_of_bessel : _root_.GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (A : ℝ) (ι : Type) (S T : Finset ι) (a b : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (F F' : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → (∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) → (∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, F g = ∑ i ∈ S, a i • Fi i g) → (∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, F' g = ∑ i ∈ T, b i • Fi i g) → _root_.Formalism.FourierDecayAlt.B.beta D F F' = ∑ i ∈ S, ∑ j ∈ T, a i * star (b j) * _root_.Formalism.FourierDecayAlt.B.beta D (Fi i) (Fi j) := by
  intro _ k r Wp Wq _ _ _ _ _ _ D A ι S T a b Fi F F' hA hFi hF hF'
  rw [_root_.Formalism.FourierDecayAlt.P.Dx1.LZ.beta_congr_left D hF, beta_congr_right_on_GV D hF',
    beta_sum_smul_left D hA S a Fi hFi
      (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum T (fun i g ↦ b i • Fi i g) (fun i _ ↦ _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_smul (b i) (hFi i)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [beta_sum_smul_right D hA T b Fi hFi (hFi i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaIntegrandIntegrableOfXiExists
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

namespace GlobalTheory.BetaIntegrand

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end GlobalTheory.BetaIntegrand

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

private theorem exists_CCle_four_of_inCC_five {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ}
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) : ∃ c, _root_.Formalism.FourierDecayAlt.B.CCle A 4 G c := by
  unfold _root_.Formalism.FourierDecayAlt.B.InCC _root_.Formalism.FourierDecayAlt.B.CCle at hG
  obtain ⟨c, h1, h2⟩ := hG
  exact ⟨c, _root_.Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) h1, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩

private theorem measurableSet_Qset' (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : MeasurableSet (_root_.Formalism.FourierDecayAlt.B.Qset Bs) :=
  measurableSet_lt measurable_const (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)

private theorem aestronglyMeasurable_indicator_hsVec_JF (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      volume := by
  refine (aestronglyMeasurable_indicator_iff (measurableSet_Qset' Bs)).2 ?_
  have h := _root_.Formalism.FourierDecayAlt.P.B7.jc_aesm_J Bs hG (1, 1)
  simp only [_root_.Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs G] at h
  exact _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_cont'.comp_aestronglyMeasurable h

private theorem mem_Qset_iff_zero_lt_bcWeight (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) :
    q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs ↔ 0 < _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q := Iff.rfl

private theorem bcWeight_mul_eq_bcWeight_mul_indicator (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {β : Type} [Zero β] (Φ : β → ℝ)
    (hΦ : Φ 0 = 0) (u : (Fin r → ℂ) × ℂ → β) (q : (Fin r → ℂ) × ℂ) :
    _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q * Φ (u q) =
      _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q * Φ ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator u q) := by
  by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
  · rw [Set.indicator_of_mem hq]
  · have hw : _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q = 0 :=
      le_antisymm (not_lt.1 ((mem_Qset_iff_zero_lt_bcWeight Bs q).not.1 hq)) (_root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q)
    rw [hw, zero_mul, zero_mul]
end

theorem _root_.GlobalTheory.betaIntegrand_integrable_of_xiExists (hXi : _root_.Formalism.FourierDecayAlt.B.XiExists) : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (A : ℝ) (X F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → _root_.Formalism.FourierDecayAlt.B.InCC A 5 X → _root_.Formalism.FourierDecayAlt.B.InCC A 5 F → Integrable (fun q : (Fin r → ℂ) × ℂ => (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) * inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs A X F hA hX hF
  obtain ⟨-, -, -, ⟨C, hC⟩, -⟩ := _root_.Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq Bs A hA
  obtain ⟨cF, hcF⟩ := exists_CCle_four_of_inCC_five hF
  obtain ⟨cX, hcX⟩ := exists_CCle_four_of_inCC_five hX
  obtain ⟨hFF, hFX, -⟩ := hC F X cF cX hF hX hcF hcX
  unfold _root_.Formalism.FourierDecayAlt.B.normSq _root_.Formalism.QuantumDeterminants.jNormSq at hFF hFX
  set w := fun q => _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q with hw
  set uF := (_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q)) with huF
  set uX := (_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)) with huX
  have hmF : AEStronglyMeasurable uF volume :=
    aestronglyMeasurable_indicator_hsVec_JF Bs (_root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cF, hcF⟩))
  have hmX : AEStronglyMeasurable uX volume :=
    aestronglyMeasurable_indicator_hsVec_JF Bs (_root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cX, hcX⟩))
  have hw0 : ∀ q, 0 ≤ w q := fun q => _root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q
  have hfun : (fun q : (Fin r → ℂ) × ℂ => (w q : ℂ) * inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) = fun q => (w q : ℂ) * inner ℂ (uF q) (uX q) := by
    funext q
    by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
    · rw [huF, huX, Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    · have hwq : w q = 0 :=
        le_antisymm (not_lt.1 ((mem_Qset_iff_zero_lt_bcWeight Bs q).not.1 hq)) (hw0 q)
      rw [hwq, Complex.ofReal_zero, zero_mul, zero_mul]
  have hFF' : ∫⁻ q, ENNReal.ofReal (w q * ‖uF q‖ ^ 2) ≠ ⊤ := by
    refine ne_of_eq_of_ne (lintegral_congr fun q => ?_) hFF
    exact congrArg ENNReal.ofReal (bcWeight_mul_eq_bcWeight_mul_indicator Bs (fun x => ‖x‖ ^ 2) (by simp) _ q).symm
  have hFX' : ∫⁻ q, ENNReal.ofReal (w q * ‖uX q‖ ^ 2) ≠ ⊤ := by
    refine ne_of_eq_of_ne (lintegral_congr fun q => ?_) hFX
    exact congrArg ENNReal.ofReal (bcWeight_mul_eq_bcWeight_mul_indicator Bs (fun x => ‖x‖ ^ 2) (by simp) _ q).symm
  have hbound : ∀ q, ‖(w q : ℂ) * inner ℂ (uF q) (uX q)‖ₑ ≤
      ENNReal.ofReal (w q * ‖uF q‖ ^ 2) + ENNReal.ofReal (w q * ‖uX q‖ ^ 2) := by
    intro q
    rw [← ENNReal.ofReal_add (mul_nonneg (hw0 q) (sq_nonneg _)) (mul_nonneg (hw0 q) (sq_nonneg _)),
      ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 q)]
    have h1 := norm_inner_le_norm (𝕜 := ℂ) (uF q) (uX q)
    have h2 : ‖uF q‖ * ‖uX q‖ ≤ ‖uF q‖ ^ 2 + ‖uX q‖ ^ 2 := by
      nlinarith [sq_nonneg (‖uF q‖ - ‖uX q‖), norm_nonneg (uF q), norm_nonneg (uX q)]
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (hw0 q)]
  have haeF : AEMeasurable (fun q => ENNReal.ofReal (w q * ‖uF q‖ ^ 2)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aemeasurable.mul (hmF.norm.aemeasurable.pow_const 2))
  rw [hfun]
  refine ⟨(Complex.continuous_ofReal.measurable.comp (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable.mul
    (hmF.inner hmX), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ q, ‖(w q : ℂ) * inner ℂ (uF q) (uX q)‖ₑ
      ≤ ∫⁻ q, (ENNReal.ofReal (w q * ‖uF q‖ ^ 2) + ENNReal.ofReal (w q * ‖uX q‖ ^ 2)) :=
        lintegral_mono hbound
    _ = (∫⁻ q, ENNReal.ofReal (w q * ‖uF q‖ ^ 2)) + ∫⁻ q, ENNReal.ofReal (w q * ‖uX q‖ ^ 2) :=
        lintegral_add_left' haeF _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hFF', lt_top_iff_ne_top.2 hFX'⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliWordProductDecayBoundUniform
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliWordProductDecayBoundUniform
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.CapelliFoldBound

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

variable {k r : ℕ} (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable {Wp Wq}

end GlobalTheory.CapelliFoldBound

namespace GlobalTheory

private theorem ckOn_sum_smul_Rw {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (L : List (ℂ × List (_root_.Formalism.FourierDecayAlt.B.Mat k r))) (hL : ∀ cw ∈ L, ∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X)
    {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)} (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) :
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g => (L.map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum) := by
  induction L with
  | nil => exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_zero'
  | cons cw L ih =>
    have hw : ∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.inLie k r X := by
      intro X hX
      have := hL cw (List.mem_cons_self ..) X hX
      unfold _root_.Formalism.FourierDecayAlt.B.unitLie at this
      unfold _root_.Formalism.FourierDecayAlt.B.inLie
      exact this.1
    exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_add' (_root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' cw.1 (_root_.Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hF cw.2 hw)) (ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h))

private theorem capelli_eq_foldT_signed_sum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (y : ℂ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.Q.CV k r y F g = ∑ σ : Equiv.Perm (Fin (2 * (r - 0) + k + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
        (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j)) F g := by
  unfold _root_.Formalism.FourierDecayAlt.Q.CV _root_.Formalism.FourierDecayAlt.Q.capL _root_.Formalism.QuantumDeterminants.qminorOp _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT
  simp only [Finset.sum_apply, List.map_ofFn, Pi.smul_apply, Function.comp_def]
  rfl

private theorem capelli_eq_wordSum_lemma_3 {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (y : ℂ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E) (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) :
    ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r y F g =
      ∑ σ : Equiv.Perm (Fin (2 * (r - 0) + k + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
          (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j))).map
            fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum := by
  intro g hg
  rw [capelli_eq_foldT_signed_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hloc : _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (⊤ : ℕ∞) F g := by
    unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hF
    exact hF g hg
  rw [_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq _ F g hg (_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top hloc)]

private theorem CCle_sum_smul_Rw {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N : ℕ) (L : List (ℂ × List (_root_.Formalism.FourierDecayAlt.B.Mat k r)))
    (hL : ∀ cw ∈ L, (∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ N) {A : ℝ} {m : ℕ}
    {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} {c : ℝ} (hF : _root_.Formalism.FourierDecayAlt.B.CCle A (m + N) F c) :
    _root_.Formalism.FourierDecayAlt.B.CCle A m (fun g => (L.map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      ((L.map fun cw => ‖cw.1‖).sum * c) := by
  induction L with
  | nil => simpa using (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (k := k) (r := r) (E := E) (A := A) (m := m))
  | cons cw L ih =>
    have hcw := hL cw (List.mem_cons_self ..)
    have h1 : _root_.Formalism.FourierDecayAlt.B.CCle A m (_root_.Formalism.FourierDecayAlt.B.Rw cw.2 F) c :=
      _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw hcw.1 (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by omega) hF)
    have h2 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul cw.1 h1) (ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact h2

private theorem norm_sign_perm_complex_eq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private theorem capelli_smooth_and_bound_lemma {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (y : ℂ) :
    (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (_root_.Formalism.FourierDecayAlt.Q.CV k r y F)) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (m : ℕ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ),
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → _root_.Formalism.FourierDecayAlt.B.CCle A (m + (2 * r + k + 1)) F c →
        _root_.Formalism.FourierDecayAlt.B.CCle A m (_root_.Formalism.FourierDecayAlt.Q.CV k r y F) (K * c) := by
  set ts : Equiv.Perm (Fin (2 * (r - 0) + k + 1)) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
      (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j) with hts
  have hwords : ∀ σ, ∀ cw ∈ _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ),
      (∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1 := by
    intro σ cw hcw
    obtain ⟨h1, h2⟩ := _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (ts σ) cw hcw
    refine ⟨h1, h2.trans ?_⟩
    simp [hts]
  refine ⟨fun F hF => ?_, ?_⟩
  · have hG := _root_.Formalism.FourierDecayAlt.P.JCx2.sq_ckOn_sum (Finset.univ : Finset (Equiv.Perm (Fin (2 * (r - 0) + k + 1))))
      (fun σ g => ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      (fun σ _ => _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ (ckOn_sum_smul_Rw _ (fun cw h => (hwords σ cw h).1) hF))
    have heq := capelli_eq_wordSum_lemma_3 y F hF
    unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hG ⊢
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hagree⟩ := hG g₀ hg₀
    exact ⟨U, f', hU, hgU, hf', fun x hx hxG => (heq x hxG).trans (hagree x hx hxG)⟩
  · refine ⟨∑ σ, ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => ‖cw.1‖).sum,
      Finset.sum_nonneg fun σ _ => List.sum_nonneg fun a ha => by
        obtain ⟨cw, -, rfl⟩ := List.mem_map.1 ha
        exact norm_nonneg _, ?_⟩
    intro A m F c hF hc
    have hc0 : 0 ≤ c := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
    have hsum := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_sum (Finset.univ : Finset (Equiv.Perm (Fin (2 * (r - 0) + k + 1))))
      (fun σ g => ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      (fun σ => ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ * (((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => ‖cw.1‖).sum * c))
      (fun σ _ => _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul _ (CCle_sum_smul_Rw _ _ (hwords σ) hc))
    simp only [norm_sign_perm_complex_eq_one, one_mul] at hsum
    rw [Finset.sum_mul]
    exact _root_.Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => (capelli_eq_wordSum_lemma_3 y F hF g hg).symm) hsum

theorem _root_.GlobalTheory.capelli_fold_ccle : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s : ℂ) (w : List (Bool × ℝ)) (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (A c : ℝ) (X : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) X → _root_.Formalism.FourierDecayAlt.B.CCle A (m + w.length * (2 * r + k + 1)) X c → _root_.Formalism.FourierDecayAlt.B.CCle A m (List.foldr (fun (a : Bool × ℝ) G => s • _root_.Formalism.FourierDecayAlt.Q.CV k r (a.2 : ℂ) G) (X) w) (K * c) := by
  intro k r Wp Wq _ _ _ _ _ _ s w
  have hsmooth : ∀ (w : List (Bool × ℝ)) (X : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) X →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (List.foldr (fun (a : Bool × ℝ) G => s • _root_.Formalism.FourierDecayAlt.Q.CV k r (a.2 : ℂ) G) X w) := by
    intro w X hX
    induction w with
    | nil => exact hX
    | cons a w ih => exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' s ((capelli_smooth_and_bound_lemma (a.2 : ℂ)).1 _ ih)
  induction w with
  | nil => exact fun m => ⟨1, zero_le_one, fun A c X _ hX => by simpa using hX⟩
  | cons a w ih =>
    intro m
    obtain ⟨K, hK, hbound⟩ := ih (m + (2 * r + k + 1))
    obtain ⟨Ky, hKy, hy⟩ := (capelli_smooth_and_bound_lemma (Wp := Wp) (Wq := Wq) (a.2 : ℂ)).2
    refine ⟨‖s‖ * (Ky * K), by positivity, fun A c X hX hXc => ?_⟩
    have h1 := hbound A c X hX (by
      have : m + (2 * r + k + 1) + w.length * (2 * r + k + 1) = m + (a :: w).length * (2 * r + k + 1) := by
        simp only [List.length_cons]; ring
      rw [this]; exact hXc)
    have h2 := hy A m _ (K * c) (hsmooth w X hX) h1
    have h3 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul s h2
    simp only [List.foldr_cons]
    rw [show ‖s‖ * (Ky * K) * c = ‖s‖ * (Ky * (K * c)) by ring]
    exact h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliWordProductDecayBoundUniformStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliWordProduct_decayBound_uniform : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s : ℂ) (w : List (Bool × ℝ)) (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (A c : ℝ) (X : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CCle A (m + w.length * (2 * r + k + 1)) X c → B.CCle A m (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (K * c) := by
  first | exact @GlobalTheory.capelli_fold_ccle | exact GlobalTheory.capelli_fold_ccle | (intros; apply GlobalTheory.capelli_fold_ccle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeCoordAddAndComplexMul
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeCoordAddAndComplexMul
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.AtAdd

variable {q : ℕ} [Fact q.Prime]

open Classical in
theorem sub_mem_of_uw (M : Mdl q) (hM : M.Ok) (s t : ℂ) (ht : t ∉ M.L.lattice) (hy : M.y t ≠ 0)
    (hu : M.u s = M.u t) (hw : M.w s = M.w t) : s - t ∈ M.L.lattice := by
  have hwt : M.w t = -1 / M.y t := by simp [Mdl.w, ht]
  have hwt0 : M.w t ≠ 0 := by rw [hwt]; exact div_ne_zero (by norm_num) hy
  have hs : s ∉ M.L.lattice := by
    intro hs
    apply hwt0
    rw [← hw]; simp [Mdl.w, hs]
  have hws : M.w s = -1 / M.y s := by simp [Mdl.w, hs]
  have hys : M.y s ≠ 0 := by
    intro h
    apply hwt0
    rw [← hw, hws, h, div_zero]
  have hyy : M.y s = M.y t := by
    rw [hws, hwt, div_eq_div_iff hys hy] at hw
    linear_combination hw
  have hxx : M.x s = M.x t := by
    have h1 : M.u s = -M.x s / M.y s := by simp [Mdl.u, hs]
    have h2 : M.u t = -M.x t / M.y t := by simp [Mdl.u, ht]
    rw [h1, h2, hyy, div_left_inj' hy] at hu
    exact neg_injective hu
  obtain ⟨φ, -, hk, hφ⟩ := Mdl.exists_pointHom q M hM
  obtain ⟨h1, e1⟩ := hφ s hs
  obtain ⟨h2, e2⟩ := hφ t ht
  rw [← hk, map_sub, e1, e2, sub_eq_zero]
  congr 1 <;> simp [hxx, hyy]

theorem sub_mem_of_germ (M : Mdl q) (hM : M.Ok) (α s t : ℂ) (hα : α ≠ 0) (ht : M.Small t)
    (hu : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u (α * z + s) = M.u (α * z + t))
    (hw : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.w (α * z + s) = M.w (α * z + t)) : s - t ∈ M.L.lattice := by
  have hg := ((uw_elliptic_flow q M hM).2.2.2.2.2.2.2.2 t ht).2.2.2.2.1
  have htend : Filter.Tendsto (fun z : ℂ => α * z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous (fun z : ℂ => α * z + t) := by fun_prop
      simpa using hc.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa [hα] using hz
  obtain ⟨z, h1, h2, h3⟩ := ((htend.eventually hg).and (hu.and hw)).exists
  have := sub_mem_of_uw M hM _ _ h1.1 h1.2.1 h2 h3
  simpa using this

theorem const_ell (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  simp [logS, ← coeff_zero_eq_constantCoeff_apply]

theorem bd_w (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (h : M.Chart ℓ) : Bd 1 (hat M.ι ℓ M.w) := by
  obtain ⟨-, v, xs, ys, -, -, hys, -, -, hc, -, hw, -⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M ℓ h
  apply (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 hys hc
  rw [pow_zero, one_mul, mul_comm, hw]
  intro n
  rw [map_neg, norm_neg, coeff_X_pow]
  split_ifs <;> simp

theorem germ_add (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (ζ ζ' : ℂ_[q]) (p p' t : ℂ) (h : M.At ω ζ p) (h' : M.At ω ζ' p') (ht : M.At ω (ζ * ζ') t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (1 * z + (p + p')) = F (1 * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hEp : Ell M.L (fun z => F (z + p)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (x + p)).comp_analyticAt (f := F) (g := fun z => z + p) (by fun_prop)
    · show F (z + l + p) = F (z + p)
      rw [add_right_comm, hE.2 l hl]
  have hBp : Bdd (hat M.ι (C ω * logS) (fun z => F (z + p))) := by
    rw [hT ζ p h]
    exact ⟨1, (Shift.shift_laws q ζ h.2.1).1 _ _ hB⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ' p' _ hM h' hEp (han p h.1) hBp
  rw [hT ζ p h, (GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).1 ζ' ζ _ h'.2.1 h.2.1 ⟨1, hB⟩, mul_comm ζ' ζ, ← hT _ t ht] at hψ
  have h1 := (GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa (han t ht.1)).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [one_mul, ← e2, e1]
  congr 1; ring

theorem germ_mul (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p t : ℂ)
    (hL : ∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) (hα : M.ι α = zc a)
    (hk : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hζ : ζ ^ (q ^ n) = 1)
    (h : M.At ω ζ p) (ht : M.At ω (ζ ^ k) t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (α * z + α * p) = F (α * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hF0 : AnalyticAt ℂ F 0 := hA 0 (Or.inl (zero_mem _))
  have hmul : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → AnalyticAt ℂ (fun z => G (α * z)) 0 := fun G hG =>
    AnalyticAt.comp_of_eq (g := G) (f := fun z => α * z) hG (by fun_prop) (by simp)
  have hEα : Ell M.L (fun z => F (α * z)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (α * x)).comp_analyticAt (f := F) (g := fun z => α * z) (by fun_prop)
    · show F (α * (z + l)) = F (α * z)
      rw [mul_add, hE.2 _ (hL l hl)]
  have hsub := (GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart q M.ι ω F hF0).2.2.1 α a hα
  have hm := (MulSeries.mulS_laws q).1 a
  have hBα : Bdd (hat M.ι (C ω * logS) (fun z => F (α * z))) := by
    rw [hsub]
    exact ⟨1, (sup_norm_laws q).2.1 _ _ _ hB hm.1 hm.2.1⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ p _ hM h hEα (hmul F hF0) hBα
  rw [hsub, ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ζ n k a _ hζ hk ⟨1, hB⟩).2, ← hT _ t ht,
    ← (GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart q M.ι ω _ (han t ht.1)).2.2.1 α a hα] at hψ
  have h1 := (GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa
    (hmul _ (han t ht.1))).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [← mul_add, ← e1, e2]

theorem norm_mul_sub_one_lt {ζ ξ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (h' : ‖ξ - 1‖ < 1) : ‖ζ * ξ - 1‖ < 1 := by
  have e : ζ * ξ - 1 = (ζ - 1) * (ξ - 1) + ((ζ - 1) + (ξ - 1)) := by ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h h'.le
  · exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h h')

theorem norm_pow_sub_one_lt {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (k : ℕ) : ‖ζ ^ k - 1‖ < 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih h

theorem at_add_and_mul : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ ζ' p p', M.At ω ζ p → M.At ω ζ' p' → M.At ω (ζ * ζ') (p + p')) ∧ ∀ (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p : ℂ), (∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) → M.ι α = zc a → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ζ ^ (q ^ n) = 1 → M.At ω ζ p → M.At ω (ζ ^ k) (α * p) := by
  intro q _ M ω hM
  have hOk : M.Ok := hM.1
  obtain ⟨hex, -, -, hiff, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω hM
  obtain ⟨hEu, hEw, -, -, -, -, -, -, hS⟩ := uw_elliptic_flow q M hOk
  have hBu : Bd 1 (hat M.ι (C ω * logS) M.u) := hM.2.2.1
  have hBw := bd_w M _ hM
  have hTu := fun ζ p h => (GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hM h).1
  have hTw := fun ζ p h => (GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hM h).2
  refine ⟨fun ζ ζ' p p' h h' => ?_, fun α a n k ζ p hL hα hk hζ h => ?_⟩
  · obtain ⟨t, ht⟩ := hex _ (norm_mul_sub_one_lt h.2.1 h'.2.1)
    have := sub_mem_of_germ M hOk 1 (p + p') t one_ne_zero ht.1
      (germ_add M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu ζ ζ' p p' t h h' ht)
      (germ_add M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw ζ ζ' p p' t h h' ht)
    refine (hiff _ t _ ht).2 ?_
    simpa using neg_mem this
  · by_cases h0 : α = 0
    · subst h0
      have ha : a = 0 := by
        have := (MulSeries.mulS_laws q).2.2.2.2.2 a
        rw [← hα, map_zero, norm_zero] at this
        exact norm_eq_zero.1 this.symm
      subst ha
      rw [zero_sub, norm_neg] at hk
      have hd : ((q : ℤ) ^ n) ∣ (k : ℤ) := by
        rw [← PadicInt.norm_int_le_pow_iff_dvd]
        simpa using hk
      have hd' : q ^ n ∣ k := by exact_mod_cast hd
      obtain ⟨m, rfl⟩ := hd'
      rw [pow_mul, hζ, one_pow, zero_mul]
      exact h10
    · obtain ⟨t, ht⟩ := hex _ (norm_pow_sub_one_lt h.2.1 k)
      have := sub_mem_of_germ M hOk α (α * p) t h0 ht.1
        (germ_mul M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu α a n k ζ p t hL hα hk hζ h ht)
        (germ_mul M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw α a n k ζ p t hL hα hk hζ h ht)
      refine (hiff _ t _ ht).2 ?_
      simpa using neg_mem this

end GlobalTheory.MomOne.AtAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeCoordAddAndComplexMulStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeCoord_add_and_complexMul : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ ζ' p p', M.At ω ζ p → M.At ω ζ' p' → M.At ω (ζ * ζ') (p + p')) ∧ ∀ (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p : ℂ), (∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) → M.ι α = zc a → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ζ ^ (q ^ n) = 1 → M.At ω ζ p → M.At ω (ζ ^ k) (α * p) := by
  first | exact @GlobalTheory.MomOne.AtAdd.at_add_and_mul | exact GlobalTheory.MomOne.AtAdd.at_add_and_mul | (intros; apply GlobalTheory.MomOne.AtAdd.at_add_and_mul <;> assumption)
end
end
