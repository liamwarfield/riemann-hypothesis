module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PKerSwap
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.AevalConj
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PArchGroup
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PArchZero
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ContinuousClassKernel
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.SiegelSetUnitaryHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelImpliesRegularClassFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTraceFromLocalInputs

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PCuspAny
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing GlobalTheory.Proof.parabolic_and_constant_term
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem MainStatements.WeightKernel.cuspAny : MainStatements.WeightKernel.CuspAny := by
  intro D V hodd T U hNoFixed μf hμf ff hff fa hA 𝔉 hP
  have := hμf
  have hH := (GlobalTheory.T.typeHypothesis_forms_agree D V T hNoFixed).1
  obtain ⟨a, ha0, ha2, hpar⟩ := parabolicAtSplitPlaces D V hodd T 𝔉 hP
  obtain ⟨v, hv⟩ := hH a ha0 (by omega)
  obtain ⟨h, hh, e⟩ := hff.2.1 v
  have hF := hff.isFinFamily
  have he := (T.frame v).idem_mem (μf v.1) (T.τ v)
  refine GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local D V 𝔉 fa ff hA hF v.1 fun ν _ x y => ?_
  exact (GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB he hh) (ff v.1) (Or.inr e)
    ν x y).2

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PArchUnimod
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel

theorem archUnimod : ArchUnimod := by
  intro D V w μ hμ
  obtain ⟨hcm, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJ' V
  haveI : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (σ := D.sp.cm.sig) w.Completion hcm hJ).1
  exact hU.2.2.2.2.2.2 μ hμ

end MainStatements.WeightKernel

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PFdRight
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PFdRight

end MainStatements.WeightKernel.PFdRight

theorem MainStatements.WeightKernel.fdRight : MainStatements.WeightKernel.FDRight := by
  intro G _ _ _ _ _ _ Γ _ μ _ _ 𝓕 h𝓕 F hF g
  have h2 : IsFundamentalDomain Γ ((fun x : G => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have key : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in (fun x : G => x * g⁻¹) ⁻¹' 𝓕, F x ∂μ := by
    rw [← Set.image_mul_right,
      (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) F 𝓕]
  rw [key]
  exact h2.setIntegral_eq h𝓕 (fun γ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hF γ γ.2 x)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PBumpOn
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem bumpOn : BumpOn := by
  intro H _ _ _ _ _ _ _ _ n ι hemb C hC
  have hK : IsCompact (matCoord ι '' C) := hC.image hemb.continuous
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  let f : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max r 1, max r 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  refine ⟨fun g => ((f (matCoord ι g) : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · refine HasCompactSupport.intro (hemb.isCompact_preimage (isCompact_closedBall (0 : Fin n → Fin n → ℂ) (max r 1 + 1))) ?_
    intro g hg
    simp only [Set.mem_preimage, Metric.mem_closedBall, not_le] at hg
    have : f (matCoord ι g) = 0 := f.zero_of_le_dist hg.le
    simp [this]
  · refine ⟨fun x => ((f x : ℝ) : ℂ), ?_, fun g => rfl⟩
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · intro y hy
    have hm : matCoord ι y ∈ Metric.closedBall (0 : Fin n → Fin n → ℂ) (max r 1) :=
      Metric.closedBall_subset_closedBall (le_max_left _ _) (hr ⟨y, hy, rfl⟩)
    have : f (matCoord ι y) = 1 := f.one_of_mem_closedBall hm
    simp [this]

end MainStatements.WeightKernel

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PWeightDiag
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate Pointwise

noncomputable section

namespace MainStatements.WeightKernel.PWeightDiag

def N {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, Complex.normSq (M a b)

def bump : ContDiffBump (1 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩

def θ : ℝ → ℝ := fun x => bump x

theorem θ_smooth : ContDiff ℝ ∞ θ := bump.contDiff
theorem θ_nonneg (x : ℝ) : 0 ≤ θ x := bump.nonneg
theorem θ_one : θ 1 = 1 := bump.one_of_mem_closedBall (by simp [bump])
theorem θ_supp {x : ℝ} (h : θ x ≠ 0) : 1/2 ≤ x ∧ x ≤ 3/2 := by
  have hs : x ∈ Function.support (bump : ℝ → ℝ) := Function.mem_support.mpr h
  rw [ContDiffBump.support_eq] at hs
  simp only [bump, Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  constructor <;> linarith [hs.1, hs.2]

def Bw {n : ℕ} (l : Fin n → ℂ) (e : Fin n → MainStatements.WeightKernel.Mx n → MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n × MainStatements.WeightKernel.Mx n → ℝ :=
  fun p => ∏ i ∈ Finset.univ.filter (fun i => 1 < ‖l i‖), θ (N (Matrix.of (e i p.1) * Matrix.of p.2))

theorem N_smul {n : ℕ} (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : N (c • M) = ‖c‖ ^ 2 * N M := by
  simp only [N, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum, Complex.normSq_eq_norm_sq, norm_mul, mul_pow]

theorem N_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M ≠ 0) : 0 < N M := by
  obtain ⟨a, b, hab⟩ : ∃ a b, M a b ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM (Matrix.ext hc)
  have h1 : 0 < Complex.normSq (M a b) := Complex.normSq_pos.mpr hab
  have h2 : Complex.normSq (M a b) ≤ ∑ b', Complex.normSq (M a b') :=
    Finset.single_le_sum (f := fun b' => Complex.normSq (M a b')) (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
  have h3 : ∑ b', Complex.normSq (M a b') ≤ N M :=
    Finset.single_le_sum (f := fun a' => ∑ b', Complex.normSq (M a' b'))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)) (Finset.mem_univ a)
  linarith

theorem single_mul_diag {n : ℕ} (i : Fin n) (τ : Fin n → ℂ) :
    single i i (1 : ℂ) * diagonal τ = τ i • single i i 1 := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hb : b = i
  · subst hb
    rw [mul_comm]
  · have hb' : i ≠ b := fun h' => hb h'.symm
    simp [Matrix.single_apply, hb']

theorem comm_diag {n : ℕ} (l : Fin n → ℂ) (hl : Function.Injective l) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : M * diagonal l = diagonal l * M) : M = diagonal fun a => M a a := by
  ext a b
  have hab := congrFun (congrFun h a) b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hab
  by_cases e : a = b
  · subst e
    simp
  · rw [Matrix.diagonal_apply_ne _ e]
    have hne : l a ≠ l b := fun h' => e (hl h')
    have hz : M a b * (l b - l a) = 0 := by linear_combination hab
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0).symm hne

end MainStatements.WeightKernel.PWeightDiag

private theorem weightDiag_lemma {n : ℕ} (i : Fin n) : MainStatements.WeightKernel.PWeightDiag.N (single i i (1 : ℂ)) = 1 := by
  simp only [MainStatements.WeightKernel.PWeightDiag.N, Matrix.single_apply, ite_and]
  simp [apply_ite Complex.normSq]

private theorem weightDiag_lemma_2 {n : ℕ} (i : Fin n) (τ : Fin n → ℂ) :
    diagonal τ * single i i (1 : ℂ) = τ i • single i i 1 := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases ha : a = i
  · subst ha
    rfl
  · have ha' : i ≠ a := fun h' => ha h'.symm
    simp [Matrix.single_apply, ha']

private theorem weightDiag_lemma_3 {n : ℕ} :
    Continuous (MainStatements.WeightKernel.PWeightDiag.N : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold MainStatements.WeightKernel.PWeightDiag.N
  exact continuous_finsetSum _ (fun a _ => continuous_finsetSum _
    (fun b _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem a b)))

private theorem weightDiag_lemma_4 {n : ℕ} (f : MainStatements.WeightKernel.Mx n → MainStatements.WeightKernel.Mx n) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : MainStatements.WeightKernel.Mx n × MainStatements.WeightKernel.Mx n =>
      MainStatements.WeightKernel.PWeightDiag.N (Matrix.of (f p.1) * Matrix.of p.2)) := by
  have hent : ∀ a b, ContDiff ℝ ∞
      (fun p : MainStatements.WeightKernel.Mx n × MainStatements.WeightKernel.Mx n => (Matrix.of (f p.1) * Matrix.of p.2) a b) := by
    intro a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact ContDiff.sum (fun c _ => (contDiff_pi.mp (contDiff_pi.mp (hf.comp contDiff_fst) a) c).mul
      (contDiff_pi.mp (contDiff_pi.mp contDiff_snd c) b))
  unfold MainStatements.WeightKernel.PWeightDiag.N
  simp only [Complex.normSq_eq_norm_sq]
  exact ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => (contDiff_norm_sq ℝ).comp (hent a b)))

open MainStatements.WeightKernel.PWeightDiag in
theorem MainStatements.WeightKernel.weightDiag : Lagr → ShiftT → BoundT → WeightDiag := by
  intro hLagr hShift hBound H _ _ _ _ _ _ _ _ n ι J hU s l hl hs hprop
  obtain ⟨hdet, hce, hrange⟩ := hU
  obtain ⟨e, he, hel⟩ := hLagr n l hl
  have hinj : Function.Injective ι := by
    intro x y hxy
    apply hce.injective
    show (fun a b => ι x a b) = fun a b => ι y a b
    rw [hxy]
  have hJl : (diagonal l)ᴴ * J * diagonal l = J := (hrange _).mp ⟨s, hs⟩
  have hinv : ∀ x : H, ι x⁻¹ * ι x = 1 ∧ ι x * ι x⁻¹ = 1 := fun x =>
    ⟨by rw [← map_mul, inv_mul_cancel, map_one], by rw [← map_mul, mul_inv_cancel, map_one]⟩
  have hdiag : ∀ w ∈ cent s, ι w = diagonal (fun a => ι w a a) := by
    intro w hw
    apply comm_diag l hl
    have hc : s * w = w * s := (Subgroup.mem_centralizer_iff.mp hw) s (Set.mem_singleton s)
    rw [← hs, ← map_mul, ← map_mul, hc]
  have hleft : ∀ w ∈ cent s, ∀ i, single i i (1 : ℂ) * ι w = ι w i i • single i i 1 := by
    intro w hw i
    calc single i i (1 : ℂ) * ι w = single i i 1 * diagonal (fun a => ι w a a) := congrArg _ (hdiag w hw)
      _ = ι w i i • single i i 1 := single_mul_diag i _
  have hright : ∀ w ∈ cent s, ∀ i, ι w * single i i (1 : ℂ) = ι w i i • single i i 1 := by
    intro w hw i
    calc ι w * single i i (1 : ℂ) = diagonal (fun a => ι w a a) * single i i 1 :=
          congrArg (· * single i i (1 : ℂ)) (hdiag w hw)
      _ = ι w i i • single i i 1 := weightDiag_lemma_2 i _
  have hcomm : ∀ w ∈ cent s, ∀ i, ι w * single i i (1 : ℂ) = single i i 1 * ι w := by
    intro w hw i
    rw [hleft w hw i, hright w hw i]
  have hF : ∀ (x y : H) (i : Fin n), N (Matrix.of (e i (matCoord ι (x⁻¹ * s * x))) * Matrix.of (matCoord ι y))
      = N (ι x⁻¹ * single i i 1 * ι x * ι y) := by
    intro x y i
    have h1 := hel i (ι x) (ι x⁻¹) (hinv x).1 (hinv x).2
    have h2 : matCoord ι (x⁻¹ * s * x) = fun a b => (ι x⁻¹ * diagonal l * ι x) a b := by
      funext a b
      simp only [matCoord, map_mul, hs]
    rw [h2, h1]
    rfl
  have Fpos : ∀ (x y : H) (i : Fin n), 0 < N (ι x⁻¹ * single i i 1 * ι y) := by
    intro x y i
    apply N_pos
    intro h0
    have key : ι x * (ι x⁻¹ * single i i 1 * ι y) * ι y⁻¹ = single i i 1 := by
      simp only [Matrix.mul_assoc]
      rw [(hinv y).2, Matrix.mul_one, ← Matrix.mul_assoc, (hinv x).2, Matrix.one_mul]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul] at key
    have := congrFun (congrFun key i) i
    simp at this
  have hk : ∀ (x w y : H), w ∈ cent s → ∀ i,
      ι x⁻¹ * single i i 1 * ι x * ι (x⁻¹ * w * y) = ι w i i • (ι x⁻¹ * single i i 1 * ι y) := by
    intro x w y hw i
    rw [map_mul, map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (ι x) (ι x⁻¹), (hinv x).2, Matrix.one_mul,
      ← Matrix.mul_assoc (single i i (1 : ℂ)) (ι w), hleft w hw i, Matrix.smul_mul, Matrix.mul_smul]
  refine ⟨Bw l e, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold Bw
    apply contDiff_prod
    intro i _
    exact θ_smooth.comp (weightDiag_lemma_4 (e i) (he i))
  · intro z
    exact Finset.prod_nonneg (fun i _ => θ_nonneg _)
  · simp only [Bw]
    apply Finset.prod_pos
    intro i _
    have h1 : matCoord ι s = matCoord ι ((1 : H)⁻¹ * s * 1) := by simp
    rw [h1, hF]
    simp only [inv_one, map_one, Matrix.one_mul, Matrix.mul_one]
    rw [weightDiag_lemma, θ_one]
    norm_num
  · intro z h z' h'
    obtain ⟨τ, hτJ, hτ⟩ := hShift n J l hl hJl
      (fun i => N (ι z⁻¹ * single i i 1 * ι h) / N (ι z'⁻¹ * single i i 1 * ι h'))
      (fun i => div_pos (Fpos _ _ _) (Fpos _ _ _))
    obtain ⟨t₀, ht₀⟩ := (hrange (diagonal τ)).mpr hτJ
    have ht₀c : t₀ ∈ cent s := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      apply hinj
      rw [map_mul, map_mul, ht₀, hs, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      exact mul_comm _ _
    refine ⟨t₀, ht₀c, fun t ht => ?_⟩
    simp only [Bw]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : 1 < ‖l i‖ := (Finset.mem_filter.mp hi).2
    congr 1
    have hσ : ‖τ i‖ ^ 2 = N (ι z⁻¹ * single i i 1 * ι h) / N (ι z'⁻¹ * single i i 1 * ι h') := hτ i hi'
    have htt : ι (t * t₀) i i = ι t i i * τ i := by
      rw [map_mul, ht₀, hdiag t ht, Matrix.diagonal_mul_diagonal]
      simp
    rw [hF, hF, hk z t h ht i, hk z' (t * t₀) h' (mul_mem ht ht₀c) i, N_smul, N_smul, htt, norm_mul,
      mul_pow, hσ, mul_assoc (‖ι t i i‖ ^ 2), div_mul_cancel₀ _ (Fpos z' h' i).ne']
  · intro C₁ C₂ hC₁ hC₂
    obtain ⟨C, hC, hCp⟩ := hprop C₁ hC₁
    obtain ⟨C', hC', hC'p⟩ := hprop C₂ hC₂
    have hιc : Continuous (fun x : H => ι x) := hce.continuous
    have hFc : ∀ i, Continuous (fun p : H × H => N (ι p.1⁻¹ * single i i 1 * ι p.2)) := fun i =>
      weightDiag_lemma_3.comp (((hιc.comp continuous_fst.inv).matrix_mul continuous_const).matrix_mul
        (hιc.comp continuous_snd))
    have hGc : Continuous (fun p : H × H => ∑ i, (N (ι p.1⁻¹ * single i i 1 * ι p.2)
        + (N (ι p.1⁻¹ * single i i 1 * ι p.2))⁻¹)) :=
      continuous_finsetSum _ (fun i _ => (hFc i).add ((hFc i).inv₀ (fun p => (Fpos p.1 p.2 i).ne')))
    obtain ⟨M0, hM0⟩ := (hC.prod hC').exists_bound_of_continuousOn hGc.continuousOn
    obtain ⟨M, hM1, hbd⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ a ∈ C, ∀ b ∈ C', ∀ i,
        N (ι a⁻¹ * single i i 1 * ι b) ≤ M ∧ M⁻¹ ≤ N (ι a⁻¹ * single i i 1 * ι b) := by
      refine ⟨max M0 1, le_max_right _ _, fun a ha b hb i => ?_⟩
      have hP := Fpos a b i
      have h1 := hM0 (a, b) ⟨ha, hb⟩
      have h2 : N (ι a⁻¹ * single i i 1 * ι b) + (N (ι a⁻¹ * single i i 1 * ι b))⁻¹
          ≤ ∑ j, (N (ι a⁻¹ * single j j 1 * ι b) + (N (ι a⁻¹ * single j j 1 * ι b))⁻¹) :=
        Finset.single_le_sum (f := fun j => N (ι a⁻¹ * single j j 1 * ι b) + (N (ι a⁻¹ * single j j 1 * ι b))⁻¹)
          (fun j _ => by have := Fpos a b j; positivity) (Finset.mem_univ i)
      have h3 : ∑ j, (N (ι a⁻¹ * single j j 1 * ι b) + (N (ι a⁻¹ * single j j 1 * ι b))⁻¹) ≤ max M0 1 :=
        (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ h1).trans (le_max_left _ _))
      have hinvpos : 0 < (N (ι a⁻¹ * single i i 1 * ι b))⁻¹ := inv_pos.mpr hP
      refine ⟨by linarith, ?_⟩
      exact inv_le_of_inv_le₀ hP (by linarith)
    have hMpos : 0 < M := by linarith
    obtain ⟨R, hR⟩ := hBound n J l hdet hl hJl (1 / (2 * M)) (2 * M) (by positivity)
    have hQ : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) R) :=
      isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 R))
    refine ⟨(fun q : H × H × H => q.1⁻¹ * q.2.1 * q.2.2) ''
      (C ×ˢ (matCoord ι ⁻¹' (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) R)) ×ˢ C'),
      (hC.prod ((hce.isCompact_preimage hQ).prod hC')).image (by fun_prop), ?_⟩
    intro z k hz hzk hB
    obtain ⟨t, ht, htz⟩ := hCp z hz
    obtain ⟨t', ht', ht'z⟩ := hC'p (z * k) hzk
    have hu : t * t'⁻¹ ∈ cent s := mul_mem ht (inv_mem ht')
    simp only [Bw] at hB
    have hB' := Finset.prod_ne_zero_iff.mp hB
    have hX : ∀ i, ι z⁻¹ * single i i 1 * ι z * ι k
        = ι (t * t'⁻¹) i i • (ι (t * z)⁻¹ * single i i 1 * ι (t' * (z * k))) := by
      intro i
      have e1 : ι z⁻¹ = ι (t * z)⁻¹ * ι t := by
        rw [← map_mul, show (t * z)⁻¹ * t = z⁻¹ by group]
      have e2 : ι z * ι k = ι t'⁻¹ * ι (t' * (z * k)) := by
        rw [← map_mul, ← map_mul, show t'⁻¹ * (t' * (z * k)) = z * k by group]
      rw [Matrix.mul_assoc _ (ι z) (ι k), e2, e1, Matrix.mul_assoc (ι (t * z)⁻¹) (ι t), hcomm t ht i]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (ι t) (ι t'⁻¹), ← map_mul, ← Matrix.mul_assoc (single i i (1 : ℂ)) (ι (t * t'⁻¹)),
        hleft _ hu i, Matrix.smul_mul, Matrix.mul_smul]
    have hτb : ∀ i, 1 < ‖l i‖ → 1 / (2 * M) ≤ ‖ι (t * t'⁻¹) i i‖ ∧ ‖ι (t * t'⁻¹) i i‖ ≤ 2 * M := by
      intro i hi
      have hfi := hB' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have hsup := θ_supp hfi
      rw [hF, hX i, N_smul] at hsup
      obtain ⟨hlo, hhi⟩ := hbd _ htz _ ht'z i
      have hP := Fpos (t * z) (t' * (z * k)) i
      have hx0 : 0 ≤ ‖ι (t * t'⁻¹) i i‖ := norm_nonneg _
      have a1 : 1 / 2 ≤ ‖ι (t * t'⁻¹) i i‖ ^ 2 * M :=
        le_trans hsup.1 (mul_le_mul_of_nonneg_left hlo (sq_nonneg _))
      have a2 : ‖ι (t * t'⁻¹) i i‖ ^ 2 ≤ 3 / 2 * M := by
        have h4 : ‖ι (t * t'⁻¹) i i‖ ^ 2 * M⁻¹ ≤ 3 / 2 :=
          le_trans (mul_le_mul_of_nonneg_left hhi (sq_nonneg _)) hsup.2
        have h5 := mul_le_mul_of_nonneg_right h4 hMpos.le
        rwa [mul_assoc, inv_mul_cancel₀ hMpos.ne', mul_one] at h5
      constructor
      · rw [div_le_iff₀ (by positivity)]
        by_contra hc
        push_neg at hc
        have h6 : ‖ι (t * t'⁻¹) i i‖ * M < 1 / 2 := by linarith
        have h7 : ‖ι (t * t'⁻¹) i i‖ < 1 / 2 := by nlinarith
        nlinarith
      · by_contra hc
        push_neg at hc
        have h8 : 2 * M * (2 * M) < ‖ι (t * t'⁻¹) i i‖ * ‖ι (t * t'⁻¹) i i‖ :=
          mul_self_lt_mul_self (by positivity) hc
        nlinarith
    have hJu : (diagonal fun a => ι (t * t'⁻¹) a a)ᴴ * J * diagonal (fun a => ι (t * t'⁻¹) a a) = J := by
      rw [← hdiag _ hu]
      exact (hrange _).mp ⟨_, rfl⟩
    have hRu := hR (fun a => ι (t * t'⁻¹) a a) hJu hτb
    refine ⟨(t * z, t * t'⁻¹, t' * (z * k)), ⟨htz, ?_, ht'z⟩, ?_⟩
    · simp only [Set.mem_preimage, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
      intro a b
      show ‖ι (t * t'⁻¹) a b‖ ≤ R
      by_cases hab : a = b
      · subst hab
        exact hRu a
      · rw [hdiag _ hu, Matrix.diagonal_apply_ne _ hab, norm_zero]
        exact (norm_nonneg _).trans (hRu a)
    · show (t * z)⁻¹ * (t * t'⁻¹) * (t' * (z * k)) = k
      group
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PShiftT
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PShiftT

def rho (S : ℂ → ℝ) (z : ℂ) : ℂ :=
  if 1 < ‖z‖ then ((Real.sqrt (S z) : ℝ) : ℂ)
  else if ‖z‖ < 1 then (((Real.sqrt (S (star z)⁻¹) : ℝ) : ℂ))⁻¹ else 1

lemma key (S : ℂ → ℝ) (hS : ∀ z, 0 < S z) (z w : ℂ) (h : star z * w = 1) :
    star (rho S z) * rho S w = 1 := by
  have hz : z ≠ 0 := by rintro rfl; simp at h
  have hw : w = (star z)⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hw
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : ‖(star z)⁻¹‖ = ‖z‖⁻¹ := by rw [norm_inv, norm_star]
  have hcc : (star (star z)⁻¹)⁻¹ = z := by rw [star_inv₀, star_star, inv_inv]
  have e : ‖z‖ * ‖z‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hipos : 0 < ‖z‖⁻¹ := inv_pos.mpr hpos
  rcases lt_trichotomy 1 ‖z‖ with h1 | h1 | h1
  · have h2 : ‖z‖⁻¹ < 1 := by nlinarith
    have hs : (((Real.sqrt (S z)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS z)).ne'
    simp only [rho, hn, hcc]
    rw [if_pos h1, if_neg (by linarith), if_pos h2, Complex.star_def, Complex.conj_ofReal]
    exact mul_inv_cancel₀ hs
  · have h2 : ‖z‖⁻¹ = 1 := by rw [← h1, inv_one]
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    simp
  · have h2 : 1 < ‖z‖⁻¹ := by nlinarith
    have hs : (((Real.sqrt (S (star z)⁻¹)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS _)).ne'
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_pos h1, if_pos h2, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    exact inv_mul_cancel₀ hs

end MainStatements.WeightKernel.PShiftT

namespace MainStatements.WeightKernel

open MainStatements.WeightKernel.PShiftT in
theorem shiftT : ShiftT := by
  intro n J l hl hJ σ hσ
  classical
  let S : ℂ → ℝ := fun z => if h : ∃ i, l i = z then σ (Classical.choose h) else 1
  have hSpos : ∀ z, 0 < S z := by
    intro z
    simp only [S]
    split_ifs
    · exact hσ _
    · exact zero_lt_one
  have hSl : ∀ i, S (l i) = σ i := by
    intro i
    have h : ∃ j, l j = l i := ⟨i, rfl⟩
    simp only [S, dif_pos h]
    rw [hl (Classical.choose_spec h)]
  refine ⟨fun i => rho S (l i), ?_, ?_⟩
  · ext i j
    have hij := congrFun (congrFun hJ i) j
    simp only [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply] at hij ⊢
    by_cases h0 : J i j = 0
    · simp [h0]
    have e1 : star (l i) * l j = 1 := by
      have : (star (l i) * l j) * J i j = 1 * J i j := by rw [one_mul]; calc _ = star (l i) * J i j * l j := by ring
          _ = J i j := hij
      exact mul_right_cancel₀ h0 this
    have e2 : star (rho S (l i)) * rho S (l j) = 1 := key S hSpos _ _ e1
    calc _ = (star (rho S (l i)) * rho S (l j)) * J i j := by ring
      _ = J i j := by rw [e2, one_mul]
  · intro i hi
    show ‖rho S (l i)‖ ^ 2 = σ i
    rw [rho, if_pos hi, hSl, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hσ i).le]

end MainStatements.WeightKernel

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PIdentOne
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PIdentOne

def gR {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℝ :=
  B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) * φ (h⁻¹ * s * h)

def G {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℂ :=
  (gR ι s B φ z h : ℂ)

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] {n : ℕ} {ι : H →* Matrix (Fin n) (Fin n) ℂ}
    {s : H} {B : Mx n × Mx n → ℝ} {φ : H → ℝ}

theorem gR_cont (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (hφc : Continuous φ) (z : H) :
    Continuous (gR ι s B φ z) := by
  unfold gR
  have hBc : Continuous B := hB.smooth.continuous
  exact (hBc.comp (continuous_const.prodMk (hι.comp (continuous_const.mul continuous_id)))).mul
    (hφc.comp ((continuous_inv.mul continuous_const).mul continuous_id))

theorem gR_supp (hB : IsWeight ι s B) (hφ : HasCompactSupport φ) (z : H) :
    HasCompactSupport (gR ι s B φ z) := by
  obtain ⟨K, hK, hKp⟩ := hB.proper {z⁻¹ * s * z} (tsupport φ) isCompact_singleton hφ
  refine HasCompactSupport.intro (hK.image (continuous_const_mul z)) fun h hh => ?_
  by_contra hne
  apply hh
  refine ⟨z⁻¹ * h, hKp z (z⁻¹ * h) (Set.mem_singleton _) ?_ ?_, mul_inv_cancel_left z h⟩
  · rw [mul_inv_cancel_left z h]
    exact subset_tsupport _ (fun h0 => hne (by simp [gR, h0]))
  · exact fun h0 => hne (by simp [gR, h0])

theorem fiber (hB : IsWeight ι s B) (dt : Measure (cent s)) [dt.IsMulRightInvariant] (z h : H) :
    ∫ t : cent s, G ι s B φ z (t * h) ∂dt = ∫ t : cent s, G ι s B φ 1 (t * h) ∂dt := by
  obtain ⟨t₀, ht₀, e⟩ := hB.shift z h 1 h
  have key : ∀ v : H, v * s = s * v → (v * h)⁻¹ * s * (v * h) = h⁻¹ * s * h := fun v hv => by
    calc (v * h)⁻¹ * s * (v * h) = h⁻¹ * (v⁻¹ * (s * v)) * h := by group
      _ = h⁻¹ * (v⁻¹ * (v * s)) * h := by rw [hv]
      _ = h⁻¹ * s * h := by group
  have hc : ∀ u : cent s, ((u : H) * h)⁻¹ * s * (u * h) = h⁻¹ * s * h := fun u => key u (mem_cent.1 u.2)
  calc ∫ t : cent s, G ι s B φ z (t * h) ∂dt
        = ∫ t : cent s, G ι s B φ 1 (((t * ⟨t₀, ht₀⟩ : cent s) : H) * h) ∂dt := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [G, gR]
          rw [hc t, hc (t * ⟨t₀, ht₀⟩), ← mul_assoc z⁻¹, e t t.2]
          simp [mul_assoc]
    _ = _ := integral_mul_right_eq_self (fun t : cent s => G ι s B φ 1 ((t : H) * h)) ⟨t₀, ht₀⟩

theorem integral_eq (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (z : H) :
    ∫ h, G ι s B φ z h ∂μ = ∫ h, G ι s B φ 1 h ∂μ := by
  have hi : ∀ w, Integrable (G ι s B φ w) μ := fun w =>
    (Complex.continuous_ofReal.comp (gR_cont hι hB hφc w)).integrable_of_hasCompactSupport
      ((gR_supp hB hφ w).comp_left Complex.ofReal_zero)
  have w1 := (weil_integral (dt := dt) (isClosed_cent s) (hi z)).2.2
  have w2 := (weil_integral (dt := dt) (isClosed_cent s) (hi 1)).2.2
  rw [← w1, ← w2]
  exact congrArg (quotInt _ dt μ) (funext fun x => fiber hB dt z x)

theorem orig_eq (μ : Measure H) [μ.IsHaarMeasure] (z : H) :
    ∫ k, (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) * (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ∂μ =
      ∫ h, G ι s B φ z h ∂μ := by
  refine (integral_mul_left_eq_self (μ := μ) (fun k => (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) *
    (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ)) z⁻¹).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [G, gR, Complex.ofReal_mul]
  rw [show (z⁻¹ * h)⁻¹ * (z⁻¹ * s * z) * (z⁻¹ * h) = h⁻¹ * s * h by group]

theorem ne_zero (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (hφc : Continuous φ) (hφ : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφs : 0 < φ s) :
    ∫ h, G ι s B φ 1 h ∂μ ≠ 0 := by
  have hpos : 0 < ∫ h, gR ι s B φ 1 h ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (gR_cont hι hB hφc 1)
      (gR_supp hB hφ 1) (fun h => mul_nonneg (hB.nonneg _) (hφ0 _)) ?_
    simp only [gR, inv_one, one_mul, mul_one]
    exact (mul_pos hB.pos hφs).ne'
  simp only [G]
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end MainStatements.WeightKernel.PIdentOne

theorem MainStatements.WeightKernel.identOne : IdentOne := by
  intro H _ _ _ _ _ _ _ _ n ι hι s B hB μ _ dt _ _ φ hφc hφ hφ0 hφs
  exact ⟨_, PIdentOne.ne_zero hι hB μ hφc hφ hφ0 hφs, fun z =>
    (PIdentOne.orig_eq μ z).trans (PIdentOne.integral_eq hι hB μ dt hφc hφ z)⟩

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PVanish
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PVanish

def mul3 {n : ℕ} (A B C : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n := fun a b => (of A * of B * of C) a b

theorem contDiff_triple_matrix_product {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g h : E → MainStatements.WeightKernel.Mx n}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ fun x => mul3 (f x) (g x) (h x) := by
  have e : ∀ (u : E → Mx n), ContDiff ℝ ∞ u → ∀ a b : Fin n, ContDiff ℝ ∞ fun x => u x a b :=
    fun u hu a b => contDiff_pi.1 (contDiff_pi.1 hu a) b
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [mul3, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun j _ =>
    (ContDiff.sum fun k _ => (e f hf a k).mul (e g hg k j)).mul (e h hh j b)

theorem triple_product_matrix_coordinates {H : Type} [Group H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (g h l : H) :
    mul3 (matCoord ι g) (matCoord ι h) (matCoord ι l) = matCoord ι (g * h * l) := by
  funext a b
  show (ι g * ι h * ι l) a b = ι (g * h * l) a b
  rw [map_mul, map_mul]

end MainStatements.WeightKernel.PVanish

open MainStatements.WeightKernel.PVanish in
theorem MainStatements.WeightKernel.vanish : KerSwap → IdentOne → IdentTwo → Vanish := by
  intro hSwap hOne hTwo H _ _ _ _ _ _ _ _ n ι hemb s B hB μ _ _ dt _ _ Ω I _ _ m _ c q hK hq hInv φ hφ hOrb
  obtain ⟨hφc, Φφ, hΦφ, hφeq⟩ := hφ
  have hmc : Continuous (matCoord ι) := hemb.continuous
  have hφcont : Continuous φ := by
    rw [show φ = fun g => Φφ (matCoord ι g) from funext hφeq]
    exact hΦφ.continuous.comp hmc
  let bp : ContDiffBump (matCoord ι s) := ⟨1, 2, one_pos, one_lt_two⟩
  let ψ : H → ℝ := fun y => bp (matCoord ι y)
  have hψc : Continuous ψ := bp.continuous.comp hmc
  have hψcs : HasCompactSupport ψ := bp.hasCompactSupport.comp_isClosedEmbedding hemb
  have hψs : 0 < ψ s := by
    have : ψ s = 1 := bp.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
    rw [this]
    exact one_pos
  obtain ⟨a, ha0, ha⟩ := hOne H n ι hmc s B hB μ dt ψ hψc hψcs (fun y => bp.nonneg) hψs
  obtain ⟨Kset, hKc, hKprop⟩ := hB.proper (tsupport φ) (tsupport ψ) hφc.isCompact hψcs.isCompact
  let p : H → Mx n × Mx n := fun k => (matCoord ι k, matCoord ι k⁻¹)
  have hp : Continuous p := hmc.prodMk (hmc.comp continuous_inv)
  let W₁ : Mx n × (Mx n × Mx n) → ℂ := fun z =>
    Φφ z.1 * ((B (z.1, z.2.1) : ℝ) : ℂ) * ((bp (mul3 z.2.2 z.1 z.2.1) : ℝ) : ℂ)
  let W₂ : Mx n × (Mx n × Mx n) → ℂ := fun z =>
    Φφ (mul3 z.2.1 z.1 z.2.2) * ((B (mul3 z.2.1 z.1 z.2.2, z.2.1) : ℝ) : ℂ) * ((bp z.1 : ℝ) : ℂ)
  have hfst : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.1 := contDiff_fst
  have hA : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.1 := contDiff_fst.comp contDiff_snd
  have hC : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.2 := contDiff_snd.comp contDiff_snd
  have hM1 := contDiff_triple_matrix_product hC hfst hA
  have hM2 := contDiff_triple_matrix_product hA hfst hC
  have hW₁ : ContDiff ℝ ∞ W₁ :=
    ((hΦφ.comp hfst).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hfst.prodMk hA)))).mul
      (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hM1))
  have hW₂ : ContDiff ℝ ∞ W₂ :=
    ((hΦφ.comp hM2).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hM2.prodMk hA)))).mul
      (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hfst))
  have hW₁pt : ∀ y k : H, W₁ (matCoord ι y, p k) =
      φ y * ((B (matCoord ι y, matCoord ι k) : ℂ) * (ψ (k⁻¹ * y * k) : ℂ)) := by
    intro y k
    simp only [W₁, p, ψ]
    rw [triple_product_matrix_coordinates, hφeq, mul_assoc]
  have hW₂pt : ∀ y k : H, W₂ (matCoord ι y, p k) =
      φ (k * y * k⁻¹) * (B (matCoord ι (k * y * k⁻¹), matCoord ι k) : ℂ) * (ψ y : ℂ) := by
    intro y k
    simp only [W₂, p, ψ]
    rw [triple_product_matrix_coordinates, hφeq]
  have hvan1 : ∀ z k : H, k ∉ Kset → W₁ (matCoord ι (z⁻¹ * s * z), p k) = 0 := by
    intro z k hk
    rw [hW₁pt]
    by_contra hne
    apply hk
    have h1 : φ (z⁻¹ * s * z) ≠ 0 := left_ne_zero_of_mul hne
    have h23 := right_ne_zero_of_mul hne
    have h2 : (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) ≠ 0 := left_ne_zero_of_mul h23
    have h3 : (ψ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ≠ 0 := right_ne_zero_of_mul h23
    have e : (z * k)⁻¹ * s * (z * k) = k⁻¹ * (z⁻¹ * s * z) * k := by group
    refine hKprop z k (subset_tsupport _ h1) ?_ (fun h0 => h2 (by simp [h0]))
    rw [e]
    exact subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))
  have hvan2 : ∀ w k : H, k ∉ Kset → W₂ (matCoord ι (w⁻¹ * s * w), p k) = 0 := by
    intro w k hk
    rw [hW₂pt]
    by_contra hne
    apply hk
    have h12 := left_ne_zero_of_mul hne
    have h3 : (ψ (w⁻¹ * s * w) : ℂ) ≠ 0 := right_ne_zero_of_mul hne
    have h1 : φ (k * (w⁻¹ * s * w) * k⁻¹) ≠ 0 := left_ne_zero_of_mul h12
    have h2 : (B (matCoord ι (k * (w⁻¹ * s * w) * k⁻¹), matCoord ι k) : ℂ) ≠ 0 :=
      right_ne_zero_of_mul h12
    have e1 : (w * k⁻¹)⁻¹ * s * (w * k⁻¹) = k * (w⁻¹ * s * w) * k⁻¹ := by group
    have e2 : (w * k⁻¹ * k)⁻¹ * s * (w * k⁻¹ * k) = w⁻¹ * s * w := by group
    refine hKprop (w * k⁻¹) k ?_ ?_ ?_
    · rw [e1]
      exact subset_tsupport _ h1
    · rw [e2]
      exact subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))
    · rw [e1]
      exact fun h0 => h2 (by simp [h0])
  have h1 := hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₁ p Kset (tsupport φ) hW₁ hp hKc
    hφc.isCompact (by
      intro k _ y hy
      have : φ y = 0 := by
        by_contra h0
        exact hy (subset_tsupport _ h0)
      rw [hW₁pt, this, zero_mul])
  have h2 := hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₂ p Kset (tsupport ψ) hW₂ hp hKc
    hψcs.isCompact (by
      intro k _ y hy
      have : ψ y = 0 := by
        by_contra h0
        exact hy (subset_tsupport _ h0)
      rw [hW₂pt, this]
      simp)
  have hR1 : ∫ x, ker c q (fun y => ∫ k in Kset, W₁ (matCoord ι y, p k) ∂μ) x ∂m =
      a * ∫ x, ker c q φ x ∂m := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [MainStatements.WeightKernel.ker]
    rw [← tsum_mul_left]
    congr 1
    funext i
    obtain ⟨z, hz⟩ := hq i x
    rw [hz, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan1 z)]
    simp only [hW₁pt]
    rw [integral_const_mul, ha z]
    ring
  have hstep : ∀ k : H, ∫ x, ker c q (fun y => W₁ (matCoord ι y, p k)) x ∂m =
      ∫ x, ker c q (fun y => W₂ (matCoord ι y, p k)) x ∂m := by
    intro k
    have hmem : (fun y => W₂ (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨?_, fun Y => W₂ (Y, p k), hW₂.comp (contDiff_id.prodMk contDiff_const), fun g => rfl⟩
      refine hψcs.mono ?_
      intro y hy
      rw [Function.mem_support] at hy ⊢
      intro h0
      apply hy
      rw [hW₂pt, h0]
      simp
    have hfun : (fun y => W₁ (matCoord ι y, p k)) =
        fun y => W₂ (matCoord ι (k⁻¹ * y * k⁻¹⁻¹), p k) := by
      funext y
      rw [hW₂pt, hW₁pt]
      have e : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ = y := by group
      rw [e, inv_inv]
      ring
    rw [hfun]
    exact hInv _ hmem k⁻¹
  have hR2 : ∫ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x ∂m = 0 := by
    have hz : ∀ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x = 0 := by
      intro x
      simp only [MainStatements.WeightKernel.ker]
      refine (tsum_congr fun i => ?_).trans tsum_zero
      obtain ⟨w, hw⟩ := hq i x
      rw [hw, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan2 w)]
      simp only [hW₂pt]
      rw [integral_mul_const, hTwo H n ι hmc s B hB μ dt φ hφcont hφc hOrb w]
      simp
    simp [hz]
  have key : a * ∫ x, ker c q φ x ∂m = 0 := by
    rw [← hR1, ← h1]
    simp only [hstep]
    rw [h2]
    exact hR2
  exact (mul_eq_zero.1 key).resolve_left ha0

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PClosedGraph
open MeasureTheory Set Filter Topology

noncomputable section

namespace MainStatements.WeightKernel.PClosedGraph

variable {Ω I : Type} [MeasurableSpace Ω] {m : Measure Ω} {u : I → Ω → ℂ}

lemma summable_norm_lp (a : lp (fun _ : I => ℂ) 1) : Summable (fun i => ‖a i‖) := by
  have h := (memℓp_gen_iff (p := (1 : ENNReal)) (by norm_num)).1 (lp.memℓp a)
  simpa using h

lemma norm_lp_eq (a : lp (fun _ : I => ℂ) 1) : ‖a‖ = ∑' i, ‖a i‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

lemma summable_mul {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : I → ℂ) (ha : Summable fun i => ‖a i‖) :
    Summable (fun i => a i * u i x) := by
  refine Summable.of_norm_bounded (ha.mul_right M) fun i => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)

lemma norm_tsum_mul_le {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : lp (fun _ : I => ℂ) 1) :
    ‖∑' i, a i * u i x‖ ≤ ‖a‖ * M := by
  have ha := summable_norm_lp a
  have hs := summable_mul hM a ha
  calc ‖∑' i, a i * u i x‖ ≤ ∑' i, ‖a i * u i x‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' i, ‖a i‖ * M := by
        refine Summable.tsum_le_tsum (fun i => ?_) hs.norm (ha.mul_right M)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)
    _ = ‖a‖ * M := by rw [tsum_mul_right, norm_lp_eq]

lemma tsum_single [DecidableEq I] (i : I) (x : Ω) : ∑' j, (lp.single 1 i (1 : ℂ) : lp (fun _ : I => ℂ) 1) j * u j x = u i x := by
  rw [tsum_eq_single i]
  · simp [lp.single_apply]
  · intro j hj
    simp [lp.single_apply, Pi.single_apply, hj]

end MainStatements.WeightKernel.PClosedGraph

open MainStatements.WeightKernel.PClosedGraph in
theorem MainStatements.WeightKernel.closedGraph : MainStatements.WeightKernel.ClosedGraph := by
  intro Ω I _ m u hbd hint
  choose M hM using hbd
  let Tf : lp (fun _ : I => ℂ) 1 → Ω → ℂ := fun a x => ∑' i, a i * u i x
  have hTi : ∀ a : lp (fun _ : I => ℂ) 1, Integrable (Tf a) m := fun a => hint a (summable_norm_lp a)
  have hadd : ∀ a b : lp (fun _ : I => ℂ) 1, Tf (a + b) = Tf a + Tf b := by
    intro a b
    funext x
    simp only [Tf, Pi.add_apply, lp.coeFn_add, add_mul]
    exact Summable.tsum_add (summable_mul (hM x) a (summable_norm_lp a))
      (summable_mul (hM x) b (summable_norm_lp b))
  have hsmul : ∀ (c : ℂ) (a : lp (fun _ : I => ℂ) 1), Tf (c • a) = fun x => c • Tf a x := by
    intro c a
    funext x
    simp only [Tf, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact tsum_mul_left
  let T : lp (fun _ : I => ℂ) 1 →ₗ[ℂ] Lp ℂ 1 m :=
    { toFun := fun a => Integrable.toL1 (Tf a) (hTi a)
      map_add' := by
        intro a b
        rw [← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hadd a b))
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply]
        rw [← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hsmul c a)) }
  have hTapp : ∀ a, T a = Integrable.toL1 (Tf a) (hTi a) := fun a => rfl
  have hcont : Continuous T := by
    refine T.continuous_of_seq_closed_graph fun s a y hs hy => ?_
    have hmeas := tendstoInMeasure_of_tendsto_Lp hy
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    apply Lp.ext
    filter_upwards [hae, (hTi a).coeFn_toL1, ae_all_iff.2 (fun n => (hTi (s n)).coeFn_toL1)]
      with x hx1 hx2 hx3
    rw [hTapp a, hx2]
    have hpt : Tendsto (fun n => Tf (s n) x) atTop (𝓝 (Tf a x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n => ‖s n - a‖ * M x) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n => ‖s n - a‖) atTop (𝓝 0) := by
          rw [← tendsto_iff_norm_sub_tendsto_zero]
          exact hs
        simpa using h0.mul_const (M x)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      have e : Tf (s n) x - Tf a x = Tf (s n - a) x := by
        have := congrFun (hadd (s n - a) a) x
        simp only [sub_add_cancel, Pi.add_apply] at this
        rw [this]
        ring
      rw [e]
      exact norm_tsum_mul_le (hM x) (s n - a)
    have hsub := hpt.comp hns.tendsto_atTop
    refine tendsto_nhds_unique hx1 ?_
    refine hsub.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hTapp, hx3]
  let T' : lp (fun _ : I => ℂ) 1 →L[ℂ] Lp ℂ 1 m := ⟨T, hcont⟩
  refine ⟨‖T'‖, fun i => ?_⟩
  classical
  let e : lp (fun _ : I => ℂ) 1 := lp.single 1 i (1 : ℂ)
  have hTe : Tf e = u i := funext fun x => tsum_single i x
  have hint_i : Integrable (u i) m := hTe ▸ hTi e
  refine ⟨hint_i, ?_⟩
  have hn : ‖T e‖ = ∫ x, ‖u i x‖ ∂m := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [(hTi e).coeFn_toL1] with x hx
    rw [hTapp, hx, hTe]
  have hle : ‖T' e‖ ≤ ‖T'‖ * ‖e‖ := T'.le_opNorm e
  have he : ‖e‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  rw [← hn]
  calc ‖T e‖ = ‖T' e‖ := rfl
    _ ≤ ‖T'‖ * ‖e‖ := hle
    _ = ‖T'‖ := by rw [he, mul_one]
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.WeightKernel

theorem regClassInt_holds : MainStatements.RegularCuspidalTrace.RegClassInt := MainStatements.WeightKernel.RegInt.regClassInt PositivityTheory.Prw.siegelCore_holds

end MainStatements.WeightKernel
