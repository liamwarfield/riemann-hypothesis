module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensor
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationAtRadiusConcaveContSlope
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnGaussNormAcrisRadiusIco
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnGaussNormAcrisRadiusIco
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
open Filter Topology

noncomputable section

namespace GlobalTheory.PMon.Gauss

theorem gC_zero_of_lt_one (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  unfold gC
  split_ifs with h
  · have hN := Classical.choose_spec h
    set N := Classical.choose h
    have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
    have hl : N (l : Formalism.Per.Acris l) = ρ := by
      have := hN.2.2.2.2 (l : Formalism.Per.Ainf l)
      rw [map_natCast] at this
      rw [this]
      exact GlobalTheory.GaussSlope.gauss_l l h0
    rw [mul_zero, hl] at hm
    have : (1 - ρ) * N 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · rfl

theorem continuousOn_gC (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) :
    ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  by_cases hx : x = 0
  · subst hx
    refine (continuousOn_const (c := (0 : ℝ))).congr fun ρ hρ => ?_
    exact gC_zero_of_lt_one l (hl0.le.trans hρ.1) hρ.2
  intro ρ₀ hρ₀
  have hpos : 0 < ρ₀ := hl0.trans_le hρ₀.1
  obtain ⟨⟨c, k, ρ₂, -, h02, -, hR⟩, hL⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l x hx ρ₀ hρ₀.1 hρ₀.2
  have hS : Set.Ico (l : ℝ)⁻¹ 1 = (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Iic ρ₀) ∪ (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Ici ρ₀) := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro hy
      rcases le_total y ρ₀ with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h) <;> exact h.1
  rw [ContinuousWithinAt, hS, ← ContinuousWithinAt, continuousWithinAt_union]
  constructor
  · rcases eq_or_lt_of_le hρ₀.1 with heq | hlt
    · refine (continuousWithinAt_singleton (f := fun ρ => gC l ρ x) (x := ρ₀)).mono ?_
      rintro y ⟨hy1, hy2⟩
      exact le_antisymm hy2 (heq ▸ hy1.1)
    · obtain ⟨c', k', ρ₁, -, -, h10, hL'⟩ := hL hlt
      have hg : ContinuousWithinAt (fun ρ : ℝ => c' * ρ ^ k') (Set.Iic ρ₀) ρ₀ :=
        (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k' (Or.inl hpos.ne'))).continuousWithinAt
      have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₁ ρ₀) ρ₀ :=
        (hg.mono Set.Icc_subset_Iic_self).congr (fun y hy => hL' y hy) (hL' ρ₀ ⟨h10.le, le_rfl⟩)
      exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE h10)).mono Set.inter_subset_right
  · have hg : ContinuousWithinAt (fun ρ : ℝ => c * ρ ^ k) (Set.Ici ρ₀) ρ₀ :=
      (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k (Or.inl hpos.ne'))).continuousWithinAt
    have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₀ ρ₂) ρ₀ :=
      (hg.mono Set.Icc_subset_Ici_self).congr (fun y hy => hR y hy) (hR ρ₀ ⟨le_rfl, h02.le⟩)
    exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE h02)).mono Set.inter_subset_right

theorem continuousOn_gC_target :
    ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) :=
  fun l _ x => continuousOn_gC l x

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnGaussNormAcrisRadiusIcoStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_gaussNormAcrisRadius_Ico : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  first | exact @GlobalTheory.PMon.Gauss.continuousOn_gC_target | exact GlobalTheory.PMon.Gauss.continuousOn_gC_target | (intros; apply GlobalTheory.PMon.Gauss.continuousOn_gC_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationAtRadiusConcaveContSlope
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

lemma one_lt_natCast_of_prime : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

lemma prime_rpow_neg_mem_Ico_inv_one {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hL := one_lt_natCast_of_prime (l := l)
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

lemma logb_gaussNormAcrisRadius_convex {x : Formalism.Per.Acris l} (hx : x ≠ 0) {r₁ r₂ t : ℝ} (h1 : 0 < r₂) (h12 : r₂ ≤ r₁)
    (h2 : r₁ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.logb l (gC l ((l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))) x) ≤
      t * Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x) + (1 - t) * Real.logb l (gC l ((l : ℝ) ^ (-r₂)) x) := by
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  obtain ⟨a1, b1⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) (by linarith : 0 < r₁) h2
  obtain ⟨a2, b2⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) h1 (by linarith)
  have hm0 : 0 < t * r₁ + (1 - t) * r₂ := by nlinarith
  have hm1 : t * r₁ + (1 - t) * r₂ ≤ 1 := by nlinarith
  obtain ⟨a0, b0⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) hm0 hm1
  have hle : (l : ℝ) ^ (-r₁) ≤ (l : ℝ) ^ (-r₂) := Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have key := GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x _ _ t a1 hle b2 ht0 ht1
  have heq : ((l : ℝ) ^ (-r₁)) ^ t * ((l : ℝ) ^ (-r₂)) ^ (1 - t) = (l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂)) := by
    rw [← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    congr 1; ring
  rw [heq] at key
  have p1 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a1 b1
  have p2 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a2 b2
  have p0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a0 b0
  calc Real.logb l (gC l ((l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))) x)
      ≤ Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x ^ t * gC l ((l : ℝ) ^ (-r₂)) x ^ (1 - t)) :=
        Real.logb_le_logb_of_le hL p0 key
    _ = t * Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x) + (1 - t) * Real.logb l (gC l ((l : ℝ) ^ (-r₂)) x) := by
        rw [Real.logb_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne',
          Real.logb_rpow_eq_mul_logb_of_pos p1, Real.logb_rpow_eq_mul_logb_of_pos p2]

theorem vr_concaveOn_Ioc {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) := by
  refine ⟨convex_Ioc 0 1, ?_⟩
  intro r₁ hr₁ r₂ hr₂ a b ha hb hab
  simp only [vr, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  rcases le_total r₂ r₁ with h | h
  · have := logb_gaussNormAcrisRadius_convex hx hr₂.1 h hr₁.2 ha (by linarith)
    linarith
  · have := logb_gaussNormAcrisRadius_convex hx hr₁.1 h hr₂.2 (t := 1 - a) (by linarith) (by linarith)
    have e : (1 - a) * r₂ + (1 - (1 - a)) * r₁ = a * r₁ + (1 - a) * r₂ := by ring
    rw [e] at this
    linarith

theorem vr_continuousOn_Ioc {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) := by
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  have hmaps : Set.MapsTo (fun r : ℝ => (l : ℝ) ^ (-r)) (Set.Ioc 0 1) (Set.Ico (l : ℝ)⁻¹ 1) :=
    fun r hr => prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2
  have hc1 : Continuous (fun r : ℝ => (l : ℝ) ^ (-r)) :=
    Continuous.rpow continuous_const continuous_neg (fun _ => Or.inl hL0.ne')
  have hc2 : ContinuousOn (fun r : ℝ => gC l ((l : ℝ) ^ (-r)) x) (Set.Ioc 0 1) :=
    (GlobalTheory.T.continuousOn_gaussNormAcrisRadius_Ico l x).comp hc1.continuousOn hmaps
  have hpos : ∀ r ∈ Set.Ioc (0 : ℝ) 1, gC l ((l : ℝ) ^ (-r)) x ≠ 0 := fun r hr =>
    (GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).1 (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).2).ne'
  simp only [vr, Real.logb]
  exact ((hc2.log hpos).div_const _).neg

theorem vr_right_affine {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧
      ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) := by
  intro r hr
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  obtain ⟨a, b⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) hr.1 hr.2.le
  have hlt : (l : ℝ)⁻¹ < (l : ℝ) ^ (-r) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_lt_rpow_of_exponent_lt hL (by linarith [hr.2])
  obtain ⟨c, k, ρ₁, hc, hρ₁, hρ₁r, hmon⟩ := (GlobalTheory.T.gaussNormAcris_locally_monomial l x hx _ a b).2 hlt
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le (inv_pos.mpr hL0) hρ₁
  have hsr : r < -Real.logb l ρ₁ := by
    have := Real.logb_lt_logb hL hρ₁0 hρ₁r
    rw [Real.logb_rpow hL0 hL.ne'] at this
    linarith
  have hρs : ρ₁ = (l : ℝ) ^ (-(-Real.logb l ρ₁)) := by
    rw [neg_neg, Real.rpow_logb hL0 hL.ne' hρ₁0]
  have hlogl : Real.log l ≠ 0 := (Real.log_pos hL).ne'
  have formula : ∀ t, r ≤ t → t ≤ -Real.logb l ρ₁ → vr l t x = -Real.logb l c + k * t := by
    intro t ht1 ht2
    have hmem : (l : ℝ) ^ (-t) ∈ Set.Icc ρ₁ ((l : ℝ) ^ (-r)) := by
      constructor
      · rw [hρs]; exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
      · exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
    simp only [vr]
    rw [hmon _ hmem]
    simp only [Real.logb]
    rw [Real.log_mul hc.ne' (zpow_ne_zero _ (Real.rpow_pos_of_pos hL0 _).ne'), Real.log_zpow,
      Real.log_rpow hL0]
    field_simp
    ring
  refine ⟨k, min (-Real.logb l ρ₁ - r) (1 - r), lt_min (by linarith) (by linarith [hr.2]),
    by linarith [min_le_right (-Real.logb l ρ₁ - r) (1 - r)], ?_⟩
  intro t ht
  have hs1 : r + min (-Real.logb l ρ₁ - r) (1 - r) ≤ -Real.logb l ρ₁ := by
    linarith [min_le_left (-Real.logb l ρ₁ - r) (1 - r)]
  rw [formula t ht.1 (ht.2.trans hs1), formula r le_rfl hsr.le]
  ring

theorem vr_concave_cont_rightSlope : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 →
    ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) ∧ ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) ∧
      ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧
        ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) :=
  fun _ _ _ hx => ⟨vr_concaveOn_Ioc hx, vr_continuousOn_Ioc hx, vr_right_affine hx⟩

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationAtRadiusConcaveContSlopeStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) ∧ ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) ∧ ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) := by
  first | exact @GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope | exact GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope | (intros; apply GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEmbeddingIntegersResCharUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEmbeddingIntegersResCharUnit
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.NLocPlace

theorem vAdd_int (D : D7) (w : D.what₂.places.Pl) (a : 𝓞 D.what₂.LL) (ha : (a : D.what₂.LL) ≠ 0) :
    0 ≤ vAdd (D.plEq w) (a : D.what₂.LL) ∧ (a ∈ (D.plEq w).asIdeal ↔ 0 < vAdd (D.plEq w) (a : D.what₂.LL)) := by
  have hv0 : (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hle : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL a) ≤ 1 :=
    (D.plEq w).valuation_le_one a
  have hmem := (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL) a
  change (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) ≤ 1 at hle
  change (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) < 1 ↔ _ at hmem
  unfold vAdd
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hmem
  refine ⟨by omega, ?_⟩
  rw [← hmem]
  omega

end GlobalTheory.NLocPlace

namespace GlobalTheory.NLocPlace

theorem ec_int_resChar_unit : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl),
    (∀ a : 𝓞 D.what₂.LL, B.ec j w (a : D.what₂.LL) ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range) ∧
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal ∧
    ∀ (a : 𝓞 D.what₂.LL) (z : B.Oc j w), algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) z = B.ec j w (a : D.what₂.LL) →
      (a ∈ (D.plEq w).asIdeal ↔ ¬ IsUnit z) := by
  intro D M B j w
  have hinj : Function.Injective (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))) :=
    IsFractionRing.injective _ _

  have hval : ∀ x : D.what₂.LL, x ≠ 0 → D.what₂.places.val w x = ((vAdd (D.plEq w) x : ℤ) : WithTop ℤ) :=
    fun x hx => D.val_eq w x hx

  have hsum : ∀ x : D.what₂.LL, x ≠ 0 → vAdd (D.plEq w) x + vAdd (D.plEq w) x⁻¹ = 0 := by
    intro x hx
    have h1 : D.what₂.places.val w (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, AddValuation.map_one]
    rw [AddValuation.map_mul, hval x hx, hval x⁻¹ (inv_ne_zero hx), ← WithTop.coe_add] at h1
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply (B.ec_w j w _).1
    by_cases ha : (a : D.what₂.LL) = 0
    · rw [ha, AddValuation.map_zero]; exact le_top
    · rw [hval _ ha]
      exact_mod_cast (vAdd_int D w a ha).1
  · have hp0 : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) ≠ 0 := by
      push_cast; exact Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
    rw [(vAdd_int D w _ hp0).2]
    have h1 := D.what₂.places.val_resChar w
    have hc : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
      push_cast; rfl
    rw [← hc, hval _ hp0] at h1
    have h2 : vAdd (D.plEq w) (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) :=
      WithTop.coe_injective h1
    rw [h2]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  · intro a z hz
    by_cases ha : (a : D.what₂.LL) = 0
    · have ha' : a = 0 := by exact_mod_cast ha
      have hz0 : z = 0 := hinj (by rw [hz, ha, map_zero, map_zero])
      subst ha' hz0
      simp
    · have hec : B.ec j w (a : D.what₂.LL) ≠ 0 := by
        rw [map_ne_zero]; exact ha
      obtain ⟨hnn, hiff⟩ := vAdd_int D w a ha
      have hs := hsum _ ha
      rw [hiff]
      constructor
      · rintro hpos ⟨u, hu⟩
        have h1 : algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) (↑u⁻¹ : B.Oc j w) = B.ec j w (a : D.what₂.LL)⁻¹ := by
          rw [map_inv₀, ← hz, ← hu]
          apply eq_inv_of_mul_eq_one_right
          rw [← map_mul, Units.mul_inv, map_one]
        have h2 := (B.ec_w j w (a : D.what₂.LL)⁻¹).2 ⟨_, h1⟩
        rw [hval _ (inv_ne_zero ha)] at h2
        have h3 : (0 : ℤ) ≤ vAdd (D.plEq w) (a : D.what₂.LL)⁻¹ := by exact_mod_cast h2
        omega
      · intro hnu
        by_contra hle
        have h0 : vAdd (D.plEq w) (a : D.what₂.LL)⁻¹ = 0 := by omega
        have h2 : 0 ≤ D.what₂.places.val w (a : D.what₂.LL)⁻¹ := by
          rw [hval _ (inv_ne_zero ha), h0]; rfl
        obtain ⟨y, hy⟩ := (B.ec_w j w _).1 h2
        apply hnu
        have hzy : z * y = 1 := hinj (by rw [map_mul, map_one, hz, hy, ← map_mul, mul_inv_cancel₀ ha, map_one])
        exact ⟨⟨z, y, hzy, by rw [mul_comm]; exact hzy⟩, rfl⟩

end GlobalTheory.NLocPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEmbeddingIntegersResCharUnitStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffEmbedding_integers_resChar_unit : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl), (∀ a : 𝓞 D.what₂.LL, B.ec j w (a : D.what₂.LL) ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range) ∧ ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal ∧ ∀ (a : 𝓞 D.what₂.LL) (z : B.Oc j w), algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) z = B.ec j w (a : D.what₂.LL) → (a ∈ (D.plEq w).asIdeal ↔ ¬ IsUnit z) := by
  first | exact @GlobalTheory.NLocPlace.ec_int_resChar_unit | exact GlobalTheory.NLocPlace.ec_int_resChar_unit | (intros; apply GlobalTheory.NLocPlace.ec_int_resChar_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientsClosedSubQuotSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientsClosedSubQuotSum
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedFun.LatQuot

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k]

def subLattice [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O) (lam : O)
    (hl : algebraMap O LL lam ≠ 0) (P : Submodule O ↥T.L.T) (hP : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P)
    (hlam : ∀ x, lam • x ∈ P) : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) T.ρ where
  T := P.map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨latRep T.L g x, hP g x hx, rfl⟩
  fg := by
    have := StdAdm.finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := StdAdm.finite_lat T
    have := T.L.free
    have : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have h1 : lam • y ∈ P.map T.L.T.subtype := ⟨lam • ⟨y, hy⟩, hlam _, rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL lam)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← algebraMap_smul LL lam y, inv_smul_smul₀ hl] at h2

theorem onto_sub [IsDomain O] [IsPrincipalIdealRing O] (lam : O) (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f)
    (hi : Function.Injective f) (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)) (hq : Onto T B q) :
    ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q := by
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hr' : ∀ x, r (f x) = x := fun x => LinearMap.congr_fun hr x
  let P : Submodule O ↥T.L.T := (LinearMap.range (f.restrictScalars O)).comap q
  have hP : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P := by
    rintro g x ⟨a, ha⟩
    refine ⟨A.ρ g a, ?_⟩
    have ha' : f a = q x := ha
    change f (A.ρ g a) = q _
    rw [hf, ha', hq.2]
  have hlam : ∀ x, lam • x ∈ P := by
    intro x
    refine ⟨0, ?_⟩
    rw [map_zero, map_smul, ← algebraMap_smul k lam, hk, zero_smul]
  let L := subLattice T lam hl P hP hlam
  have hle : L.T ≤ T.L.T := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨withLat T L, (r.restrictScalars O).comp (q.comp (Submodule.inclusion hle)), ?_, ?_⟩
  · intro a
    obtain ⟨x, hx⟩ := hq.1 (f a)
    refine ⟨⟨x.1, x, ⟨a, hx.symm⟩, rfl⟩, ?_⟩
    change r (q x) = a
    rw [hx, hr']
  · rintro g ⟨_, x, ⟨a, ha⟩, rfl⟩
    have ha' : f a = q x := ha
    change r (q (latRep T.L g x)) = A.ρ g (r (q x))
    rw [hq.2, ← ha', ← hf, hr', hr']

theorem onto_quot (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f)
    (hs : Function.Surjective f) (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q) :
    Onto T B ((f.restrictScalars O).comp q) := by
  refine ⟨hs.comp hq.1, fun g x => ?_⟩
  change f (q _) = B.ρ g (f (q x))
  rw [hq.2, hf]

theorem onto_sum (A B C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k))
    (hi : IsHom A C i) (hj : IsHom B C j) (hs : Function.Surjective (i.coprod j))
    (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q)
    (T' : LocLat G Qp LL O) (q' : ↥T'.L.T →ₗ[O] (Fin B.m → k)) (hq' : Onto T' B q') :
    Onto (StdAdm.prodLat T T') C (((i.coprod j).restrictScalars O).comp
      ((q.prodMap q').comp (StdAdm.prodLatEquiv T T').toLinearMap)) := by
  refine ⟨hs.comp ((hq.1.prodMap hq'.1).comp (StdAdm.prodLatEquiv T T').surjective), fun g x => ?_⟩
  change i (q (latRep T.L g (StdAdm.prodLatEquiv T T' x).1)) + j (q' (latRep T'.L g (StdAdm.prodLatEquiv T T' x).2)) =
    C.ρ g (i (q (StdAdm.prodLatEquiv T T' x).1) + j (q' (StdAdm.prodLatEquiv T T' x).2))
  rw [hq.2, hq'.2, hi, hj, map_add (f := _)]

theorem onto_one [IsDomain O] (hs : Function.Surjective (algebraMap O k)) (T : LocLat G Qp LL O) (e₀ : ↥T.L.T)
    (hρ : ∀ g x, T.ρ g x = x) (h0 : e₀ ≠ 0) (hsp : Submodule.span O {e₀} = ⊤) :
    ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  have := T.L.free
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    refine ⟨smul_left_injective O h0, ?_⟩
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hsp]
  let e := LinearEquiv.ofBijective _ hb
  have he : e 1 = e₀ := one_smul O e₀
  refine ⟨(LinearMap.pi fun _ => Algebra.linearMap O k).comp e.symm.toLinearMap, ⟨?_, fun g x => ?_⟩, ?_⟩
  · intro y
    obtain ⟨c, hc⟩ := hs (y 0)
    refine ⟨e c, funext fun i => ?_⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change algebraMap O k (e.symm (e c)) = y 0
    rw [e.symm_apply_apply, hc]
  · have h1 : latRep T.L g x = x := Subtype.ext (hρ g x)
    rw [h1]
    exact (one_smul k _).symm
  · funext i
    change algebraMap O k (e.symm e₀) = 1
    rw [← he, e.symm_apply_apply, map_one]

theorem lattice_quotients : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 → lam ∣ x) → (∀ (A B : Ob k G) f, IsHom A B f → Function.Injective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) ∧ (∀ (A B : Ob k G) f, IsHom A B f → Function.Surjective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) ∧ (∀ (A B C : Ob k G) i j, IsHom A C i → IsHom B C j → Function.Surjective (i.coprod j) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin C.m → k)), Onto T C q) ∧ ∀ (T : LocLat G Qp LL O) (e₀ : ↥T.L.T), (∀ g x, T.ρ g x = x) → e₀ ≠ 0 → Submodule.span O {e₀} = ⊤ → ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  intro G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk hs _
  refine ⟨?_, ?_, ?_, onto_one hs⟩
  · rintro A B f hf hi ⟨T, q, hq⟩
    exact onto_sub lam hl hk A B f hf hi T q hq
  · rintro A B f hf hi ⟨T, q, hq⟩
    exact ⟨T, _, onto_quot A B f hf hi T q hq⟩
  · rintro A B C i j hi hj h ⟨T, q, hq⟩ ⟨T', q', hq'⟩
    exact ⟨_, _, onto_sum A B C i j hi hj h T q hq T' q' hq'⟩

end GlobalTheory.RedFun.LatQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientsClosedSubQuotSumStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeQuotients_closed_sub_quot_sum : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 → lam ∣ x) → (∀ (A B : Ob k G) f, IsHom A B f → Function.Injective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) ∧ (∀ (A B : Ob k G) f, IsHom A B f → Function.Surjective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) ∧ (∀ (A B C : Ob k G) i j, IsHom A C i → IsHom B C j → Function.Surjective (i.coprod j) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin C.m → k)), Onto T C q) ∧ ∀ (T : LocLat G Qp LL O) (e₀ : ↥T.L.T), (∀ g x, T.ρ g x = x) → e₀ ≠ 0 → Submodule.span O {e₀} = ⊤ → ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  first | exact @GlobalTheory.RedFun.LatQuot.lattice_quotients | exact GlobalTheory.RedFun.LatQuot.lattice_quotients | (intros; apply GlobalTheory.RedFun.LatQuot.lattice_quotients <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicIntegersEqWittZetaSubOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicIntegersEqWittZetaSubOne
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS Polynomial
open scoped IntermediateField

namespace GlobalTheory.PrismS.Poly

variable {l : ℕ} [Fact l.Prime]

theorem mem_OL_of_norm_le (K : FinExt l) (y : ↥K.1) (h : ‖(y : Om l)‖ ≤ 1) : y ∈ OL K := by
  have hi : IsIntegral ℚ_[l] (y : Om l) := Algebra.IsIntegral.isIntegral _
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  have h1 : IsIntegral ℤ_[l] (y : Om l) := ⟨q, hm, by
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
  exact (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1

theorem norm_coeff_le (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X])
    (hd : p.natDegree < N) (h1 : ‖aeval π p‖ ≤ 1) (j : ℕ) :
    ‖((p.coeff j : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have key : ∀ i ∈ p.support, ∃ n : ℤ, ‖((p.coeff i : ↥(K0 K)) : Om l)‖ = (l : ℝ) ^ n ∧
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, hn, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, -, hn⟩ := key i hi
    obtain ⟨m, -, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  by_cases hj : j ∈ p.support
  swap
  · rw [notMem_support_iff.1 hj]; simp
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  have h7 := Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hj
  rw [← h6] at h7
  obtain ⟨n, hn, hn'⟩ := key _ hj
  have h8 : ‖p.coeff j • π ^ j‖ ≤ ‖aeval π p‖ := h7
  replace h8 := (h8.trans h1).trans (Real.rpow_zero (l : ℝ)).ge
  rw [hn', Real.rpow_le_rpow_left_iff hl1] at h8
  have hj' : (j : ℝ) < N := by exact_mod_cast (le_natDegree_of_mem_supp j hj).trans_lt hd
  have h9 : (j : ℝ) / N < 1 := (div_lt_one hN).2 hj'
  have h10 : n < 1 := by
    have : (n : ℝ) < 1 := by linarith
    exact_mod_cast this
  rw [hn]
  exact zpow_le_one_of_nonpos₀ hl1.le (by omega)

theorem coe_eval₂ (K : FinExt l) (π : Om l) (t : OC l) (ht : (t : ℂ_[l]) = (π : ℂ_[l]))
    (r : (WK K)[X]) : ((r.eval₂ (intToOC (unr K)) t : OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (aeval π (r.map ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)))) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), ← hp, ← hq]; rfl
  | monomial n a =>
    rw [eval₂_monomial, Polynomial.map_monomial, aeval_monomial, map_mul, map_pow]
    push_cast
    rw [ht]
    rfl

theorem exists_poly (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ s))
    (x : Om l) (hx : x ∈ Ks K s) :
    ∃ p : (↥(K0 K))[X], p.natDegree < l ^ (s - 1) * (l - 1) ∧ aeval (ζ - 1) p = x := by
  have hlp : l.Prime := Fact.out
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [GlobalTheory.Cyc.Ks_eq_restrictScalars K s ζ hζ] at hx
  have hx' : x ∈ ((↥(K0 K))⟮ζ⟯).toSubalgebra := hx
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, rfl⟩ := hx'
  refine ⟨taylor 1 (q %ₘ minpoly ↥(K0 K) ζ), ?_, ?_⟩
  · rw [natDegree_taylor, ← Nat.totient_prime_pow hlp hs,
      ← natDegree_cyclotomic (l ^ s) ↥(K0 K), ← GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs ζ hζ]
    exact natDegree_modByMonic_lt _ (minpoly.monic hint) (minpoly.ne_one _ _)
  · rw [taylor_apply, aeval_comp]
    simp only [map_add (f := _), aeval_X, aeval_C, map_one, sub_add_cancel]
    exact aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), 1 ≤ s → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ s) → ∀ t : OC l, (t : ℂ_[l]) = ((ζ - 1 : Om l) : ℂ_[l]) → (∀ r : Polynomial (WK K), r.natDegree < l ^ (s - 1) * (l - 1) → r.eval₂ (intToOC (unr K)) t = 0 → r = 0) ∧ (K.1 ≤ Ks K s → ∀ x : ↥(OL K), ∃ r : Polynomial (WK K), r.eval₂ (intToOC (unr K)) t = intToOC K x) := by
  intro l _ K s hs ζ hζ t ht
  have hlp : l.Prime := Fact.out
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l ^ (s - 1) * (l - 1) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l s hs (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  have hinj : Function.Injective ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)) :=
    Subtype.val_injective
  refine ⟨fun r hr h0 => ?_, fun hK x => ?_⟩
  · by_contra hne
    have h1 := coe_eval₂ K (ζ - 1) t ht r
    rw [h0] at h1
    refine GlobalTheory.Cyc.aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm _
      ((Polynomial.map_ne_zero_iff hinj).2 hne) (natDegree_map_le.trans_lt hr) ?_
    exact (algebraMap (Om l) ℂ_[l]).injective (h1.symm.trans (map_zero _).symm)
  · obtain ⟨p, hp, hpx⟩ := exists_poly K s hs ζ hζ _ (hK (x : ↥K.1).2)
    have hc := norm_coeff_le K _ _ hnorm p hp (hpx ▸ norm_le_one_of_mem_OL K x)
    have hl : p ∈ Polynomial.lifts ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)) := by
      rw [lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, mem_OL_of_norm_le (unr K) _ (hc n)⟩, rfl⟩
    obtain ⟨r, rfl⟩ := (mem_lifts _).1 hl
    refine ⟨r, Subtype.ext ?_⟩
    rw [coe_eval₂ K (ζ - 1) t ht r, hpx]
    rfl

end GlobalTheory.PrismS.Poly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicIntegersEqWittZetaSubOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_integers_eq_witt_zeta_sub_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), 1 ≤ s → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ s) → ∀ t : OC l, (t : ℂ_[l]) = ((ζ - 1 : Om l) : ℂ_[l]) → (∀ r : Polynomial (WK K), r.natDegree < l ^ (s - 1) * (l - 1) → r.eval₂ (intToOC (unr K)) t = 0 → r = 0) ∧ (K.1 ≤ Ks K s → ∀ x : ↥(OL K), ∃ r : Polynomial (WK K), r.eval₂ (intToOC (unr K)) t = intToOC K x) := by
  first | exact @GlobalTheory.PrismS.Poly.main | exact GlobalTheory.PrismS.Poly.main | (intros; apply GlobalTheory.PrismS.Poly.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelInverseFibreProductLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelInverseFibreProductLattices
noncomputable section

namespace GlobalTheory.RedFun.SubLat

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.TopSteps.StdAdm
open scoped LaurentSeries PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL]

def subLattice [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O) {lam : O}
    (hl : algebraMap O LL lam ≠ 0) (P : Submodule O ↥T.L.T) (hg : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P)
    (hP : ∀ x, lam • x ∈ P) : Lattice (O := O) T.ρ where
  T := P.map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨latRep T.L g x, hg g x hx, rfl⟩
  fg := by
    have := finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := finite_lat T
    have := T.L.free
    have : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have h1 : lam • y ∈ P.map T.L.T.subtype := ⟨lam • ⟨y, hy⟩, hP _, rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL lam)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← algebraMap_smul LL lam y, inv_smul_smul₀ hl] at h2

variable {k : Type} [Field k] [Algebra O k]


omit [Algebra O LL] in
theorem lam_smul {lam : O} (hk : algebraMap O k lam = 0) {m : ℕ} (t : Fin m → k) : lam • t = 0 := by
  ext i
  simp [Algebra.smul_def, hk]

theorem exists_ker [IsDomain O] [IsPrincipalIdealRing O] {lam : O} (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (hq : Onto T A q) : ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L),
      ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x := by
  have hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x) := hq.2
  have hP : ∀ x, lam • x ∈ LinearMap.ker q := fun x => by
    rw [LinearMap.mem_ker, map_smul, lam_smul hk]
  have hg : ∀ σ, ∀ x ∈ LinearMap.ker q, latRep T.L σ x ∈ LinearMap.ker q := fun σ x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hq2, hx, map_zero]
  refine ⟨{ T with L := subLattice T hl (LinearMap.ker q) hg hP },
    ⟨LinearMap.id, fun _ _ => rfl, continuous_id, ?_⟩, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro x
    constructor
    · intro hx
      exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
      have hzx : z = x := Subtype.ext h
      subst hzx
      exact hz

theorem exists_inv {lam : O} (hl : algebraMap O LL lam ≠ 0) (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L)
    (hf : Function.Injective f.f) (h : ∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) :
    ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x := by
  have hsurj : Function.Surjective f.f := by
    have hle : Submodule.span LL (T.L.T : Set T.V) ≤ LinearMap.range f.f := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, -, hy⟩ := h x hx
      refine ⟨(algebraMap O LL lam)⁻¹ • y, ?_⟩
      rw [map_smul, hy, ← algebraMap_smul LL lam x, inv_smul_smul₀ hl]
    rw [T.L.span] at hle
    exact fun x => hle Submodule.mem_top
  let e := LinearEquiv.ofBijective f.f ⟨hf, hsurj⟩
  have h1 : ∀ z, f.f (e.symm z) = z := fun z => e.apply_symm_apply z
  let c := algebraMap O LL lam
  refine ⟨⟨c • (e.symm : T.V →ₗ[LL] T'.V), ?_, IsModuleTopology.continuous_of_linearMap _, ?_⟩, ?_⟩
  · intro σ x
    apply hf
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, f.equiv, h1]
  · intro x hx
    obtain ⟨y, hy, hfy⟩ := h x hx
    have hxy : (c • (e.symm : T.V →ₗ[LL] T'.V)) x = y := by
      apply hf
      rw [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1, hfy, algebraMap_smul]
    rw [hxy]
    exact hy
  · intro x
    show f.f ((c • (e.symm : T.V →ₗ[LL] T'.V)) x) = c • x
    rw [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1]

theorem exists_fibre [IsDomain O] [IsPrincipalIdealRing O] {lam : O} (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k))
    (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)) (hq : Onto T A q) (hq' : Onto T' A' q') (hg : IsHom A A' g) :
    ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L),
      (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧
      ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  have hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x) := hq.2
  have hq2' : ∀ σ x, q' (latRep T'.L σ x) = A'.ρ σ (q' x) := hq'.2
  have hg0 : ∀ σ x, g (A.ρ σ x) = A'.ρ σ (g x) := hg
  let φ : ↥(prodLat T T').L.T →ₗ[O] (Fin A'.m → k) :=
    q' ∘ₗ (LinearMap.snd O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap) -
      (g.restrictScalars O) ∘ₗ q ∘ₗ (LinearMap.fst O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap)
  have hφ : ∀ z, φ z = q' (prodLatEquiv T T' z).2 - g (q (prodLatEquiv T T' z).1) := fun z => rfl
  have hP : ∀ z, lam • z ∈ LinearMap.ker φ := fun z => by
    rw [LinearMap.mem_ker, map_smul, lam_smul hk]
  have hst : ∀ σ, ∀ z ∈ LinearMap.ker φ, latRep (prodLat T T').L σ z ∈ LinearMap.ker φ := by
    intro σ z hz
    rw [LinearMap.mem_ker, hφ] at hz ⊢
    simp only [prodLatEquiv_act]
    rw [hq2, hq2', hg0, ← map_sub, hz, map_zero]
  refine ⟨{ prodLat T T' with L := subLattice (prodLat T T') hl (LinearMap.ker φ) hst hP },
    ⟨LinearMap.fst LL T.V T'.V, fun _ _ => rfl, continuous_fst, ?_⟩,
    ⟨LinearMap.snd LL T.V T'.V, fun _ _ => rfl, continuous_snd, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2.1
  · rintro _ ⟨z, -, rfl⟩
    exact z.2.2
  · intro x hx
    obtain ⟨x', hx'⟩ := hq'.1 (g (q ⟨x, hx⟩))
    let w : ↥(prodLat T T').L.T := ⟨(x, (x' : T'.V)), hx, x'.2⟩
    refine ⟨(x, (x' : T'.V)), ⟨w, ?_, rfl⟩, rfl⟩
    show φ w = 0
    rw [hφ]
    exact sub_eq_zero.mpr hx'
  · rintro ⟨_, ⟨w, hw, rfl⟩⟩
    have hw' : φ w = 0 := hw
    rw [hφ, sub_eq_zero] at hw'
    exact hw'

theorem ker_inv_fibre : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → (∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) ∧ (∀ (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f → (∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) → ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x) ∧ ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k)) (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), Onto T A q → Onto T' A' q' → IsHom A A' g → ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L), (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧ ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  intro G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk
  exact ⟨fun T A q hq => exists_ker hl hk T A q hq, fun T T' f hf h => exists_inv hl T T' f hf h,
    fun T A q T' A' q' g hq hq' hg => exists_fibre hl hk T A q T' A' q' g hq hq' hg⟩

end GlobalTheory.RedFun.SubLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelInverseFibreProductLatticesStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_inverse_fibreProduct_lattices : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → (∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) ∧ (∀ (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f → (∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) → ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x) ∧ ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k)) (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), Onto T A q → Onto T' A' q' → IsHom A A' g → ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L), (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧ ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  first | exact @GlobalTheory.RedFun.SubLat.ker_inv_fibre | exact GlobalTheory.RedFun.SubLat.ker_inv_fibre | (intros; apply GlobalTheory.RedFun.SubLat.ker_inv_fibre <;> assumption)
end
end
