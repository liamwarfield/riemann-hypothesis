module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def blockB (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.fst ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

def blockD (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.snd ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

theorem blockB_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockB J q = (J (0, q)).1 := rfl

theorem blockD_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockD J q = (J (0, q)).2 := rfl

def fockForm (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ))
    (fun x x' y => by simp only [map_add (f := _), LinearMap.add_apply]; push_cast; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.real_smul]; push_cast; ring)
    (fun x y y' => by simp only [map_add (f := _)]; push_cast; ring)
    (fun c x y => by simp only [map_smul, smul_eq_mul, Complex.real_smul]; push_cast; ring)

theorem fockForm_apply (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (x y : V) :
    fockForm β J x y = ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ) := rfl

end GlobalTheory.FockFamily

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffProdLinearMapUpperRightLowerRightBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffProdLinearMapUpperRightLowerRightBlocks
open MeasureTheory

namespace GlobalTheory.FockFamily

theorem contDiff_blockB_blockD {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) (hJ : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  constructor
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockB_apply] using (hJ (0, q)).fst
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockD_apply] using (hJ (0, q)).snd

end GlobalTheory.FockFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffProdLinearMapUpperRightLowerRightBlocksStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  first | exact @GlobalTheory.FockFamily.contDiff_blockB_blockD | exact GlobalTheory.FockFamily.contDiff_blockB_blockD | (intros; apply GlobalTheory.FockFamily.contDiff_blockB_blockD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNeg
open MeasureTheory

namespace GlobalTheory

theorem schwartz_gaussian_form_re_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ) (hg : g ≠ 0)
    (hform : ∀ x, g x = g 0 * Complex.exp (M x x)) (v : V) (hv : v ≠ 0) : (M v v).re < 0 := by
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    ext x
    rw [hform x, h0]; simp
  by_contra hre
  push_neg at hre
  obtain ⟨C, hC, hdec⟩ := g.decay 1 0
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set s : ℝ := (C + 1) / (‖v‖ * ‖g 0‖) with hs
  have hspos : 0 < s := by positivity
  have key := hdec (s • v)
  rw [norm_iteratedFDeriv_zero, pow_one, hform (s • v)] at key
  have hM : M (s • v) (s • v) = ((s ^ 2 : ℝ) : ℂ) * M v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Complex.real_smul]; push_cast; ring
  rw [hM, norm_mul, Complex.norm_exp] at key
  have hexp : 1 ≤ Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re) := by
    apply Real.one_le_exp
    rw [Complex.re_ofReal_mul]
    positivity
  have hnorm : ‖s • v‖ = s * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  rw [hnorm] at key
  have h1 : s * ‖v‖ * ‖g 0‖ = C + 1 := by
    rw [hs]; field_simp
  have h2 : s * ‖v‖ * ‖g 0‖ ≤ s * ‖v‖ * (‖g 0‖ * Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNegStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_form_re_neg_of_ne_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ x, g x = g 0 * Complex.exp (M x x)) → ∀ v, v ≠ 0 → (M v v).re < 0 := by
  first | exact @GlobalTheory.schwartz_gaussian_form_re_neg | exact GlobalTheory.schwartz_gaussian_form_re_neg | (intros; apply GlobalTheory.schwartz_gaussian_form_re_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtDiagSumProdPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtDiagSumProdPairing
open MeasureTheory

namespace GlobalTheory

theorem hasDerivAt_diag_sum_prod_pairing
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hM : ∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) :
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  classical
  set d := Module.finrank ℝ V
  let e : Module.Basis (Fin d) ℝ V := Module.finBasis ℝ V

  have hinj : Function.Injective β.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    exact hβ q (fun x => by simpa using LinearMap.congr_fun hq x)
  have hsurj : Function.Surjective β.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  choose q hq using fun i : Fin d => hsurj (e.coord i)
  have hqx : ∀ x i, β x (q i) = e.repr x i := by
    intro x i
    have := LinearMap.congr_fun (hq i) x
    simpa using this

  have hexp : ∀ x t, M t x x =
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := by
    intro x t
    conv_lhs => rw [← e.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum,
      Complex.real_smul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  let c : Fin d × Fin d → ℂ := fun p => deriv (fun t => M t (e p.1) (e p.2)) 0
  refine ⟨d * d, fun k => q (finProdFinEquiv.symm k).1, fun k => q (finProdFinEquiv.symm k).2,
    fun k => c (finProdFinEquiv.symm k), fun x => ?_⟩
  have hfun : (fun t => M t x x) = fun t =>
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := funext (hexp x)
  rw [hfun]
  have hd : HasDerivAt (fun t => ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j))
      (∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * c (i, j)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hM (e i) (e j)).hasDerivAt).const_mul _
  convert hd using 1
  simp only [hqx]
  rw [← Fintype.sum_prod_type']
  rw [← (finProdFinEquiv (m := d) (n := d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtDiagSumProdPairingStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) →
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.hasDerivAt_diag_sum_prod_pairing | exact GlobalTheory.hasDerivAt_diag_sum_prod_pairing | (intros; apply GlobalTheory.hasDerivAt_diag_sum_prod_pairing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffFockGaussianFormOfLinearMapFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffFockGaussianFormOfLinearMapFamily
open MeasureTheory

namespace GlobalTheory.FockFamily

theorem fockForm_family_contDiff {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) →
    (∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t))) →
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.FockFamily.fockForm β (J t) x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => GlobalTheory.FockFamily.fockForm β (J p.1) p.2 p.2) := by
  intro hB hD hU

  let β₁ : V →ₗ[ℝ] (V →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ β
  let βc : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap β₁
  have hβc : ∀ x y, βc x y = β x y := fun x y => rfl

  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Ring.inverse (blockB (J t))) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (contDiffAt_ringInverse ℝ (hU t).unit).comp t hB.contDiffAt
  have hDC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => (blockD (J t)).comp (Ring.inverse (blockB (J t)))) := hD.clm_comp hC
  have hπ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ × V => (Real.pi : ℂ) * Complex.I) := contDiff_const
  have hπ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (Real.pi : ℂ) * Complex.I) := contDiff_const
  have hR : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ},
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun e => ((f e : ℝ) : ℂ)) :=
    fun hf => Complex.ofRealCLM.contDiff.comp hf
  constructor
  · intro x y
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => Real.pi * βc x (Ring.inverse (blockB (J t)) y)) :=
      contDiff_const.mul (contDiff_const.clm_apply (hC.clm_apply contDiff_const))
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => βc x (((blockD (J t)).comp (Ring.inverse (blockB (J t)))) y)) :=
      contDiff_const.clm_apply (hDC.clm_apply contDiff_const)
    have := (hR h1).add (hπ'.mul (hR h2))
    simpa only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply] using this
  · have hCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => Ring.inverse (blockB (J p.1)) p.2) :=
      (hC.comp contDiff_fst).clm_apply contDiff_snd
    have hDCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => ((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2) :=
      (hDC.comp contDiff_fst).clm_apply contDiff_snd
    have hβp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => βc p.2) :=
      βc.contDiff.comp contDiff_snd
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => Real.pi * βc p.2 (Ring.inverse (blockB (J p.1)) p.2)) :=
      contDiff_const.mul (hβp.clm_apply hCp)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => βc p.2 (((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2)) :=
      hβp.clm_apply hDCp
    have := (hR h1).add (hπ.mul (hR h2))
    simpa only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply] using this

end GlobalTheory.FockFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffFockGaussianFormOfLinearMapFamilyStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_fockGaussianFormOfLinearMap_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) →
    (∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t))) →
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.FockFamily.fockForm β (J t) x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => GlobalTheory.FockFamily.fockForm β (J p.1) p.2 p.2) := by
  first | exact @GlobalTheory.FockFamily.fockForm_family_contDiff | exact GlobalTheory.FockFamily.fockForm_family_contDiff | (intros; apply GlobalTheory.FockFamily.fockForm_family_contDiff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UniformlyNegDefiniteNearOfContinuousQuadFormFami
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UniformlyNegDefiniteNearOfContinuousQuadFormFami
open MeasureTheory

namespace GlobalTheory

theorem quadForm_eventually_unif_negDef {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hc : Continuous (fun p : ℝ × V => M p.1 p.2 p.2))
    (hneg : ∀ t v, v ≠ 0 → (M t v v).re < 0) (t₀ : ℝ) :
    ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
  have hF : Continuous (fun p : ℝ × V => (M p.1 p.2 p.2).re) := Complex.continuous_re.comp hc
  have hscale : ∀ t (c : ℝ) (u : V), (M t (c • u) (c • u)).re = c ^ 2 * (M t u u).re := by
    intro t c u
    simp only [map_smul, LinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
    ring
  have key : ∀ (ε : ℝ) (t : ℝ), (∀ u ∈ Metric.sphere (0:V) 1, (M t u u).re < -ε) →
      ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
    intro ε t ht x
    by_cases hx : x = 0
    · subst hx; simp
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0:V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have h1 := ht _ hu
      have hx' : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      have h2 : (M t x x).re = ‖x‖ ^ 2 * (M t (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := by
        conv_lhs => rw [hx']
        exact hscale t _ _
      rw [h2]
      have hp : 0 ≤ ‖x‖ ^ 2 := by positivity
      nlinarith
  have hS : IsCompact (Metric.sphere (0:V) 1) := isCompact_sphere 0 1
  rcases (Metric.sphere (0:V) 1).eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, Filter.Eventually.of_forall fun t => key 1 t ?_⟩
    intro u hu
    rw [hE] at hu
    exact absurd hu (Set.notMem_empty _)
  · have hcont0 : ContinuousOn (fun u : V => (M t₀ u u).re) (Metric.sphere 0 1) :=
      (hF.comp (Continuous.prodMk_right t₀)).continuousOn
    obtain ⟨u₀, hu₀, hmax⟩ := hS.exists_isMaxOn hNE hcont0
    have hu₀0 : u₀ ≠ 0 := by
      rintro rfl
      simp at hu₀
    have hm : (M t₀ u₀ u₀).re < 0 := hneg t₀ u₀ hu₀0
    refine ⟨-(M t₀ u₀ u₀).re / 2, by linarith, ?_⟩
    have hev : ∀ᶠ t in nhds t₀, ∀ u ∈ Metric.sphere (0:V) 1,
        (M t u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
      apply hS.eventually_forall_of_forall_eventually
      intro u hu
      have hlt : (M t₀ u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
        have := hmax hu
        simp only [Set.mem_setOf_eq] at this
        linarith
      exact hF.continuousAt.eventually_lt continuousAt_const hlt
    exact hev.mono fun t ht => key _ t ht

theorem quadForm_unif_target : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    Continuous (fun p : ℝ × V => M p.1 p.2 p.2) → (∀ t v, v ≠ 0 → (M t v v).re < 0) →
    ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) :=
  fun M hc hneg t₀ => quadForm_eventually_unif_negDef M hc hneg t₀

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UniformlyNegDefiniteNearOfContinuousQuadFormFamiStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformly_negDefinite_near_of_continuous_quadForm_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    Continuous (fun p : ℝ × V => M p.1 p.2 p.2) → (∀ t v, v ≠ 0 → (M t v v).re < 0) →
    ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
  first | exact @GlobalTheory.quadForm_unif_target | exact GlobalTheory.quadForm_unif_target | (intros; apply GlobalTheory.quadForm_unif_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEq
open MeasureTheory

noncomputable section

namespace GlobalTheory.FockFamily

theorem fderiv_eq_of_dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (hB : IsUnit (blockB J)) (g : V → ℂ)
    (heq : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) (x y : V) :
    fderiv ℝ g x y = 2 * fockForm β J x y * g x := by
  have h := heq (0, Ring.inverse (blockB J) y) x
  have h1 : (J (0, Ring.inverse (blockB J) y)).1 = y := by
    rw [← blockB_apply, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hB]; rfl
  have h2 : (J (0, Ring.inverse (blockB J) y)).2 = blockD J (Ring.inverse (blockB J) y) := rfl
  simp only [GlobalTheory.GaussLine.dHeis, h1, h2, map_zero, zero_sub] at h
  rw [fockForm_apply]
  push_cast
  linear_combination h - 2 * Real.pi * (β x (Ring.inverse (blockB J) y) : ℂ) * g x * Complex.I_sq

theorem solution_eq_gauss {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (hB : IsUnit (blockB J)) (g : V → ℂ)
    (hg : Differentiable ℝ g)
    (heq : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) (x : V) :
    g x = g 0 * Complex.exp (fockForm β J x x) := by
  set c : ℂ := fockForm β J x x with hc
  let h : ℝ → ℂ := fun s => g (s • x) * Complex.exp (-(((s ^ 2 : ℝ)) : ℂ) * c)
  have hd : ∀ s : ℝ, HasDerivAt h 0 s := by
    intro s
    have e1 : HasDerivAt (fun t : ℝ => g (t • x)) (fderiv ℝ g (s • x) x) s := by
      have := (hg (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
      simp only [one_smul] at this
      exact this
    have e2 : HasDerivAt (fun t : ℝ => Complex.exp (-(((t ^ 2 : ℝ)) : ℂ) * c))
        (Complex.exp (-(((s ^ 2 : ℝ)) : ℂ) * c) * (-((((2 : ℕ) : ℝ) * s ^ (2 - 1) * 1 : ℝ) : ℂ) * c)) s := by
      exact ((((hasDerivAt_id s).pow 2).ofReal_comp).neg.mul_const c).cexp
    have hf : fderiv ℝ g (s • x) x = 2 * ((s : ℂ) * c) * g (s • x) := by
      rw [fderiv_eq_of_dHeis β J hB g heq, map_smul, LinearMap.smul_apply, Complex.real_smul]
    show HasDerivAt (fun t : ℝ => g (t • x) * Complex.exp (-(((t ^ 2 : ℝ)) : ℂ) * c)) 0 s
    refine (e1.mul e2).congr_deriv ?_
    rw [hf]
    push_cast
    ring
  have hconst : ∀ a b : ℝ, h a = h b := fun a b =>
    is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) a b
  have := hconst 1 0
  simp only [h, one_smul, zero_smul, one_pow, Complex.ofReal_one, neg_mul, one_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.FockFamily

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEqStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), IsUnit (GlobalTheory.FockFamily.blockB J) → ∀ g : V → ℂ, Differentiable ℝ g →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β J x x) := by
  first | exact @GlobalTheory.FockFamily.solution_eq_gauss | exact GlobalTheory.FockFamily.solution_eq_gauss | (intros; apply GlobalTheory.FockFamily.solution_eq_gauss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitUpperRightBlockOfHeisenbergDerivativeSolut
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitUpperRightBlockOfHeisenbergDerivativeSolut
open MeasureTheory

noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem isUnit_of_injective_clm (B : V →L[ℝ] V) (h : Function.Injective B) : IsUnit B := by
  have hs : Function.Surjective (B : V →ₗ[ℝ] V) := LinearMap.injective_iff_surjective.mp h
  let e : V ≃ₗ[ℝ] V := LinearEquiv.ofBijective (B : V →ₗ[ℝ] V) ⟨h, hs⟩
  let e' : V ≃L[ℝ] V := e.toContinuousLinearEquiv
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ V).symm e', ?_⟩
  ext x; rfl

theorem dense_pair_ne_zero (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q x₀ : V) (hx : β x₀ q ≠ 0) :
    Dense {x | β x q ≠ 0} := by
  have hint : interior ((LinearMap.ker (β.flip q) : Submodule ℝ V) : Set V) = ∅ := by
    by_contra hne
    have := Submodule.eq_top_of_nonempty_interior' _ (Set.nonempty_iff_ne_empty.mpr hne)
    apply hx
    have : x₀ ∈ LinearMap.ker (β.flip q) := by rw [this]; trivial
    simpa using this
  have := interior_eq_empty_iff_dense_compl.mp hint
  convert this using 1
  ext x; simp

theorem isUnit_blockB_of_solution (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (J : (V × V) →ₗ[ℝ] (V × V)) (g : V → ℂ) (hg : Continuous g) (hg0 : g ≠ 0)
    (hJ : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) :
    IsUnit (blockB J) := by
  apply isUnit_of_injective_clm
  refine (injective_iff_map_eq_zero (blockB J)).mpr ?_
  intro q hq
  apply hβ q
  by_contra hne
  push_neg at hne
  obtain ⟨x₀, hx₀⟩ := hne
  have hzero : ∀ x, β x q ≠ 0 → g x = 0 := by
    intro x hx
    have h := hJ (0, q) x
    have h1 : (J (0, q)).1 = 0 := by rw [← blockB_apply]; exact hq
    simp only [GlobalTheory.GaussLine.dHeis, h1, map_zero] at h
    have key : (((β x q : ℝ) : ℂ) + Complex.I * ((β x (J (0, q)).2 : ℝ) : ℂ)) * g x = 0 := by
      have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      have h2 : (2 * Real.pi : ℂ) * ((((β x q : ℝ) : ℂ) + Complex.I * ((β x (J (0, q)).2 : ℝ) : ℂ)) * g x) = 0 := by
        linear_combination (-1 : ℂ) * h + (2 * Real.pi * ((β x q : ℝ) : ℂ) * g x) * Complex.I_sq
      exact (mul_eq_zero.mp h2).resolve_left hpi
    rcases mul_eq_zero.mp key with h3 | h3
    · exfalso; apply hx
      have := congrArg Complex.re h3
      simpa using this
    · exact h3
  apply hg0
  have hd := dense_pair_ne_zero β q x₀ hx₀
  exact Continuous.ext_on hd hg continuous_const (fun x hx => hzero x hx)
end GlobalTheory.FockFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitUpperRightBlockOfHeisenbergDerivativeSolutStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_upperRightBlock_of_heisenbergDerivative_solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ (J : (V × V) →ₗ[ℝ] (V × V)) (g : V → ℂ), Continuous g → g ≠ 0 →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    IsUnit (GlobalTheory.FockFamily.blockB J) := by
  first | exact @GlobalTheory.FockFamily.isUnit_blockB_of_solution | exact GlobalTheory.FockFamily.isUnit_blockB_of_solution | (intros; apply GlobalTheory.FockFamily.isUnit_blockB_of_solution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussians
open MeasureTheory

namespace GlobalTheory.FockFamily

theorem fock_vacua_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  intro V _ _ _ β hβ J hJ _ hex
  choose g0 hg0ne hg0 using hex
  have hunit : ∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t)) := fun t =>
    GlobalTheory.T.isUnit_upperRightBlock_of_heisenbergDerivative_solution β hβ (J t) (g0 t) (g0 t).continuous (fun h => hg0ne t (SchwartzMap.ext (fun x => congrFun h x))) (hg0 t)
  obtain ⟨hB, hD⟩ := GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks J hJ
  obtain ⟨hsm, hjoint⟩ := GlobalTheory.T.contDiff_fockGaussianFormOfLinearMap_family β J hB hD hunit
  have hray : ∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) → ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β (J t) x x) :=
    fun t g hg => GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq β (J t) (hunit t) g g.differentiable hg
  refine ⟨fun t => GlobalTheory.FockFamily.fockForm β (J t), hsm, hjoint, ?_, hray, ?_⟩
  · exact GlobalTheory.T.uniformly_negDefinite_near_of_continuous_quadForm_family (fun t => GlobalTheory.FockFamily.fockForm β (J t)) hjoint.continuous
      (fun t v hv => GlobalTheory.T.gaussian_form_re_neg_of_ne_zero _ (g0 t) (hg0ne t) (hray t (g0 t) (hg0 t)) v hv)
  · exact GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings β hβ _ (fun x y => ((hsm x y).differentiable (by simp)).differentiableAt)

end GlobalTheory.FockFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussiansStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_smooth_family_complexGaussians : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.FockFamily.fock_vacua_family | exact GlobalTheory.FockFamily.fock_vacua_family | (intros; apply GlobalTheory.FockFamily.fock_vacua_family <;> assumption)
end
