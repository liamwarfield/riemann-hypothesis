module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRadAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPairDone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE_TopSpec

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpecAsm
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSFund
open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Fund

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]

theorem rds_zeta_compact (D : B.RealPlaceData k r Wp Wq) {Kz : Set ℂ} (hKz : IsCompact Kz)
    (hKzA : Kz ⊆ JCx2.rbO (Tz k r D.z) (Tz k r D.z')) :
    ∃ K' : Set (Mx k r), IsCompact K' ∧ K' ⊆ Qx5.Dp k r D.z D.z' ∧
      ∀ g ∈ Glev k r (Fin.last r), 0 < GGl k r D.z D.z' g → zetaL k r D.z D.z' (Fin.last r) g ∈ Kz → g ∈ K' := by
  have hmem := Formalism.FourierDecayAlt.P.b2_rank_one_mem k r D.z D.z' D.μsec D.z_mem D.z'_mem D.sec
  let SW : Set (Mt k r) := {x | (Matrix.of x : Mx k r) ∈ UWset k r D.z}
  let SW' : Set (Mt k r) := {x | (Matrix.of x : Mx k r) ∈ UWset k r D.z'}
  let F : ℂ × (Mt k r × Mt k r) → Mt k r := fun p =>
    JCx2.rbMul (JCx2.rbMul (p.2.1, JCx2.rbEf k r D.μsec p.1), p.2.2)
  have hF : ∀ p : ℂ × (Mt k r × Mt k r),
      (Matrix.of (F p) : Mx k r) = Matrix.of p.2.1 * NF.muZ k r D.μsec p.1 * Matrix.of p.2.2 := fun p => rfl
  have hSW : IsCompact SW := Formalism.FourierDecayAlt.P.B2x3.compactW k r D.z D.z_mem D.T_pos
  have hSW' : IsCompact SW' := Formalism.FourierDecayAlt.P.B2x3.compactW k r D.z' D.z'_mem D.T'_pos
  have hS : IsCompact (Kz ×ˢ (SW ×ˢ SW')) := hKz.prod (hSW.prod hSW')
  have hEc : ContinuousOn (JCx2.rbEf k r D.μsec) (JCx2.rbO (Tz k r D.z) (Tz k r D.z')) :=
    JCx2.rb_contOn_E fun i j => (D.sec.1 i j).continuousOn
  have hFc : ContinuousOn F (Kz ×ˢ (SW ×ˢ SW')) := by
    have hA : ContinuousOn (fun p : ℂ × (Mt k r × Mt k r) =>
        (p.2.1, JCx2.rbEf k r D.μsec p.1)) (Kz ×ˢ (SW ×ˢ SW')) :=
      (continuous_fst.comp continuous_snd).continuousOn.prodMk
        (hEc.comp continuousOn_fst fun p hp => hKzA hp.1)
    have hB : ContinuousOn (fun p : ℂ × (Mt k r × Mt k r) =>
        (JCx2.rbMul (p.2.1, JCx2.rbEf k r D.μsec p.1), p.2.2)) (Kz ×ˢ (SW ×ˢ SW')) :=
      (Formalism.FourierDecayAlt.P.B7.continuous_mulM.comp_continuousOn hA).prodMk
        (continuous_snd.comp continuous_snd).continuousOn
    exact Formalism.FourierDecayAlt.P.B7.continuous_mulM.comp_continuousOn hB
  refine ⟨F '' (Kz ×ˢ (SW ×ˢ SW')), hS.image_of_continuousOn hFc, ?_, ?_⟩
  · rintro g ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩
    have hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq p.1 := hKzA hp1
    obtain ⟨-, hherm⟩ := hmem p.1 hζ ((Matrix.of p.2.1 : Mx k r)⁻¹) (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp2)
      (Matrix.of p.2.2) hp3
    have hinvinv : ((Matrix.of p.2.1 : Mx k r)⁻¹)⁻¹ = Matrix.of p.2.1 :=
      Matrix.inv_eq_right_inv (Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hp2)
    rw [hinvinv] at hherm
    show 0 < GGl k r D.z D.z' (Matrix.of (F p))
    rw [hF]
    unfold GGl
    rw [P5.Rad.zetaL_last]
    erw [hherm]
    exact sub_pos.2 hζ
  · intro g hg hG hζK
    have hu := P5.Rad.glev_last_uwb hg
    have hζA : Tz k r D.z * Tz k r D.z' < Complex.normSq (herm (Hpk k r) (g.mulVec D.z') D.z) := by
      unfold GGl at hG
      rw [P5.Rad.zetaL_last] at hG
      linarith
    obtain ⟨h, hh, h', hh', hgeq⟩ := Formalism.FourierDecayAlt.P.b2_rank_one_coord k r D.z D.z' D.μsec D.k_pos D.z_mem
      D.z'_mem D.T_pos D.T'_pos D.sec g hu hζA
    rw [P5.Rad.zetaL_last] at hζK
    refine ⟨(herm (Hpk k r) (g.mulVec D.z') D.z, ((h⁻¹ : Mx k r), (h' : Mx k r))),
      ⟨hζK, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh, hh'⟩, ?_⟩
    show (Matrix.of (F _) : Mx k r) = g
    rw [hF]
    exact hgeq.symm

theorem rds_haar_pos {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {g₀ : Mx k r}
    (hg₀ : g₀ ∈ Glev k r (Fin.last r)) {V : Set (Mt k r)} (hV : IsOpen V) (hgV : (g₀ : Mt k r) ∈ V) : 0 < μ V := by
  have hinv : ∀ u ∈ Glev k r (Fin.last r), u⁻¹ ∈ Glev k r (Fin.last r) := fun u hu => Formalism.FourierDecayAlt.P.Qx8.glev_inv hu
  have hunit : ∀ u ∈ Glev k r (Fin.last r), IsUnit (u : B.Mat k r).det := fun u hu =>
    Matrix.isUnit_det_of_left_inverse (Formalism.FourierDecayAlt.P.Qx8.inv_mul_uh hu.1)
  have hV1 : IsOpen (lmulM g₀ ⁻¹' V) := hV.preimage (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont _)
  have h1 : ((1 : B.Mat k r) : Mt k r) ∈ lmulM g₀ ⁻¹' V := by
    show g₀ * 1 ∈ V
    rw [mul_one]; exact hgV
  have hpos := Formalism.FourierDecayAlt.P.CutMP.JA.SA.haar_pos_nhds_one hμ hinv hunit hV1 h1
  have e := hμ.left g₀ hg₀
  have hm := Measure.map_apply (μ := μ) (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) g₀).measurable hV.measurableSet
  rw [e] at hm
  rw [hm]; exact hpos

theorem rds_dxc_pos {A : Set (Fin r → ℂ)} (hA : IsOpen A) (hAne : A.Nonempty) (hAO : A ⊆ OmX r) : 0 < dxc r A := by
  have hmeas : Measurable fun c : Fin r → ℂ => ENNReal.ofReal (∏ l, (‖c l‖ ^ 2)⁻¹) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun l _ => ?_)
    exact ((measurable_pi_apply l).norm.pow_const 2).inv
  rw [pos_iff_ne_zero]
  intro h0
  unfold dxc at h0
  rw [withDensity_apply_eq_zero' hmeas.aemeasurable] at h0
  have hsub : A ⊆ {c | ENNReal.ofReal (∏ l, (‖c l‖ ^ 2)⁻¹) ≠ 0} ∩ A := by
    intro c hc
    refine ⟨?_, hc⟩
    simp only [Set.mem_ofPred_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Finset.prod_pos fun l _ => inv_pos.2 (pow_pos (norm_pos_iff.2 (hAO hc l)) 2)
  exact (hA.measure_ne_zero volume hAne) (measure_mono_null hsub h0)

end Fund

section Fund2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rds_hsVec_ne_zero {A : Wq →L[ℂ] Wp} (hA : A ≠ 0) : B.hsVec A ≠ 0 := by
  intro h
  apply hA
  have hb : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => by
    have := congrArg (fun v => (WithLp.ofLp v) i) h
    simpa [B.hsVec] using this
  ext v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (stdOrthonormalBasis ℂ Wq).sum_repr v, map_sum]
  simp [hb]

theorem rdsMul_mem (a : (Fin r → ℂ) → ℝ) (b : ℂ → ℝ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (Δ : RadSp k r z z' π π') :
    (fun c g => ((a c * b (zetaL k r z z' (Fin.last r) g) : ℝ) : ℂ) • (Δ : Fn k r (Wq →L[ℂ] Wp)) c g) ∈
      RadSp k r z z' π π' := by
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · simp [Δ.2.1 x hx]
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := Δ.2.2.1 x₀ hx₀
    refine ⟨U, fun x => ((a x.1 * b (zetaL k r z z' (Fin.last r) x.2) : ℝ) : ℂ) • F x, hU, hxU, ?_,
      fun x hx hg => by simp only [hΦF x hx hg]⟩
    have hs : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r =>
        ((a x.1 * b (zetaL k r z z' (Fin.last r) x.2) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((ha.comp contDiff_fst).mul
        (hb.comp ((Qx5.zetaL_contDiff k r z z' _).comp contDiff_snd)))
    exact hs.contDiffOn.smul hF
  · show ((a x.1 * b (zetaL k r z z' (Fin.last r) (h * x.2 * h')) : ℝ) : ℂ) •
        (Δ : Fn k r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
      (π h).comp ((((a x.1 * b (zetaL k r z z' (Fin.last r) x.2) : ℝ) : ℂ) •
        (Δ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
    rw [Formalism.FourierDecayAlt.P.Qx8.zetaL_equiv hh hh', Δ.2.2.2 x hx h hh h' hh', ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]

end Fund2

theorem spectral_fundamental_identity : RDSFund := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Φ₁ Φ₂ hEq x₀ hx₀
  subst hz hz' hπ hπ'
  have hμ := hD.2.1
  have hσ := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμ
  by_contra hne
  let Δ : RadSp P.k P.r D.z D.z' D.π D.π' := Φ₁ - Φ₂
  have hΔ0 : (Δ : Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 x₀.2 ≠ 0 := by
    simp only [Δ, Submodule.coe_sub, Pi.sub_apply]
    exact sub_ne_zero.2 hne

  have hOm : IsOpen (OmX P.r) := by
    have : OmX P.r = ⋂ l, {c : Fin P.r → ℂ | c l ≠ 0} := by ext c; simp [OmX]
    rw [this]; exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hOm x₀.1 hx₀.1
  let χb : ContDiffBump x₀.1 := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hχO : Metric.closedBall x₀.1 (ε / 2) ⊆ OmX P.r :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεO

  let ζ₀ := zetaL P.k P.r D.z D.z' (Fin.last P.r) x₀.2
  have hζ₀ : ζ₀ ∈ JCx2.rbO (Tz P.k P.r D.z) (Tz P.k P.r D.z') := by
    have := hx₀.2.2
    unfold GGl at this
    show Tz P.k P.r D.z * Tz P.k P.r D.z' < Complex.normSq ζ₀
    linarith
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 (JCx2.rb_isOpen_O _ _) ζ₀ hζ₀
  let ηb : ContDiffBump ζ₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hKz : IsCompact (Metric.closedBall ζ₀ (δ / 2)) := isCompact_closedBall _ _
  have hKzA : Metric.closedBall ζ₀ (δ / 2) ⊆ JCx2.rbO (Tz P.k P.r D.z) (Tz P.k P.r D.z') :=
    (Metric.closedBall_subset_ball (by linarith)).trans hδO
  obtain ⟨K', hK'c, hK'D, hK'⟩ := rds_zeta_compact D hKz hKzA

  let Ψ : RadSp P.k P.r D.z D.z' D.π D.π' := ⟨_, rdsMul_mem χb ηb χb.contDiff ηb.contDiff Δ⟩
  have hΨv : ∀ c g, (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      ((χb c * ηb (zetaL P.k P.r D.z D.z' (Fin.last P.r) g) : ℝ) : ℂ) • (Δ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g :=
    fun _ _ => rfl
  have hΨ : RTest Ψ := by
    refine ⟨Metric.closedBall x₀.1 (ε / 2) ×ˢ (K' ∩ Glev P.k P.r (Fin.last P.r)),
      (isCompact_closedBall _ _).prod (hK'c.inter_right (Qx5.Glev_closed _)), ?_, ?_⟩
    · rintro x ⟨hx1, hx2, hx3⟩
      exact ⟨hχO hx1, hx3, hK'D hx2⟩
    · intro x hx
      rw [hΨv]
      by_cases hxD : x ∈ DomR P.k P.r D.z D.z'
      · have hcoef : χb x.1 * ηb (zetaL P.k P.r D.z D.z' (Fin.last P.r) x.2) = 0 := by
          by_cases h1 : x.1 ∈ Metric.closedBall x₀.1 (ε / 2)
          · have h2 : x.2 ∉ K' := fun h2 => hx ⟨h1, h2, hxD.2.1⟩
            have h3 : zetaL P.k P.r D.z D.z' (Fin.last P.r) x.2 ∉ Metric.closedBall ζ₀ (δ / 2) :=
              fun h3 => h2 (hK' x.2 hxD.2.1 hxD.2.2 h3)
            have h4 : ηb (zetaL P.k P.r D.z D.z' (Fin.last P.r) x.2) = 0 := by
              rw [← Function.notMem_support, ηb.support_eq]
              exact fun h5 => h3 (Metric.ball_subset_closedBall h5)
            rw [h4, mul_zero]
          · have h4 : χb x.1 = 0 := by
              rw [← Function.notMem_support, χb.support_eq]
              exact fun h5 => h1 (Metric.ball_subset_closedBall h5)
            rw [h4, zero_mul]
        rw [hcoef]; simp
      · rw [Δ.2.1 x hxD, smul_zero]

  have h1 := hEq Ψ hΨ
  rw [radIp_eq_prod hμ Φ₁ Ψ hΨ, radIp_eq_prod hμ Φ₂ Ψ hΨ] at h1
  have hsub : ∫ p, ipF Δ Ψ p ∂((dxc P.r).prod μ) = 0 := by
    have e : ipF Δ Ψ = fun p => ipF Φ₁ Ψ p - ipF Φ₂ Ψ p := by
      funext p
      simp only [ipF, Δ, Submodule.coe_sub, Pi.sub_apply, hsVec_sub_rd, inner_sub_left]
    rw [e, integral_sub (ipF_integrable hμ Φ₁ Ψ hΨ) (ipF_integrable hμ Φ₂ Ψ hΨ), h1, sub_self]

  let f : (Fin P.r → ℂ) × Mt P.k P.r → ℝ := fun p =>
    (χb p.1 * ηb (zetaL P.k P.r D.z D.z' (Fin.last P.r) (Matrix.of p.2))) *
      ‖B.hsVec ((Δ : Fn P.k P.r (Wq →L[ℂ] Wp)) p.1 (Matrix.of p.2))‖ ^ 2
  have hf : ∀ p, ipF Δ Ψ p = (f p : ℂ) := by
    intro p
    simp only [ipF, hΨv, rds_hsVec_smul, inner_smul_right, inner_self_eq_norm_sq_to_K, f]
    push_cast
    rfl
  have hfi : Integrable f ((dxc P.r).prod μ) := by
    have := (ipF_integrable hμ Δ Ψ hΨ).re
    simpa [hf] using this
  have hf0 : ∫ p, f p ∂((dxc P.r).prod μ) = 0 := by
    have e : (fun p => ipF Δ Ψ p) = fun p => ((f p : ℝ) : ℂ) := funext hf
    rw [e, integral_complex_ofReal] at hsub
    exact_mod_cast hsub
  have hfnn : 0 ≤ f := fun p =>
    mul_nonneg (mul_nonneg (χb.nonneg) (ηb.nonneg)) (sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg hfnn hfi).1 hf0

  let p₀ : (Fin P.r → ℂ) × Mt P.k P.r := (x₀.1, x₀.2)
  have hp₀D : p₀ ∈ DomRt P.k P.r D.z D.z' := hx₀
  have hfp₀ : 0 < f p₀ := by
    refine mul_pos (mul_pos (χb.pos_of_mem_ball (Metric.mem_ball_self χb.rOut_pos))
      (ηb.pos_of_mem_ball (Metric.mem_ball_self ηb.rOut_pos))) ?_
    exact pow_pos (norm_pos_iff.2 (rds_hsVec_ne_zero hΔ0)) 2
  have hfc : ContinuousOn f (DomRt P.k P.r D.z D.z') := by
    have e : f = fun p => Complex.re (ipF Δ Ψ p) := by funext p; rw [hf]; simp
    rw [e]
    exact Complex.continuous_re.comp_continuousOn (ipF_contOn Δ Ψ)
  have hev : ∀ᶠ p in 𝓝[DomRt P.k P.r D.z D.z'] p₀, 0 < f p := (hfc p₀ hp₀D).eventually (lt_mem_nhds hfp₀)
  obtain ⟨O, hOo, hp₀O, hOsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨A, Bo, hA, hB, hA0, hB0, hAB⟩ := isOpen_prod_iff.1 hOo p₀.1 p₀.2 hp₀O
  let A' := A ∩ OmX P.r
  let B' := Bo ∩ {x : Mt P.k P.r | 0 < GGl P.k P.r D.z D.z' (Matrix.of x)}
  have hA' : IsOpen A' := hA.inter hOm
  have hB' : IsOpen B' := hB.inter (isOpen_lt continuous_const (Qx5.GGl_continuous P.k P.r D.z D.z'))
  have hGl : IsClosed {x : Mt P.k P.r | (Matrix.of x : Mx P.k P.r) ∈ Glev P.k P.r (Fin.last P.r)} :=
    Qx5.Glev_closed _
  have hbox : A' ×ˢ (B' ∩ {x : Mt P.k P.r | (Matrix.of x : Mx P.k P.r) ∈ Glev P.k P.r (Fin.last P.r)}) ⊆
      {p | ¬ f p = (0 : (Fin P.r → ℂ) × Mt P.k P.r → ℝ) p} := by
    rintro p ⟨⟨hpA, hpO⟩, ⟨hpB, hpG⟩, hpL⟩
    have hpD : p ∈ DomRt P.k P.r D.z D.z' := ⟨hpO, hpL, hpG⟩
    exact (hOsub ⟨hAB ⟨hpA, hpB⟩, hpD⟩).ne'
  have hnull := measure_mono_null hbox (ae_iff.1 hae)
  rw [Measure.prod_prod, measure_inter_conull (show μ {x : Mt P.k P.r |
      (Matrix.of x : Mx P.k P.r) ∈ Glev P.k P.r (Fin.last P.r)}ᶜ = 0 from hμ.conc)] at hnull
  have hApos : 0 < dxc P.r A' := rds_dxc_pos hA' ⟨x₀.1, hA0, hx₀.1⟩ Set.inter_subset_right
  have hBpos : 0 < μ B' := rds_haar_pos hμ hx₀.2.1 hB' ⟨hB0, hx₀.2.2⟩
  exact (ENNReal.mul_pos hApos.ne' hBpos.ne').ne' hnull

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSYReal
namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem spectral_Y_real : RDSYReal := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _
  classical
  let T : Finset ℝ := Finset.univ.biUnion fun τ : M.Ty P =>
    (Finset.Icc 1 (P.k - 1)).image fun i => -(M.rho P τ i)
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (T ∪ T.image (fun t => t - 1) ∪ T.image (fun t => t + 1))
  have hinv := hD.2.2.2.2.2.1
  have good : ∀ t : ℝ, t ∉ T → (t : ℂ) ∈ st.inv := by
    intro t ht
    rw [hinv]
    intro τ
    unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i hi h0
    apply ht
    refine Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, Finset.mem_image.2 ⟨i, hi, ?_⟩⟩
    have h1 : ((t + M.rho P τ i : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have h2 := Complex.ofReal_eq_zero.1 h1
    linarith
  refine ⟨(y : ℂ), by rw [Complex.star_def, Complex.conj_ofReal], ?_,
    good y fun h => hy (Finset.mem_union_left _ (Finset.mem_union_left _ h)), ?_⟩
  · have e : ((y : ℂ) - 1) = ((y - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    exact good (y - 1) fun h => hy (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y - 1, h, by ring⟩))
  · have e : ((y : ℂ) + 1) = ((y + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    exact good (y + 1) fun h => hy (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨y + 1, h, by ring⟩)))

end Formalism.FourierDecayAlt.P.CutSE
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSSection
open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Gauge

variable {k r : ℕ}

def secGauge (k r : ℕ) (c : Fin r → ℂ) : ℂ := ∏ a : Fin r, ((‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ)

theorem secGauge_smooth : ContDiffOn ℝ ∞ (secGauge k r) (OmX r) := by
  unfold secGauge
  apply contDiffOn_prod
  intro a _ x hx
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖) x :=
    (contDiffAt_norm ℝ (hx a)).comp x (contDiff_apply ℝ (fun _ => ℂ) a).contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt).comp x (h1.pow _)

theorem secGauge_ne {c : Fin r → ℂ} (hc : c ∈ OmX r) : secGauge k r c ≠ 0 := by
  unfold secGauge
  refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_)
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc a)))

theorem secGauge_inv_smooth : ContDiffOn ℝ ∞ (fun c => (secGauge k r c)⁻¹) (OmX r) := secGauge_smooth.inv (fun c hc => secGauge_ne hc)

theorem resG_last_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Mx k r → E) (c : Fin r → ℂ)
    (g : Mx k r) : resG k r (Fin.last r) J c g = secGauge k r c • J (wCell k r (Fin.last r) c * g) := by
  unfold resG secGauge
  congr 1
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [if_pos (show (a : ℕ) < (Fin.last r : ℕ) from a.isLt)]

end Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem spectral_section_identity : RDSSection := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Ψ _
  classical
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  obtain ⟨h0, hs, he⟩ := Ψ.2

  let Φf : Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g => (secGauge P.k P.r c)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
  have hmem : Φf ∈ RadSp P.k P.r z z' π π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = 0
      rw [h0 x hx, smul_zero]
    · obtain ⟨U, F, hU, hxU, hF, hΨ⟩ := hs x₀ hx₀
      have hV : IsOpen {x : (Fin P.r → ℂ) × Mx P.k P.r | x.1 ∈ OmX P.r} :=
        (Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX P.r).preimage continuous_fst
      refine ⟨U ∩ {x | x.1 ∈ OmX P.r}, fun x => (secGauge P.k P.r x.1)⁻¹ • F x, hU.inter hV, ⟨hxU, hx₀.1⟩, ?_,
        fun x hx hxG => ?_⟩
      · have hg : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × Mx P.k P.r => (secGauge P.k P.r x.1)⁻¹)
            (U ∩ {x | x.1 ∈ OmX P.r}) :=
          secGauge_inv_smooth.comp contDiff_fst.contDiffOn fun x hx => hx.2
        exact hg.smul (hF.mono Set.inter_subset_left)
      · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
        rw [hΨ x hx.1 hxG]
    · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
        (π h).comp (((secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
      rw [he x hx h hh h' hh', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  obtain ⟨D₀, hD₀, K, hK, hKv⟩ :=
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_descent_holds Wp Wq P.k P.r z z' π π' hz hz' Φf hmem
  have hsub : ∀ g ∈ Q.Glev P.k P.r 0 ∩ Q.OmPlus P.k P.r z z', g ∈ D₀ := by
    intro g hg
    obtain ⟨n, hn, n', hn', c, hc, g₁, hg₁, hGG, hgeq⟩ :=
      Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_cover_holds P.k P.r z z' hz hz' g hg
    have hw := (hKv c hc g₁ hg₁ hGG).1
    have hwG : Q.wCell P.k P.r (Fin.last P.r) c * g₁ ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg₁)
    rw [hgeq]
    exact hD₀.2 _ ⟨hwG, hw⟩ n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n, hn, (Matrix.one_mul n).symm⟩ n'
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n', hn', (Matrix.one_mul n').symm⟩
  have hKO : K ∈ Q.FFl P.k P.r z z' π π' 0 (Q.OmPlus P.k P.r z z') := by
    obtain ⟨hs', hL, hRt, hW⟩ := hK
    exact ⟨fun g₀ hg₀ => hs' g₀ ⟨hg₀.1, hsub g₀ hg₀⟩, fun g hg n hn => hL g ⟨hg.1, hsub g hg⟩ n hn,
      fun g hg n hn => hRt g ⟨hg.1, hsub g hg⟩ n hn, fun g hg h hh h' hh' => hW g ⟨hg.1, hsub g hg⟩ h hh h' hh'⟩
  refine ⟨K, ?_, fun x hx => ?_⟩
  · rw [rdb_ffl_om_eq]; exact hKO
  · rw [resG_last_eq, (hKv x.1 hx.1 x.2 hx.2.1 hx.2.2).2]
    show _ = secGauge P.k P.r x.1 • ((secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
    rw [smul_smul, mul_inv_cancel₀ (secGauge_ne hx.1), one_smul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_open (h0 : RDSOpAv) (h1 : RDSOpR) (h2 : RDSOpRv) (h3 : RDSOpA)
    (hp : RDSPAdj) (hQ : RDSQQAdj) (hX : RDSXiTest) (hP : RDSPair) : RDIdentSpec :=
  rDIdentSpec_of_cut spectral_Y_real h0 h1 h2 h3 spectral_inner_product_linear (rDSCoordAdj_of_p hp) spectral_function_adjoint hQ hX spectral_fundamental_identity spectral_section_identity hP
    radial_residue_formula radial_operator_function_field

end Formalism.FourierDecayAlt.P.CutSE
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSXiTest
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.Kfp

theorem rdsXi_kappa_inv_aeval {T A : Type} [Fintype T] [Ring A] [Algebra ℂ A] (κ : (T → ℂ) →ₐ[ℂ] A) (f : T → ℂ) :
    ∃ p : Polynomial ℂ, κ (fun ρ => (f ρ)⁻¹) = Polynomial.aeval (κ f) p := by
  classical
  set N : Finset ℂ := Finset.univ.image f
  set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
  have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
    intro ρ
    have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
    have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
    simpa only [id] using h
  have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
    funext ρ
    rw [← hp ρ]
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : T => ℂ) ρ) f p
    rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
    rw [this]
    rfl
  exact ⟨p, by rw [he, ← Polynomial.aeval_algHom_apply]⟩

theorem spectral_xi_test : RDSXiTest := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Y hYr hYi Ψ hΨ
  obtain ⟨κ, hx, hxi, -⟩ := xKappaOfNF normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hD' := hD
  obtain ⟨hPl, -, hL, hQQ, -, -, -, hst⟩ := hD'
  obtain ⟨p, hp⟩ := rdsXi_kappa_inv_aeval κ (fun ρ => M.x0 P l0 ρ Y)
  have hxiY : st.xi Y = Polynomial.aeval (st.x Y) p := by rw [hxi Y hYi, hp, ← hx Y]

  have hx1 : (st.x Y).1 = M.sgn P l0 • (X.fn 5 * X.t Y 1 1) := by
    have e1 : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hst.tau, ← mul_assoc, L.GGi_GG, one_mul]
    rw [e1, hQQ Y, Matrix.smul_apply, hL.2.2.2.2.2.2.2.2.2.2.2.1, mul_smul_comm]
    rw [Algebra.smul_def]
    show algebraMap ℂ (Module.End ℂ _) (M.sgn P l0) * (X.fn 5 * X.t Y 1 1) = _
    rw [← Algebra.smul_def]

  have hxi1 : (st.xi Y).1 = Polynomial.aeval (M.sgn P l0 • (X.fn 5 * X.t Y 1 1)) p := by
    rw [hxiY, ← hx1]
    exact (Polynomial.aeval_algHom_apply (fstAlg _) (st.x Y) p).symm

  have h1 : RTest ((st.xi Y).1 Ψ) := by
    obtain ⟨K, hK, hKD, hK0⟩ := hΨ
    refine ⟨K, hK, hKD, fun x hxK => ?_⟩
    by_cases hxD : x ∈ DomR P.k P.r z z'
    swap
    · exact ((st.xi Y).1 Ψ).2.1 x hxD
    obtain ⟨c, g⟩ := x
    have hxD' := hxD
    obtain ⟨hc, hg, hG⟩ := hxD'
    obtain ⟨hP, hz, hz', hTz, hTz', -, hπ'⟩ := hPl
    have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hP.T_pos
    have hT' : 0 < Tz P.k P.r z' := by rw [hTz']; exact hP.T'_pos
    obtain ⟨Bs, -, -, hB1, -⟩ := LieAlgebraWeightVectors.geom_package hz hz' hT hT' hg hG.ne'
    set C : Module.End ℂ Wq := M.sgn P l0 • qdet (EB π' Bs) (Y + ((P.k : ℂ) - 2) / 2) with hCdef
    have hact : ∀ (Φ : RadSp P.k P.r z z' π π') (v : Wq),
        (((M.sgn P l0 • (X.fn 5 * X.t Y 1 1)) Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v =
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (C v) := by
      intro Φ v
      rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, ContinuousLinearMap.smul_apply,
        diagonal_transfer_action X hz hz' hπ'.2.1 hπ'.2.2.1 hxD Bs hB1 Y Φ v, hCdef, LinearMap.smul_apply, map_smul]
    have h0 : (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 := hK0 (c, g) hxK
    ext v
    rw [hxi1]
    erw [aeval_act _ C hact p Ψ v]
    rw [h0]
    rfl
  refine ⟨h1, ?_⟩

  have hstar : star (st.xi Y) = st.xi Y := by
    obtain ⟨u, -⟩ := hst.x_xi Y hYi
    have e : star (st.xi Y) * st.x Y = 1 := by
      have := congrArg star u
      rwa [star_mul, hst.x_star Y hYr, star_one] at this
    calc star (st.xi Y) = star (st.xi Y) * (st.x Y * st.xi Y) := by rw [u, mul_one]
      _ = st.xi Y := by rw [← mul_assoc, e, one_mul]
  have e2 : (st.xi Y).2.unop = (st.xi Y).1 := by
    have := congrArg Prod.fst hstar
    exact this
  rw [e2]
  exact h1

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSQQAdj
open MeasureTheory Filter Topology
open scoped Matrix ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE.QQA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Loc

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem smoothLev_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Mx k r)) :
    SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : E)) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothLev_mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D D' : Set (Mx k r)} (h : D ⊆ D')
    {f : Mx k r → E} (hf : SmoothLev k r (Fin.last r) D' f) : SmoothLev k r (Fin.last r) D f :=
  fun g₀ hg₀ => hf g₀ ⟨hg₀.1, h hg₀.2⟩

theorem tL_zero_at {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D) (Y : ℂ)
    (p q : Fin 2) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g = 0 := by
  have h := (Formalism.FourierDecayAlt.P.transfer_linear_local E k r z z' (Fin.last r) D Y p q (fun _ => (0 : E)) (fun _ => (0 : E)) 1 hD
    (smoothLev_zero D) (smoothLev_zero D) g hg).1
  simp only [smul_zero, add_zero, one_smul] at h
  have h2 : tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g +
      tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g =
      tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g + 0 := by
    rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem tL_eq_zero_local {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
    {f : Mx k r → E} (hf : SmoothLev k r (Fin.last r) D f) (h0 : ∀ x ∈ Glev k r (Fin.last r) ∩ D, f x = 0) (Y : ℂ)
    (p q : Fin 2) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : tL k r z z' (Fin.last r) Y p q f g = 0 := by
  rw [(Formalism.FourierDecayAlt.P.transfer_linear_local E k r z z' (Fin.last r) D Y p q f (fun _ => (0 : E)) 0 hD hf (smoothLev_zero D)
    g hg).2 h0]
  exact tL_zero_at hD Y p q hg

theorem bump_exists {Kc : Set (Mx k r)} (hKc : IsCompact Kc) (hKD : Kc ⊆ Qx5.Dp k r z z') :
    ∃ (χ : Mx k r → ℝ) (O L : Set (Mx k r)), ContDiff ℝ ∞ χ ∧ IsOpen O ∧ Kc ⊆ O ∧ IsCompact L ∧
      L ⊆ Qx5.Dp k r z z' ∧ (∀ g ∈ O, χ g = 1) ∧ ∀ g, g ∉ L → χ g = 0 := by
  have : LocallyCompactSpace (Mx k r) :=
    (inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨L, hLc, hKL, hLD⟩ := exists_compact_between hKc (Qx5.Dp_open k r z z') hKD
  obtain ⟨f₁, hsupp, hf₁, hrange⟩ := (isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)
  have hf₁c : Continuous f₁ := hf₁.continuous
  have hpos : ∀ g ∈ Kc, 0 < f₁ g := fun g hg => by
    have h1 : g ∈ Function.support f₁ := by rw [hsupp]; exact hKL hg
    exact lt_of_le_of_ne (hrange ⟨g, rfl⟩).1 (Ne.symm h1)
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ g ∈ Kc, m ≤ f₁ g := by
    rcases Kc.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨g₁, hg₁, hmin⟩ := hKc.exists_isMinOn h hf₁c.continuousOn
      exact ⟨f₁ g₁, hpos g₁ hg₁, fun g hg => hmin hg⟩
  refine ⟨fun g => Real.smoothTransition (2 * f₁ g / m), {g | m / 2 < f₁ g}, L,
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul hf₁).div_const m),
    isOpen_lt continuous_const hf₁c, fun g hg => by have := hmK g hg; show m / 2 < f₁ g; linarith, hLc, hLD,
    fun g hg => ?_, fun g hg => ?_⟩
  · have hg' : m / 2 < f₁ g := hg
    exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hm]; linarith)
  · have h0 : f₁ g = 0 := by
      by_contra h
      have h1 : g ∈ Function.support f₁ := h
      rw [hsupp] at h1
      exact hg (interior_subset h1)
    show Real.smoothTransition (2 * f₁ g / m) = 0
    rw [h0, mul_zero, zero_div]
    exact Real.smoothTransition.zero_of_nonpos le_rfl

end Loc

section Rad

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem t_zero_near (X : ActualOps k r z z' π π') (Ψ : RadSp k r z z' π π') (Y : ℂ) (a b : Fin 2)
    {x : (Fin r → ℂ) × Mx k r} {O : Set (Mx k r)} (hO : IsOpen O) (hxO : x.2 ∈ O)
    (h0 : ∀ g ∈ Glev k r (Fin.last r) ∩ O, (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 g = 0) :
    (X.t Y a b Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := by
  by_cases hx : x ∈ DomR k r z z'
  · rw [X.t_apply Y a b Ψ x hx]
    exact tL_eq_zero_local (hO.inter (Qx5.Dp_open k r z z'))
      (smoothLev_mono Set.inter_subset_right (Qx5.slice_smooth Ψ.2 hx.1))
      (fun g hg => h0 g ⟨hg.1, hg.2.1⟩) Y a b ⟨hx.2.1, hxO, hx.2.2⟩
  · exact Formalism.FourierDecayAlt.P5.radSp_zero_off _ hx

theorem entry_operator_preserves_tests (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) {Ψ : RadSp k r z z' π π'} (hΨ : RTest Ψ) :
    RTest (X.t Y a b Ψ) := by
  obtain ⟨K, hK, hKD, h0⟩ := hΨ
  refine ⟨K, hK, hKD, fun x hx => ?_⟩
  have hO : IsOpen {g : Mx k r | (x.1, g) ∉ K} :=
    hK.isClosed.isOpen_compl.preimage (continuous_const.prodMk continuous_id)
  exact t_zero_near X Ψ Y a b hO (show (x.1, x.2) ∉ K from hx) fun g hg => h0 (x.1, g) hg.2

theorem slice_cpt {Ψ : RadSp k r z z' π π'} (hΨ : RTest Ψ) (c : Fin r → ℂ) :
    ∃ Kc : Set (Mx k r), IsCompact Kc ∧ Kc ⊆ Qx5.Dp k r z z' ∧
      ∀ g, g ∉ Kc → (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := by
  obtain ⟨K, hK, hKD, h0⟩ := hΨ
  refine ⟨Prod.snd '' (K ∩ Prod.fst ⁻¹' {c}),
    (hK.inter_right (isClosed_singleton.preimage continuous_fst)).image continuous_snd, ?_,
    fun g hg => h0 (c, g) fun hcg => hg ⟨(c, g), ⟨hcg, rfl⟩, rfl⟩⟩
  rintro _ ⟨x, ⟨hxK, -⟩, rfl⟩
  exact (hKD hxK).2.2

theorem slice_adj_clm (hz : inWb k r z) (hz' : inWb k r z') (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)}
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {Kc : Set (Mx k r)} (hKc : IsCompact Kc) (hKD : Kc ⊆ Qx5.Dp k r z z')
    (h0 : ∀ g, g ∉ Kc → (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) (Y : ℂ) (a b : Fin 2) (φ : (Wq →L[ℂ] Wp) →L[ℂ] ℂ) :
    (∫ x : Mt k r, φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
        star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ) =
      ∫ x : Mt k r, φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
        star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ := by
  obtain ⟨χ, O, L, hχs, hO, hKO, hLc, hLD, χ1, χ0⟩ := bump_exists hKc hKD
  obtain ⟨fΨ, hfΨ⟩ : ∃ f : Mx k r → ℂ, f = fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y) := ⟨_, rfl⟩
  obtain ⟨fΦ, hfΦ⟩ : ∃ f : Mx k r → ℂ, f = fun y => (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y) := ⟨_, rfl⟩
  have hsΨ : SmoothLev k r (Fin.last r) Set.univ fΨ := by
    rw [hfΨ]; exact Qx5.smooth_clm φ (Qx5.smooth_univ Ψ.2 hc hKc hKD fun g _ hg => h0 g hg)
  have hcΨ : CptOn k r (Fin.last r) fΨ := ⟨Kc, hKc, fun g _ hg => by rw [hfΨ]; simp [h0 g hg]⟩
  have hsΦ : SmoothLev k r (Fin.last r) Set.univ fΦ := by
    intro g₀ hg₀
    by_cases hgL : g₀ ∈ L
    · obtain ⟨U, F, hU, hgU, hF, he⟩ := Qx5.smooth_clm φ (Qx5.slice_smooth Φ.2 hc) g₀ ⟨hg₀.1, hLD hgL⟩
      refine ⟨U, fun y => (χ y : ℂ) * F y, hU, hgU,
        (Complex.ofRealCLM.contDiff.comp_contDiffOn hχs.contDiffOn).mul hF, fun y hy hyG => ?_⟩
      rw [hfΦ]
      show (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y) = (χ y : ℂ) * F y
      rw [← he y hy hyG]
    · refine ⟨Lᶜ, fun _ => 0, hLc.isClosed.isOpen_compl, hgL, contDiffOn_const, fun y hy _ => ?_⟩
      rw [hfΦ]
      show (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y) = 0
      rw [χ0 y hy, Complex.ofReal_zero, zero_mul]
  have hcΦ : CptOn k r (Fin.last r) fΦ := ⟨L, hLc, fun g _ hg => by rw [hfΦ]; simp [χ0 g hg]⟩
  have hh := Formalism.FourierDecayAlt.P.hermitian_haar_invariance k r z z' (Fin.last r) μ hμ hz hz' fΨ fΦ hsΨ hsΦ hcΨ hcΦ (star Y) b a
  rw [star_star] at hh
  have eA : ∀ x : Mx k r, φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) =
      fΨ x * star (tL k r z z' (Fin.last r) Y a b fΦ x) := by
    intro x
    rw [Qx5.key_pt X Φ Ψ hc Y a b φ x, hfΨ]
    by_cases hx0 : (Ψ : Fn k r (Wq →L[ℂ] Wp)) c x = 0
    · simp [hx0]
    · have hxK : x ∈ Kc := by
        by_contra h
        exact hx0 (h0 x h)
      have hxG : x ∈ Glev k r (Fin.last r) := by
        by_contra h
        exact hx0 (Formalism.FourierDecayAlt.P5.radSp_zero_off Ψ (x := (c, x)) fun hd => h hd.2.1)
      have hloc := (Formalism.FourierDecayAlt.P.transfer_linear_local ℂ k r z z' (Fin.last r) (O ∩ Qx5.Dp k r z z') Y a b
        (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) fΦ 0 (hO.inter (Qx5.Dp_open k r z z'))
        (smoothLev_mono Set.inter_subset_right (Qx5.smooth_clm φ (Qx5.slice_smooth Φ.2 hc)))
        (smoothLev_mono (Set.subset_univ _) hsΦ) x ⟨hxG, hKO hxK, hKD hxK⟩).2
        (fun y hy => by rw [hfΦ]; show _ = (χ y : ℂ) * _; rw [χ1 y hy.2.1, Complex.ofReal_one, one_mul])
      rw [hloc]
  have eB : ∀ x : Mx k r, φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) *
      star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) =
      tL k r z z' (Fin.last r) (star Y) b a fΨ x * star (fΦ x) := by
    intro x
    have e0 : φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) =
        tL k r z z' (Fin.last r) (star Y) b a (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) x *
          star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) := by
      have := congrArg star (Qx5.key_pt X Ψ Φ hc (star Y) b a φ x)
      simpa [mul_comm] using this
    rw [e0, hfΨ, hfΦ]
    show _ = _ * star ((χ x : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x))
    by_cases hxO : x ∈ O
    · rw [χ1 x hxO, Complex.ofReal_one, one_mul]
    · by_cases hxD : (c, x) ∈ DomR k r z z'
      · have hxK : x ∉ Kc := fun h => hxO (hKO h)
        have ht0 : tL k r z z' (Fin.last r) (star Y) b a (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) x = 0 :=
          tL_eq_zero_local hKc.isClosed.isOpen_compl
            (smoothLev_mono (Set.subset_univ _) (hfΨ ▸ hsΨ))
            (fun y hy => by simp [h0 y hy.2]) (star Y) b a ⟨hxD.2.1, hxK⟩
        rw [ht0, zero_mul, zero_mul]
      · have hΦ0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c x = 0 := Formalism.FourierDecayAlt.P5.radSp_zero_off Φ (x := (c, x)) hxD
        rw [hΦ0]
        simp
  simp only [eA, eB]
  exact hh.symm

theorem slice_adj (hz : inWb k r z) (hz' : inWb k r z') (X : ActualOps k r z z' π π')
    {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {Kc : Set (Mx k r)} (hKc : IsCompact Kc) (hKD : Kc ⊆ Qx5.Dp k r z z')
    (h0 : ∀ g, g ∉ Kc → (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) (Y : ℂ) (a b : Fin 2) (v : Wq) :
    (∫ x : Mt k r, inner ℂ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v)
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v) ∂μ) =
      ∫ x : Mt k r, inner ℂ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v)
        ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v) ∂μ := by
  have htΨ : ∀ g ∈ Glev k r (Fin.last r), g ∉ Kc → (X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 :=
    fun g _ hg => t_zero_near X Ψ (star Y) b a (x := (c, g)) hKc.isClosed.isOpen_compl hg
      (fun g' hg' => h0 g' hg'.2)
  simp only [Qx5.inner_coef]
  rw [integral_finsetSum _ fun j _ =>
      (Qx5.integrable_pair hμ (X.t Y a b Φ) Ψ hc hKc hKD (fun g _ hg => h0 g hg) _).1,
    integral_finsetSum _ fun j _ => (Qx5.integrable_pair hμ Φ (X.t (star Y) b a Ψ) hc hKc hKD htΨ _).1]
  exact Finset.sum_congr rfl fun j _ => slice_adj_clm hz hz' X hμ Φ Ψ hc hKc hKD h0 Y a b _

theorem radIp_adj (hz : inWb k r z) (hz' : inWb k r z')
    (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Ψ : RadSp k r z z' π π') (hΨ : RTest Ψ) (Y : ℂ) (a b : Fin 2) :
    radIp μ (X.t Y a b Φ) Ψ = radIp μ Φ (X.t (star Y) b a Ψ) := by
  unfold radIp
  congr 1
  funext c
  by_cases hc : c ∈ OmX r
  · obtain ⟨Kc, hKc, hKD, h0⟩ := slice_cpt hΨ c
    have htΨ : ∀ g ∈ Glev k r (Fin.last r), g ∉ Kc → (X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 :=
      fun g _ hg => t_zero_near X Ψ (star Y) b a (x := (c, g)) hKc.isClosed.isOpen_compl hg
        (fun g' hg' => h0 g' hg'.2)
    rw [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadAdj.int_hs_sum hμ (X.t Y a b Φ) Ψ hc hKc hKD (fun g _ hg => Or.inr (h0 g hg)),
      Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadAdj.int_hs_sum hμ Φ (X.t (star Y) b a Ψ) hc hKc hKD
        (fun g hg hgK => Or.inr (htΨ g hg hgK))]
    exact Finset.sum_congr rfl fun i _ => slice_adj hz hz' X hμ Φ Ψ hc hKc hKD h0 Y a b _
  · have hz0 : ∀ (Θ : RadSp k r z z' π π') (g : Mx k r), (Θ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := fun Θ g =>
      Formalism.FourierDecayAlt.P5.radSp_zero_off Θ (x := (c, g)) fun hd => hc hd.1
    simp only [hz0]

theorem rAdj_XQQ (hz : inWb k r z) (hz' : inWb k r z')
    (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (Y : ℂ)
    (a b : Fin 2) : RAdj μ (X.QQ Y a b) := by
  refine ⟨fun Ψ hΨ => entry_operator_preserves_tests X Y a b hΨ, fun Ψ hΨ => entry_operator_preserves_tests X (star Y) b a hΨ,
    fun Φ Ψ hΨ => radIp_adj hz hz' X hμ Φ Ψ hΨ Y a b, fun Φ Ψ hΨ => ?_⟩
  have h := radIp_adj hz hz' X hμ Φ Ψ hΨ (star Y) b a
  rw [star_star] at h
  exact h

theorem hsVec_smul_q (w : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (w • A) = w • B.hsVec A := by
  unfold B.hsVec
  rfl

theorem radIp_smul_left (μ : Measure (Mt k r)) (w : ℂ) (Φ Ψ : RadSp k r z z' π π') :
    radIp μ (w • Φ) Ψ = starRingEnd ℂ w * radIp μ Φ Ψ := by
  unfold radIp
  rw [← integral_const_mul]
  congr 1
  funext c
  rw [← integral_const_mul]
  congr 1
  funext x
  change ⟪B.hsVec (w • (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)), B.hsVec ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))⟫_ℂ = _
  rw [hsVec_smul_q, inner_smul_left]

theorem radIp_smul_right (μ : Measure (Mt k r)) (w : ℂ) (Φ Ψ : RadSp k r z z' π π') :
    radIp μ Φ (w • Ψ) = w * radIp μ Φ Ψ := by
  unfold radIp
  rw [← integral_const_mul]
  congr 1
  funext c
  rw [← integral_const_mul]
  congr 1
  funext x
  change ⟪B.hsVec ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)), B.hsVec (w • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))⟫_ℂ = _
  rw [hsVec_smul_q, inner_smul_right]

theorem rAdj_smul_real {μ : Measure (Mt k r)} {a : Pr (RadSp k r z z' π π')}
    (ha : RAdj μ a) (s : ℂ) (hs : starRingEnd ℂ s = s) : RAdj μ (s • a) := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  have es : s • a = algebraMap ℂ (Pr (RadSp k r z z' π π')) s * a := Algebra.smul_def s a
  have e1 : ∀ Φ, (s • a).1 Φ = s • a.1 Φ := fun Φ => by
    rw [es, rds_fst_mul, Module.End.mul_apply, rds_fst_alg, Module.algebraMap_end_apply]
  have e2 : ∀ Φ, (s • a).2.unop Φ = s • a.2.unop Φ := fun Φ => by
    rw [es, rds_snd_mul, Module.End.mul_apply, rds_snd_alg, Module.algebraMap_end_apply, map_smul, hs]
  refine ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_⟩
  · rw [e1]; exact rTest_smul s (h1 Ψ hΨ)
  · rw [e2]; exact rTest_smul s (h2 Ψ hΨ)
  · rw [e1, e2, radIp_smul_left, radIp_smul_right, h3 Φ Ψ hΨ, hs]
  · rw [e1, e2, radIp_smul_left, radIp_smul_right, h4 Φ Ψ hΨ, hs]

end Rad

end Formalism.FourierDecayAlt.P.CutSE.QQA

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem spectral_quadratic_adjoint : RDSQQAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Y a b
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  rw [hD.2.2.2.1 Y, Matrix.smul_apply]
  refine QQA.rAdj_smul_real (QQA.rAdj_XQQ hz hz' X hD.2.1 Y a b) _ ?_
  simp [M.sgn]

end Formalism.FourierDecayAlt.P.CutSE
end
end

namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_R (hR : RDSOpR) (hRv : RDSOpRv) : RDIdentSpec :=
  rDIdentSpec_of_open spectral_operator_A_adjoint hR hRv spectral_operator_A spectral_pairing_adjoint spectral_quadratic_adjoint spectral_xi_test spectral_pairing_identity

theorem thmPActualCpt_of_R (hR : RDSOpR) (hRv : RDSOpRv) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_spec (rDIdentSpec_of_R hR hRv)

end Formalism.FourierDecayAlt.P.CutSE
