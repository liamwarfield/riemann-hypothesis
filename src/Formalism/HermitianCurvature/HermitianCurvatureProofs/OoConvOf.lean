module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiRegOf

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleIntegrandMeasurable
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerBound
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GNMulRpow
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MapInvMEq
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_cont : Continuous (fun g : Mx k r => B.gN g) := by
  unfold B.gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp (continuous_apply_apply i j))

theorem gNpow_inCC (hNI : NormInv) (b : ℝ) (hb : b ≠ 0) :
    B.InCC b 0 (fun g : B.Mat k r => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  have hpos : ∀ g ∈ B.GV k r, 0 < B.gN g := fun g hg => lt_of_lt_of_le one_pos ((hNI k r).2 g hg).2
  have hf : ContinuousOn (fun g : Mx k r => ((B.gN g ^ (-b) : ℝ) : ℂ)) (B.GV k r) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact gN_cont.continuousOn.rpow_const (fun g hg => Or.inl (hpos g hg).ne')
  refine ⟨1, ckOn_zero_of_contOn _ hf, ?_⟩
  intro uu vv _ _ hlen g hg
  have hu : uu = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hv : vv = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hu; subst hv
  show B.gN g ^ b * ‖((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ ≤ 1
  have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
  rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hgN _)]
  have := rpow_bound (B.gN g) 1 b hgN hb
  simpa using this

def invP (p : B.SS k r) : B.SS k r :=
  ((B2.invM p.1.1, B2.invM p.1.2), (B2.invM p.2.1, B2.invM p.2.2))

theorem map_invM_eq {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : B.IsHaarOn U μ) : μ.map B2.invM = μ := Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU hμ

theorem ae_of_haarB {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  rw [ae_iff]; exact hμ.conc

theorem ae_SS {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r ∧
      Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW := ae_of_haarB D.haarW
  have hN := ae_of_haarB D.haarN
  have hW' := ae_of_haarB D.haarW'
  have e1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have e2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have e3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have e4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem map_invP {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    D.μSS.map invP = D.μSS := by
  have hm := B2x1.invM_meas (k := k) (r := r)
  have hW := map_invM_eq (weyl_subgroup_closed k r D.z) D.haarW
  have hN := map_invM_eq (unipotent_radical_closed k r) D.haarN
  have hW' := map_invM_eq (weyl_subgroup_closed k r D.z') D.haarW'
  show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)).map
      (Prod.map (Prod.map B2.invM B2.invM) (Prod.map B2.invM B2.invM)) = (D.μW.prod D.μN).prod (D.μW'.prod D.μN)
  rw [← Measure.map_prod_map _ _ (hm.prodMap hm) (hm.prodMap hm), ← Measure.map_prod_map _ _ hm hm,
    ← Measure.map_prod_map _ _ hm hm, hW, hN, hW']

theorem la_fin (hNI : NormInv) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] {b : ℝ} (hb : JF.TransportedAlt k r b 0) (hb0 : b ≠ 0)
    {γ : B.Mat k r} (hγ : γ ∈ JF.Om k r D.z D.z') :
    ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
      ∂D.μSS < ⊤ := by
  set F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun g => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) with hF
  have hJC := Formalism.FourierDecayAlt.P.bessel_integral_converges k r ℂ ℂ (triv D) b F hb (gNpow_inCC hNI b hb0)
  obtain ⟨bb, hbb, hbd⟩ := hJC.2 {γ} isCompact_singleton (Set.singleton_subset_iff.mpr hγ)
  set G : B.SS k r → ℝ≥0∞ := fun p => ‖B.gN (B.sgs p γ) ^ (-b)‖ₑ with hG
  have h1 : ∫⁻ p, G p ∂D.μSS < ⊤ := by
    calc ∫⁻ p, G p ∂D.μSS ≤ ∫⁻ p, ‖bb p‖ₑ ∂D.μSS := by
          apply lintegral_mono_ae
          filter_upwards [hbd γ rfl] with p hp
          have e : ‖B.gN (B.sgs p γ) ^ (-b)‖ = ‖B.rho (triv D) p F γ‖ := by
            rw [rho_triv]; simp [hF]
          simp only [hG]
          rw [← ofReal_norm, ← ofReal_norm, e]
          exact ENNReal.ofReal_le_ofReal (hp.trans (Real.le_norm_self _))
      _ < ⊤ := hbb.hasFiniteIntegral
  have hinv : ∀ᵐ p ∂D.μSS, invP (invP p) = p ∧
      G (invP p) = ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ *
        (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ := by
    filter_upwards [ae_SS D] with p hp
    have u1 := (weyl_subgroup_closed k r D.z).unit _ hp.1
    have u2 := (unipotent_radical_closed k r).unit _ hp.2.1
    have u3 := (weyl_subgroup_closed k r D.z').unit _ hp.2.2.1
    have u4 := (unipotent_radical_closed k r).unit _ hp.2.2.2
    have ii : ∀ x : Formalism.QuantumDeterminants.Mt k r, IsUnit (Matrix.of x).det → B2.invM (B2.invM x) = x := by
      intro x hx
      show (((Matrix.of x)⁻¹)⁻¹ : B.Mat k r) = Matrix.of x
      exact Matrix.nonsing_inv_nonsing_inv _ hx
    refine ⟨?_, ?_⟩
    · simp only [invP]
      rw [ii _ u1, ii _ u2, ii _ u3, ii _ u4]
    · simp only [hG, invP, B.sgs]
      have j1 : (Matrix.of (B2.invM p.1.1))⁻¹ = Matrix.of p.1.1 := ii _ u1
      have j2 : (Matrix.of (B2.invM p.1.2))⁻¹ = Matrix.of p.1.2 := ii _ u2
      rw [j1, j2]
      rfl
  calc ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
        ∂D.μSS = ∫⁻ p, G (invP p) ∂D.μSS := lintegral_congr_ae (hinv.mono fun p hp => hp.2.symm)
    _ = ∫⁻ p, G (invP p) ∂(D.μSS.map invP) := by rw [map_invP D]
    _ ≤ ∫⁻ p, G (invP (invP p)) ∂D.μSS := by
      have hm := B2x1.invM_meas (k := k) (r := r)
      have hinvP : Measurable (invP (k := k) (r := r)) :=
        (hm.prodMap hm).prodMap (hm.prodMap hm)
      exact lintegral_map_le (fun p => G (invP p)) hinvP.aemeasurable
    _ = ∫⁻ p, G p ∂D.μSS := lintegral_congr_ae (hinv.mono fun p hp => by show G (invP (invP p)) = G p; rw [hp.1])
    _ < ⊤ := h1

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem l_enorm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {l : H → Wp} (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be z c π σ μW μN x y = (innerSL ℂ (l y)).smulRight (l x))
    {v : H} (hv : v ∈ DDsp σ w0) (hlv : l v ≠ 0) {x : H} (hx : x ∈ DDsp σ w0)
    {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖l (σ g x)‖ₑ ≤ (‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) *
      ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
  rw [l_of_be (hbe _ (dd_stable hds hg x hx) v hv) hlv]
  have hbe' := be_enorm_le (c := c) hds hT hπ hW hN (x := x) (v := v) hg
  calc ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ • (be z c π σ μW μN (σ g x) v) (l v)‖ₑ
      = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖(be z c π σ μW μN (σ g x) v) (l v)‖ₑ := enorm_smul _ _
    _ ≤ ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * (‖be z c π σ μW μN (σ g x) v‖ₑ * ‖l v‖ₑ) := by
        gcongr
        exact ContinuousLinearMap.le_opENorm _ _
    _ ≤ ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ((∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) *
          ‖l v‖ₑ) := by gcongr
    _ = _ := by ring

theorem lint_left {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : B.IsHaarOn (B.GV k r) μG)
    {a : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (Formalism.QuantumDeterminants.lmulM a x) ∂μG = ∫⁻ x, F x ∂μG := by
  have hm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul (show Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) from continuous_id)
    exact this.measurable
  rw [← lintegral_map hF hm, hG.left a ha]

theorem gN_mul_rpow (hNI : NormInv) {x Y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ} (hb : 0 ≤ b) :
    B.gN (Y * x) ^ (-b) ≤ B.gN x ^ b * B.gN Y ^ (-b) := by
  obtain ⟨hsub, hinv⟩ := hNI k r
  have hxi := MatrixMultiplicationContinuity.uh_inv hx
  have hYx : Y * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hY hx
  have h1 : 1 ≤ B.gN x := (hinv x hx).2
  have h2 : 1 ≤ B.gN Y := (hinv Y hY).2
  have h3 : 1 ≤ B.gN (Y * x) := (hinv _ hYx).2
  have hle : B.gN Y ≤ B.gN (Y * x) * B.gN x := by
    have e : Y = Y * x * x⁻¹ := by rw [Matrix.mul_assoc, hxi.2.1, Matrix.mul_one]
    calc B.gN Y = B.gN (Y * x * x⁻¹) := by rw [← e]
      _ ≤ B.gN (Y * x) * B.gN x⁻¹ := hsub _ _
      _ = B.gN (Y * x) * B.gN x := by rw [(hinv x hx).1]
  have hpos : 0 < B.gN x := lt_of_lt_of_le one_pos h1
  have hq : B.gN Y / B.gN x ≤ B.gN (Y * x) := (div_le_iff₀ hpos).mpr hle
  have hqpos : 0 < B.gN Y / B.gN x := div_pos (lt_of_lt_of_le one_pos h2) hpos
  calc B.gN (Y * x) ^ (-b) ≤ (B.gN Y / B.gN x) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hqpos hq (by linarith)
    _ = B.gN x ^ b * B.gN Y ^ (-b) := by
        rw [Real.div_rpow (lt_of_lt_of_le one_pos h2).le hpos.le, Real.rpow_neg hpos.le,
          div_eq_mul_inv, inv_inv, mul_comm]

theorem meas_matmul {α : Type*} [MeasurableSpace α] {f g : α → Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => (fun i j => (Matrix.of (f p) * Matrix.of (g p)) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  exact ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hf)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply l).comp hg))

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem cmHalfIntegralGenerator_mem_algebraicClosure {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) : w0 ∈ DDsp σ w0 := by
  have hone : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  refine Submodule.subset_span ⟨1, hone, ?_⟩
  show σ 1 w0 = w0
  rw [(MatrixMultiplicationContinuity.sigma_facts hds).1]; rfl

theorem enorm_smulRight {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (a : E) (b : F) :
    ‖(innerSL ℂ a).smulRight b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, ENNReal.ofReal_mul (norm_nonneg _)]

theorem mt_cont : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := by
  first
    | exact continuous_id
    | fun_prop
    | continuity

theorem inner_bound (hNI : NormInv) {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : B.IsHaarOn (B.GV k r) μG)
    (hGc : ∀ᵐ x ∂μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) {C1 C2 a b : ℝ}
    (hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-a))
    (hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a)
    {P Q γi : Mx k r} (hP : P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hQ : Q ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hγ : γi ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ x, ‖e1 (P * Matrix.of x)‖ₑ * ‖e2 (Q * (γi * Matrix.of x))‖ₑ ∂μG ≤
      ENNReal.ofReal (|C1| * |C2|) * ‖B.gN (Q * γi * P⁻¹) ^ (-b)‖ₑ *
        ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG := by
  obtain ⟨hPi, hPP, -⟩ := MatrixMultiplicationContinuity.uh_inv hP
  set Y : Mx k r := Q * γi * P⁻¹ with hY
  have hYU : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hQ hγ) hPi
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ‖e1 (P * Matrix.of x)‖ₑ * ‖e2 (Q * (γi * Matrix.of x))‖ₑ with hF
  have hFm : Measurable F := by
    have c1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => e1 (P * Matrix.of x)) :=
      he1.comp (continuous_const.matrix_mul mt_cont)
    have c2 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => e2 (Q * (γi * Matrix.of x))) :=
      he2.comp (continuous_const.matrix_mul (continuous_const.matrix_mul mt_cont))
    exact c1.measurable.enorm.mul c2.measurable.enorm
  have hNI' := hNI k r
  calc ∫⁻ x, F x ∂μG = ∫⁻ x, F (Formalism.QuantumDeterminants.lmulM P⁻¹ x) ∂μG := (lint_left hG hPi hFm).symm
    _ ≤ ∫⁻ x, (ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ) * ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG := by
        apply lintegral_mono_ae
        filter_upwards [hGc] with x hx
        have e1x : P * Matrix.of (Formalism.QuantumDeterminants.lmulM P⁻¹ x) = Matrix.of x := by
          show P * (P⁻¹ * Matrix.of x) = Matrix.of x
          rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
        have e2x : Q * (γi * Matrix.of (Formalism.QuantumDeterminants.lmulM P⁻¹ x)) = Y * Matrix.of x := by
          show Q * (γi * (P⁻¹ * Matrix.of x)) = Q * γi * P⁻¹ * Matrix.of x
          simp only [Matrix.mul_assoc]
        simp only [hF]
        rw [e1x, e2x]
        have hYx : Y * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hYU hx
        have ht1 : 1 ≤ B.gN (Matrix.of x) := (hNI'.2 _ hx).2
        have htp : 0 < B.gN (Matrix.of x) := lt_of_lt_of_le one_pos ht1
        have hs1 : 1 ≤ B.gN (Y * Matrix.of x) := (hNI'.2 _ hYx).2
        have hYp : 0 ≤ B.gN Y ^ (-b) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
        have bnd1 : ‖e1 (Matrix.of x)‖ ≤ |C1| * B.gN (Matrix.of x) ^ (-a) :=
          (hb1 _ hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg htp.le _))
        have bnd2 : ‖e2 (Y * Matrix.of x)‖ ≤ |C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)) := by
          refine (hb2 _ hYx).trans ?_
          calc C2 * B.gN (Y * Matrix.of x) ^ (-a) ≤ |C2| * B.gN (Y * Matrix.of x) ^ (-a) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
            _ ≤ |C2| * B.gN (Y * Matrix.of x) ^ (-b) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)) (abs_nonneg _)
            _ ≤ |C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)) :=
                mul_le_mul_of_nonneg_left (gN_mul_rpow hNI hx hYU hb0) (abs_nonneg _)
        have key : |C1| * B.gN (Matrix.of x) ^ (-a) * (|C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b))) =
            (|C1| * |C2|) * B.gN Y ^ (-b) * B.gN (Matrix.of x) ^ (-(a - b)) := by
          have : B.gN (Matrix.of x) ^ (-a) * B.gN (Matrix.of x) ^ b = B.gN (Matrix.of x) ^ (-(a - b)) := by
            rw [← Real.rpow_add htp]; ring_nf
          calc |C1| * B.gN (Matrix.of x) ^ (-a) * (|C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)))
              = (|C1| * |C2|) * B.gN Y ^ (-b) * (B.gN (Matrix.of x) ^ (-a) * B.gN (Matrix.of x) ^ b) := by ring
            _ = _ := by rw [this]
        have hxp : 0 ≤ B.gN (Matrix.of x) ^ (-(a - b)) := Real.rpow_nonneg htp.le _
        have hC : 0 ≤ |C1| * |C2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have L : ‖e1 (Matrix.of x)‖ₑ * ‖e2 (Y * Matrix.of x)‖ₑ =
            ENNReal.ofReal (‖e1 (Matrix.of x)‖ * ‖e2 (Y * Matrix.of x)‖) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
        have R : ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ * ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ =
            ENNReal.ofReal ((|C1| * |C2|) * B.gN Y ^ (-b) * B.gN (Matrix.of x) ^ (-(a - b))) := by
          rw [Real.enorm_eq_ofReal hYp, Real.enorm_eq_ofReal hxp, ENNReal.ofReal_mul (mul_nonneg hC hYp),
            ENNReal.ofReal_mul hC]
        rw [L, R]
        apply ENNReal.ofReal_le_ofReal
        rw [← key]
        exact mul_le_mul bnd1 bnd2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htp.le _))
    _ = ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ * ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG :=
        lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem meas_G (γ : Mx k r) (b : ℝ) :
    Measurable (fun pp : B.SS k r =>
      ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^ (-b)‖ₑ) := by
  have hi := B2x1.invM_meas (k := k) (r := r)
  have m1 : Measurable (fun pp : B.SS k r => pp.1.1) := measurable_fst.fst
  have m2 : Measurable (fun pp : B.SS k r => pp.1.2) := measurable_fst.snd
  have m3 : Measurable (fun pp : B.SS k r => B2.invM pp.2.2) := hi.comp measurable_snd.snd
  have m4 : Measurable (fun pp : B.SS k r => B2.invM pp.2.1) := hi.comp measurable_snd.fst
  have mγ : Measurable (fun _ : B.SS k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul m1 m2) mγ) m3) m4
  have hg : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y)) := gN_cont.comp mt_cont
  exact ((hg.measurable.comp M).pow_const (-b)).enorm

def Phi3 (e1 e2 : Mx k r → ℂ) (γi : Mx k r) (x : Formalism.QuantumDeterminants.Mt k r) (p q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ * ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ

theorem triple_integrand_measurable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    {X : α → Formalism.QuantumDeterminants.Mt k r} {Pp Qq : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Continuous X) (hP : Continuous Pp) (hQ : Continuous Qq) :
    Measurable (fun t => Phi3 e1 e2 γi (X t) (Pp t) (Qq t)) := by
  unfold Phi3
  exact ((he1.comp (((mt_cont.comp hP.fst).matrix_mul (mt_cont.comp hP.snd)).matrix_mul
    (mt_cont.comp hX))).enorm.measurable).mul
    ((he2.comp (((mt_cont.comp hQ.fst).matrix_mul (mt_cont.comp hQ.snd)).matrix_mul
    (continuous_const.matrix_mul (mt_cont.comp hX)))).enorm.measurable)

theorem triple_lintegral_product {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x : Formalism.QuantumDeterminants.Mt k r) :
    (∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂μp) *
      (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ ∂μq) =
      ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp := by
  simp only [Phi3]
  have ha : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ :=
    (he1.comp (((mt_cont.comp continuous_fst).matrix_mul (mt_cont.comp continuous_snd)).matrix_mul
      continuous_const)).enorm.measurable
  rw [← lintegral_mul_const _ ha]
  refine lintegral_congr fun p => ?_
  rw [lintegral_const_mul' _ _ enorm_ne_top]

theorem triple_lintegral_swap {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    [SFinite μG] [SFinite μp] [SFinite μq] :
    ∫⁻ x, ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp ∂μG =
      ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γi x p q ∂μG ∂μq ∂μp := by
  have h1 : Measurable (Function.uncurry fun (x : Formalism.QuantumDeterminants.Mt k r)
      (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq) := by
    have hm := triple_integrand_measurable he1 he2 γi
      (α := (Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
      (X := fun z => z.1.1) (Pp := fun z => z.1.2) (Qq := fun z => z.2)
      (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst) continuous_snd
    exact hm.lintegral_prod_right'
  rw [lintegral_lintegral_swap h1.aemeasurable]
  refine lintegral_congr fun p => ?_
  have h2 : Measurable (Function.uncurry fun (x : Formalism.QuantumDeterminants.Mt k r)
      (q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => Phi3 e1 e2 γi x p q) :=
    triple_integrand_measurable he1 he2 γi (X := fun z : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => z.1)
      (Pp := fun _ => p) (Qq := fun z => z.2) continuous_fst continuous_const continuous_snd
  exact lintegral_lintegral_swap h2.aemeasurable

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_Y_eq (hNI : NormInv) {P Q γ : Mx k r} (hP : P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hQ : Q ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    B.gN (Q * γ⁻¹ * P⁻¹) = B.gN (P * γ * Q⁻¹) := by
  set H := Formalism.QuantumDeterminants.Hpk k r with hHdef
  have hU : ∀ g ∈ Formalism.QuantumDeterminants.UH H, IsUnit g.det := by
    intro g hg
    have h1 : gᴴ * H * g = H := hg
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH : IsUnit H.det := Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r
    have h3 : (gᴴ).det * g.det = 1 := by
      apply hH.mul_left_cancel
      calc H.det * ((gᴴ).det * g.det) = (gᴴ).det * H.det * g.det := by ring
        _ = H.det := h2
        _ = H.det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((gᴴ).det) (by rw [mul_comm]; exact h3)
  have hmem_mul : ∀ a ∈ Formalism.QuantumDeterminants.UH H, ∀ b ∈ Formalism.QuantumDeterminants.UH H, a * b ∈ Formalism.QuantumDeterminants.UH H := by
    intro a ha b hb
    have ha' : aᴴ * H * a = H := ha
    have hb' : bᴴ * H * b = H := hb
    show (a * b)ᴴ * H * (a * b) = H
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
      _ = H := by rw [ha', hb']
  have hmem_inv : ∀ a ∈ Formalism.QuantumDeterminants.UH H, a⁻¹ ∈ Formalism.QuantumDeterminants.UH H := by
    intro a ha
    have hd := hU a ha
    have ha' : aᴴ * H * a = H := ha
    show (a⁻¹)ᴴ * H * a⁻¹ = H
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha']
      _ = (a * a⁻¹)ᴴ * H * (a * a⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hx : Q * γ⁻¹ * P⁻¹ ∈ Formalism.QuantumDeterminants.UH H :=
    hmem_mul _ (hmem_mul _ hQ _ (hmem_inv _ hγ)) _ (hmem_inv _ hP)
  have hxinv : (Q * γ⁻¹ * P⁻¹)⁻¹ = P * γ * Q⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hU _ hγ),
      Matrix.nonsing_inv_nonsing_inv _ (hU _ hP), mul_assoc]
  rw [← ((hNI k r).2 _ hx).1, hxinv]

set_option maxHeartbeats 1000000 in
theorem ooConv_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGG : GrowthG) (hDD : DecDD)
    (hBC : BeConv) : More.OOConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe' γ hγ
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have hS2' := hS2
  obtain ⟨-, -, -, -, -, -, hT', -, hπ', hW', -, -, hq'⟩ := hS2'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μW' := hW'.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hγU : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hγ.1
  obtain ⟨hγi, hγγ, hγγ'⟩ := MatrixMultiplicationContinuity.uh_inv hγU
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hP1 := phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN
    D.μG νq hS1 l hbe w0 hw0DD
  have hP2 := phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN
    D.μG νq' hS2 l' hbe' w0 hw0DD
  have cont2' : ContinuousOn (fun g : Mx k r => l' (σ (γ⁻¹ * g) w0)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    hP2.1.comp (continuous_const.matrix_mul continuous_id).continuousOn (fun g hg => DDSmoothness.uh_mul hγi hg)
  have hop : ContinuousOn (fun g : Mx k r => (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))).smulRight (l (σ g w0)))
      (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    have ha : ContinuousOn (fun g : Mx k r =>
        ContinuousLinearMap.smulRightL ℂ Wq Wp (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))))
        (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
      (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous.comp_continuousOn
        ((innerSL ℂ).continuous.comp_continuousOn cont2')
    exact (ha.clm_apply hP1.1).congr fun g _ => rfl
  have hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))) D.μG := by
    have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r =>
        (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0)))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
      hop.comp mt_cont.continuousOn (fun x hx => hx)
    have := hc.aestronglyMeasurable (μ := D.μG) uh_mem_measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) hGc] at this
  refine ⟨hmeas, ?_⟩
  show ∫⁻ x, ‖(innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))‖ₑ ∂D.μG < ⊤
  simp only [enorm_smulRight]
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    have e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_]
      · simp
      filter_upwards [hGc] with x hx
      rw [hA _ (dd_stable hds hx w0 hw0DD)]; simp
    rw [e]; exact ENNReal.zero_lt_top
  by_cases hA' : ∃ v ∈ DDsp σ w0, l' v ≠ 0
  swap
  · push Not at hA'
    have e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_]
      · simp
      filter_upwards [hGc] with x hx
      rw [hA' _ (dd_stable hds (DDSmoothness.uh_mul hγi hx) w0 hw0DD)]; simp
    rw [e]; exact ENNReal.zero_lt_top
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨v', hv', hlv'⟩ := hA'
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨e2, he2, hee2⟩ := coef_ext hds v' w0
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := hDD hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' hS2 w0 hw0DD
    v' hv'
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee2 y hy]; exact hC2 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hb0 : 0 < aOf r h - AG k r - 1 := by linarith
  have hba : aOf r h - AG k r - 1 ≤ aOf r h := by linarith
  have hab : aOf r h - (aOf r h - AG k r - 1) = AG k r + 1 := by ring
  have hThrb : JF.TransportedAlt k r (aOf r h - AG k r - 1) 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
    linarith
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [hab]; linarith)).hasFiniteIntegral
  have hLa := la_fin hNI D hThrb hb0.ne' hγ
  have hpt : ∀ᵐ x ∂D.μG, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤
      ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
        ((∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN)) *
          (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN))) := by
    filter_upwards [hGc] with x hx
    have hgx : γ⁻¹ * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hγi hx
    have b1 := l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hx
    have b2 := l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT' hπ' hW' hN hbe' hv' hlv' hw0DD hgx
    have i1 : ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) w0⟫_ℂ‖ₑ ∂(D.μW.prod D.μN) =
        ∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN) := by
      apply lintegral_congr_ae
      filter_upwards [prod_ae hW hN] with p hp
      rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hx)]
    have i2 : ∫⁻ q, ‖⟪v', σ (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x)) w0⟫_ℂ‖ₑ
        ∂(D.μW'.prod D.μN) =
        ∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN) := by
      apply lintegral_congr_ae
      filter_upwards [prod_ae hW' hN] with q hq
      rw [hee2 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hq.1.1 hq.2.1) hgx)]
    rw [i1] at b1; rw [i2] at b2
    calc ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤ _ * _ := mul_le_mul' b2 b1
      _ = _ := by ring
  have hinner : ∀ᵐ p ∂(D.μW.prod D.μN), ∀ᵐ q ∂(D.μW'.prod D.μN),
      ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ≤
        (ENNReal.ofReal (|C1| * |C2|) *
          ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
        ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹) ^
          (-(aOf r h - AG k r - 1))‖ₑ := by
    filter_upwards [prod_ae hW hN] with p hp
    filter_upwards [prod_ae hW' hN] with q hq
    have hPU : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hQU : Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hq.1.1 hq.2.1
    have hIB := inner_bound hNI D.haarG hGc he1 he2 hb1 hb2 hb0.le hba hPU hQU hγi
    have hY := gN_Y_eq hNI hPU hQU hγU
    have e : Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ =
        Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹ := by
      rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    unfold Phi3
    rw [hY, e] at hIB
    calc _ ≤ _ := hIB
      _ = _ := by ring
  have hmG := meas_G (k := k) (r := r) γ (aOf r h - AG k r - 1)
  calc ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG
      ≤ ∫⁻ x, ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γ⁻¹ x p q ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) ∂D.μG := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        rw [← triple_lintegral_product he1 he2 γ⁻¹]; exact hx
    _ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by
        rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]), triple_lintegral_swap he1 he2 γ⁻¹]
    _ ≤ ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, (ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
            ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹) ^
              (-(aOf r h - AG k r - 1))‖ₑ ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by
        gcongr 1
        exact lintegral_mono_ae (hinner.mono fun p hp => lintegral_mono_ae hp)
    _ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ((ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
          ∫⁻ pp, ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^
              (-(aOf r h - AG k r - 1))‖ₑ ∂D.μSS) := by
        congr 1
        have hc0 : ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKg.ne
        simp_rw [lintegral_const_mul' _ _ hc0]
        rw [show D.μSS = (D.μW.prod D.μN).prod (D.μW'.prod D.μN) from rfl, lintegral_prod _ hmG.aemeasurable]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) (ENNReal.mul_lt_top ?_ hLa)
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKg

end Formalism.FourierDecayAlt.P.S3dx4
